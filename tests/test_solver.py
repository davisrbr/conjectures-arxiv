from __future__ import annotations

import json

from conjectures_arxiv.cli import _solver_failure_message, _solver_status_reason, build_parser
from conjectures_arxiv.solver import OpenAIConjectureSolver
from conjectures_arxiv.solver import DEFAULT_MAX_OUTPUT_TOKENS, DEFAULT_REASONING_EFFORT


class FakeResponse:
    def __init__(self, payload, *, output_text: str = ""):
        self.payload = payload
        self.output_text = output_text
        self.id = payload.get("id", "")
        self.status = payload.get("status", "")

    def model_dump(self, mode="json"):
        assert mode == "json"
        return self.payload


class FakeResponsesAPI:
    def __init__(self, *, create_response: FakeResponse, retrieve_response: FakeResponse):
        self.create_response = create_response
        self.retrieve_response = retrieve_response
        self.create_kwargs = None
        self.retrieve_kwargs = None
        self.retrieve_response_id = None

    def create(self, **kwargs):
        self.create_kwargs = kwargs
        return self.create_response

    def retrieve(self, response_id, **kwargs):
        self.retrieve_response_id = response_id
        self.retrieve_kwargs = kwargs
        return self.retrieve_response


class FakeClient:
    def __init__(self, *, create_response: FakeResponse, retrieve_response: FakeResponse):
        self.responses = FakeResponsesAPI(
            create_response=create_response,
            retrieve_response=retrieve_response,
        )


def _sample_record() -> dict:
    return {
        "conjecture_id": 152,
        "arxiv_id": "2602.21846v1",
        "title": "Scalable Kernel-Based Distances for Statistical Inference and Integration",
        "summary": "A paper about kernel quantile discrepancies.",
        "authors": ["Alice", "Bob"],
        "abs_url": "https://arxiv.org/abs/2602.21846v1",
        "pdf_url": "https://arxiv.org/pdf/2602.21846v1",
        "source_url": "https://arxiv.org/e-print/2602.21846v1",
        "source_file": "main.tex",
        "start_line": 6088,
        "end_line": 6095,
        "raw_tex": "\\begin{conjecture}X\\end{conjecture}",
        "body_tex": "X",
        "plain_text": "X",
    }


def test_solver_build_prompt_includes_context_and_urls() -> None:
    solver = OpenAIConjectureSolver(model="gpt-5.4", client=FakeClient(create_response=FakeResponse({}), retrieve_response=FakeResponse({})))
    prompt = solver.build_prompt(record=_sample_record(), context_window="6088: Conjecture")

    assert "Please confirm or disconfirm this conjecture." in prompt.prompt_text
    assert "ARXIV_ID: 2602.21846v1" in prompt.prompt_text
    assert "PDF_URL: https://arxiv.org/pdf/2602.21846v1" in prompt.prompt_text
    assert "LOCAL_SOURCE_CONTEXT:\n6088: Conjecture" in prompt.prompt_text
    assert "Return plain text with these section headers exactly" in prompt.instructions


def test_solver_submit_and_retrieve_capture_sources_and_config() -> None:
    create_payload = {
        "id": "resp_create",
        "status": "queued",
        "output": [
            {
                "id": "ws_1",
                "type": "web_search_call",
                "status": "completed",
                "action": {
                    "type": "search",
                    "queries": ["kernel quantile discrepancy conjecture"],
                    "sources": [{"type": "url", "url": "https://arxiv.org/abs/2602.21846v1"}],
                },
            },
            {
                "id": "msg_1",
                "type": "message",
                "role": "assistant",
                "status": "completed",
                "content": [
                    {
                        "type": "output_text",
                        "text": "Initial assessment.",
                        "annotations": [
                            {
                                "type": "url_citation",
                                "title": "arXiv paper",
                                "url": "https://arxiv.org/abs/2602.21846v1",
                                "start_index": 0,
                                "end_index": 10,
                            }
                        ],
                    }
                ],
            },
        ],
    }
    retrieve_payload = {
        "id": "resp_create",
        "status": "completed",
        "completed_at": 1772971200,
        "output": [
            {
                "id": "msg_2",
                "type": "message",
                "role": "assistant",
                "status": "completed",
                "content": [
                    {
                        "type": "output_text",
                        "text": "Verdict\nunresolved\n\nSources\n- https://arxiv.org/abs/2602.21846v1",
                        "annotations": [],
                    }
                ],
            }
        ],
    }
    client = FakeClient(
        create_response=FakeResponse(create_payload, output_text="Initial assessment."),
        retrieve_response=FakeResponse(retrieve_payload),
    )
    solver = OpenAIConjectureSolver(model="gpt-5.4", client=client)
    prompt = solver.build_prompt(record=_sample_record(), context_window="ctx")

    submitted = solver.submit(
        prompt=prompt,
        record=_sample_record(),
        reasoning_effort="xhigh",
        search_context_size="high",
        max_output_tokens=16000,
        max_tool_calls=32,
    )
    assert submitted.response_id == "resp_create"
    assert submitted.status == "queued"
    assert submitted.output_text == "Initial assessment."
    submitted_sources = json.loads(submitted.sources_json)
    assert any(source["kind"] == "web_search_source" for source in submitted_sources)
    assert any(source["kind"] == "output_citation" for source in submitted_sources)

    create_kwargs = client.responses.create_kwargs
    assert create_kwargs is not None
    assert create_kwargs["model"] == "gpt-5.4"
    assert create_kwargs["background"] is True
    assert create_kwargs["store"] is True
    assert create_kwargs["include"] == ["web_search_call.action.sources"]
    assert create_kwargs["reasoning"] == {"effort": "xhigh"}
    assert create_kwargs["tools"] == [{"type": "web_search", "search_context_size": "high"}]
    assert create_kwargs["max_output_tokens"] == 16000
    assert create_kwargs["max_tool_calls"] == 32

    retrieved = solver.retrieve(response_id="resp_create")
    assert client.responses.retrieve_response_id == "resp_create"
    assert client.responses.retrieve_kwargs == {"include": ["web_search_call.action.sources"]}
    assert retrieved.status == "completed"
    assert retrieved.completed_at == "2026-03-08T12:00:00Z"
    assert "Verdict" in retrieved.output_text


def test_solver_retrieve_incomplete_captures_reason() -> None:
    payload = {
        "id": "resp_incomplete",
        "status": "incomplete",
        "incomplete_details": {"reason": "max_output_tokens"},
        "output": [],
    }
    client = FakeClient(
        create_response=FakeResponse({}),
        retrieve_response=FakeResponse(payload),
    )
    solver = OpenAIConjectureSolver(model="gpt-5.4", client=client)

    snapshot = solver.retrieve(response_id="resp_incomplete")

    assert snapshot.status == "incomplete"
    assert json.loads(snapshot.error_json) == {"incomplete_details": {"reason": "max_output_tokens"}}


def test_solver_cli_defaults_and_incomplete_message() -> None:
    parser = build_parser()
    args = parser.parse_args(["solve-llm"])
    status_args = parser.parse_args(["solve-status"])

    assert args.reasoning_effort == DEFAULT_REASONING_EFFORT
    assert args.max_output_tokens == DEFAULT_MAX_OUTPUT_TOKENS
    assert status_args.limit == 20
    assert status_args.refresh_open is False
    assert (
        _solver_failure_message(
            status="incomplete",
            error_json='{"incomplete_details":{"reason":"max_output_tokens"}}',
        )
        == "Solver ended incomplete: reason=max_output_tokens. No visible output was captured."
    )
    assert (
        _solver_status_reason(
            status="incomplete",
            error_json='{"incomplete_details":{"reason":"max_output_tokens"}}',
        )
        == "Solver ended incomplete: reason=max_output_tokens. No visible output was captured"
    )
