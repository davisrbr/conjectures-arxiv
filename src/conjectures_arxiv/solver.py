from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
import json
import time
from typing import Any

from .database import TIMESTAMP_FMT


DEFAULT_REASONING_EFFORT = "xhigh"
DEFAULT_MAX_OUTPUT_TOKENS = 128000
SOLVER_PROMPT_VERSION = "gpt54-autonomous-web-v1"
TERMINAL_RESPONSE_STATUSES = {"completed", "failed", "cancelled", "incomplete"}


@dataclass(frozen=True)
class SolverPrompt:
    instructions: str
    prompt_text: str


@dataclass(frozen=True)
class SolverAttemptSnapshot:
    response_id: str
    status: str
    output_text: str
    sources_json: str
    raw_response_json: str
    error_json: str
    completed_at: str | None


class OpenAIConjectureSolver:
    def __init__(self, *, model: str = "gpt-5.4", client=None) -> None:
        self.model = model
        if client is not None:
            self.client = client
            return

        try:
            from openai import OpenAI  # type: ignore
        except ModuleNotFoundError as exc:
            raise RuntimeError("LLM solving requires the openai package. Install with: pip install openai") from exc

        try:
            self.client = OpenAI()
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError("LLM solving requires OPENAI_API_KEY to be set in the environment.") from exc

    def build_prompt(self, *, record: dict[str, Any], context_window: str = "") -> SolverPrompt:
        return SolverPrompt(
            instructions=self._instructions(),
            prompt_text=self._user_prompt(record=record, context_window=context_window),
        )

    def submit(
        self,
        *,
        prompt: SolverPrompt,
        record: dict[str, Any],
        reasoning_effort: str = DEFAULT_REASONING_EFFORT,
        search_context_size: str = "high",
        max_output_tokens: int = DEFAULT_MAX_OUTPUT_TOKENS,
        max_tool_calls: int = 32,
    ) -> SolverAttemptSnapshot:
        metadata = {
            "conjecture_id": str(record.get("conjecture_id", "")),
            "arxiv_id": str(record.get("arxiv_id", "")),
            "prompt_version": SOLVER_PROMPT_VERSION,
        }
        response = self.client.responses.create(
            model=self.model,
            instructions=prompt.instructions,
            input=[
                {
                    "role": "user",
                    "content": [{"type": "input_text", "text": prompt.prompt_text}],
                }
            ],
            background=True,
            store=True,
            include=["web_search_call.action.sources"],
            max_output_tokens=max_output_tokens,
            max_tool_calls=max_tool_calls,
            metadata=metadata,
            parallel_tool_calls=True,
            reasoning={"effort": reasoning_effort},
            tool_choice="auto",
            tools=[{"type": "web_search", "search_context_size": search_context_size}],
            truncation="auto",
        )
        return self._snapshot_from_response(response)

    def retrieve(self, *, response_id: str) -> SolverAttemptSnapshot:
        response = self.client.responses.retrieve(
            response_id,
            include=["web_search_call.action.sources"],
        )
        return self._snapshot_from_response(response)

    def wait(
        self,
        *,
        response_id: str,
        poll_interval_seconds: float = 10.0,
    ) -> SolverAttemptSnapshot:
        while True:
            snapshot = self.retrieve(response_id=response_id)
            if snapshot.status in TERMINAL_RESPONSE_STATUSES:
                return snapshot
            time.sleep(poll_interval_seconds)

    @staticmethod
    def _instructions() -> str:
        return (
            "You are evaluating a mathematical conjecture from a recent arXiv paper. "
            "Work autonomously and use web search whenever it helps. Consult the paper and relevant literature "
            "before making claims about priority, novelty, or whether the exact statement is already known.\n\n"
            "Your job is to determine whether you can prove the conjecture, refute it by explicit counterexample, "
            "identify that the exact result is already essentially in the literature, or conclude that you cannot "
            "settle it from the available information.\n\n"
            "Requirements:\n"
            "- Distinguish carefully between the exact conjecture and nearby results.\n"
            "- Do not claim success unless you can give a mathematically coherent proof sketch or an explicit "
            "counterexample with verification.\n"
            "- If notation or hypotheses are missing, say so clearly and explain how that affects your conclusion.\n"
            "- If you find the exact result or a close variant in the literature, cite sources and say whether it is "
            "(a) nearly exact in the literature, (b) close to existing literature, or (c) relatively novel.\n"
            "- Cite sources for literature claims.\n\n"
            "Return plain text with these section headers exactly:\n"
            "Verdict\n"
            "Well-specifiedness\n"
            "Reasoning\n"
            "Literature overlap\n"
            "Sources"
        )

    @staticmethod
    def _user_prompt(*, record: dict[str, Any], context_window: str) -> str:
        authors = ", ".join(str(author) for author in record.get("authors", [])) or "(unknown)"
        context_block = context_window.strip() or "(not provided)"
        return (
            "Please confirm or disconfirm this conjecture. If successful, discuss whether your proposed solution "
            "can already be found (a) nearly exactly in the literature, (b) whether a close version of it exists in "
            "the literature, or (c) if it is relatively novel. Finally, whether successful or not, comment on how "
            "well-specified the conjecture is.\n\n"
            "The solution might not be present in the literature, in which case you should attempt one.\n\n"
            f"CONJECTURE_ID: {record.get('conjecture_id', '')}\n"
            f"ARXIV_ID: {record.get('arxiv_id', '')}\n"
            f"TITLE: {record.get('title', '')}\n"
            f"AUTHORS: {authors}\n"
            f"ABSTRACT_URL: {record.get('abs_url', '')}\n"
            f"PDF_URL: {record.get('pdf_url', '')}\n"
            f"SOURCE_URL: {record.get('source_url', '')}\n"
            f"SOURCE_LOCATION: {record.get('source_file', '')}:{record.get('start_line', '')}-{record.get('end_line', '')}\n\n"
            f"PAPER_ABSTRACT:\n{record.get('summary', '')}\n\n"
            f"CONJECTURE_LATEX:\n{record.get('body_tex', '') or record.get('raw_tex', '')}\n\n"
            f"CONJECTURE_PLAIN_TEXT:\n{record.get('plain_text', '')}\n\n"
            f"LOCAL_SOURCE_CONTEXT:\n{context_block}\n"
        )

    @classmethod
    def _snapshot_from_response(cls, response: Any) -> SolverAttemptSnapshot:
        payload = cls._to_json_dict(response)
        return SolverAttemptSnapshot(
            response_id=str(payload.get("id", getattr(response, "id", ""))),
            status=str(payload.get("status", getattr(response, "status", "")) or ""),
            output_text=cls._extract_output_text(response=response, payload=payload),
            sources_json=json.dumps(cls._extract_sources(payload), ensure_ascii=True, sort_keys=True),
            raw_response_json=json.dumps(payload, ensure_ascii=True, sort_keys=True),
            error_json=cls._extract_error_json(payload),
            completed_at=cls._completed_at_str(payload.get("completed_at")),
        )

    @staticmethod
    def _to_json_dict(response: Any) -> dict[str, Any]:
        if hasattr(response, "model_dump"):
            dumped = response.model_dump(mode="json")
            if isinstance(dumped, dict):
                return dumped
        if isinstance(response, dict):
            return response
        return {}

    @classmethod
    def _extract_output_text(cls, *, response: Any, payload: dict[str, Any]) -> str:
        output_text = getattr(response, "output_text", None)
        if isinstance(output_text, str) and output_text.strip():
            return output_text.strip()

        parts: list[str] = []
        for item in payload.get("output", []):
            if not isinstance(item, dict) or item.get("type") != "message":
                continue
            for content in item.get("content", []):
                if not isinstance(content, dict) or content.get("type") != "output_text":
                    continue
                text = str(content.get("text", "")).strip()
                if text:
                    parts.append(text)
        return "\n\n".join(parts).strip()

    @classmethod
    def _extract_sources(cls, payload: dict[str, Any]) -> list[dict[str, Any]]:
        sources: list[dict[str, Any]] = []
        seen: set[tuple[str, str, str]] = set()

        for item in payload.get("output", []):
            if not isinstance(item, dict):
                continue

            if item.get("type") == "web_search_call":
                action = item.get("action", {})
                if isinstance(action, dict):
                    queries = action.get("queries")
                    if not isinstance(queries, list) or not queries:
                        query = action.get("query")
                        queries = [query] if isinstance(query, str) and query else []
                    for source in action.get("sources", []) or []:
                        if not isinstance(source, dict):
                            continue
                        url = str(source.get("url", "")).strip()
                        if not url:
                            continue
                        key = ("web_search_source", url, json.dumps(queries, ensure_ascii=True))
                        if key in seen:
                            continue
                        seen.add(key)
                        sources.append(
                            {
                                "kind": "web_search_source",
                                "web_search_call_id": str(item.get("id", "")),
                                "queries": queries,
                                "url": url,
                            }
                        )

            if item.get("type") != "message":
                continue
            for content in item.get("content", []):
                if not isinstance(content, dict) or content.get("type") != "output_text":
                    continue
                for annotation in content.get("annotations", []) or []:
                    if not isinstance(annotation, dict) or annotation.get("type") != "url_citation":
                        continue
                    url = str(annotation.get("url", "")).strip()
                    title = str(annotation.get("title", "")).strip()
                    if not url:
                        continue
                    key = ("output_citation", url, title)
                    if key in seen:
                        continue
                    seen.add(key)
                    sources.append(
                        {
                            "kind": "output_citation",
                            "title": title,
                            "url": url,
                        }
                    )

        return sources

    @staticmethod
    def _extract_error_json(payload: dict[str, Any]) -> str:
        details: dict[str, Any] = {}
        error = payload.get("error")
        if error not in (None, ""):
            details["error"] = error
        incomplete_details = payload.get("incomplete_details")
        if incomplete_details not in (None, ""):
            details["incomplete_details"] = incomplete_details
        if not details:
            return ""
        return json.dumps(details, ensure_ascii=True, sort_keys=True)

    @staticmethod
    def _completed_at_str(value: Any) -> str | None:
        if value in (None, ""):
            return None
        try:
            timestamp = float(value)
        except (TypeError, ValueError):
            return None
        return datetime.utcfromtimestamp(timestamp).strftime(TIMESTAMP_FMT)
