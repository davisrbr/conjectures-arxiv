from __future__ import annotations

from datetime import datetime

from conjectures_arxiv.conjecture_extractor import ExtractedConjecture
from conjectures_arxiv.database import Database
from conjectures_arxiv.llm_filter import GPT5MiniConjectureFilter, LLMFilterRunner
from conjectures_arxiv.models import Paper


class FakeResponsesAPI:
    def __init__(self, output_text: str | list[str]):
        if isinstance(output_text, str):
            self.outputs = [output_text]
        else:
            self.outputs = output_text
        self.calls = 0

    def create(self, **kwargs):
        del kwargs

        class Resp:
            pass

        resp = Resp()
        index = min(self.calls, len(self.outputs) - 1)
        resp.output_text = self.outputs[index]
        self.calls += 1
        return resp


class FakeClient:
    def __init__(self, output_text: str | list[str]):
        self.responses = FakeResponsesAPI(output_text)


class StaticContextProvider:
    def get_context(self, record, window_lines=12):
        del record, window_lines
        return " 10: We conjecture this is open."



def _sample_paper() -> Paper:
    return Paper(
        arxiv_id="2603.00002v1",
        title="LLM Test",
        summary="Summary",
        authors=["Alice"],
        categories=["math.CO"],
        published_at=datetime(2026, 3, 1, 0, 0, 0),
        updated_at=datetime(2026, 3, 1, 0, 0, 0),
        abs_url="https://arxiv.org/abs/2603.00002v1",
        pdf_url="https://arxiv.org/pdf/2603.00002v1.pdf",
        source_url="https://arxiv.org/e-print/2603.00002v1",
    )



def _sample_conjecture() -> ExtractedConjecture:
    return ExtractedConjecture(
        source_file="main.tex",
        index_in_file=1,
        start_line=50,
        end_line=52,
        raw_tex="\\begin{conjecture}X\\end{conjecture}",
        body_tex="X",
        plain_text="X",
        content_hash="hash-1",
    )


def _sample_conjecture_two() -> ExtractedConjecture:
    return ExtractedConjecture(
        source_file="main.tex",
        index_in_file=2,
        start_line=60,
        end_line=62,
        raw_tex="\\begin{conjecture}Y\\end{conjecture}",
        body_tex="Y",
        plain_text="Y",
        content_hash="hash-2",
    )



def test_gpt5mini_filter_parses_json_response() -> None:
    client = FakeClient('{"label":"real_open_conjecture","confidence":0.87,"rationale":"open","evidence_snippet":"we conjecture"}')
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)

    result = filterer.classify(
        record={
            "arxiv_id": "2603.00002v1",
            "title": "T",
            "summary": "S",
            "source_file": "main.tex",
            "start_line": 1,
            "end_line": 2,
            "raw_tex": "\\begin{conjecture}X\\end{conjecture}",
            "plain_text": "X",
        },
        context_window="ctx",
    )

    assert result.label == "real_open_conjecture"
    assert result.confidence == 0.87
    assert result.rationale == "open"



def test_llm_filter_runner_writes_labels(tmp_path) -> None:
    db = Database(tmp_path / "c.sqlite")
    db.init_schema()
    paper = _sample_paper()
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture()])

    client = FakeClient('{"label":"not_real_conjecture","confidence":0.95,"rationale":"resolved","evidence_snippet":"follows"}')
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)
    runner = LLMFilterRunner(db=db, classifier=filterer, context_provider=StaticContextProvider())

    summary = runner.run(model="gpt-5-mini", only_unlabeled=True)
    assert summary.total_candidates == 1
    assert summary.processed == 1
    assert summary.failures == 0
    assert summary.label_counts["not_real_conjecture"] == 1

    counts = db.llm_label_counts(model="gpt-5-mini")
    assert counts["not_real_conjecture"] == 1
    db.close()


def test_gpt5mini_filter_batch_parses_results() -> None:
    client = FakeClient(
        '{"results":[{"conjecture_id":11,"label":"real_open_conjecture","confidence":0.9,"rationale":"open","evidence_snippet":"text"},'
        '{"conjecture_id":12,"label":"uncertain","confidence":0.4,"rationale":"unclear","evidence_snippet":"context"}]}'
    )
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)
    results = filterer.classify_batch(
        items=[
            {"conjecture_id": 11, "record": {"arxiv_id": "a", "title": "t", "summary": "s", "source_file": "f", "start_line": 1, "end_line": 1, "raw_tex": "x", "plain_text": "x"}, "context_window": "ctx"},
            {"conjecture_id": 12, "record": {"arxiv_id": "b", "title": "t", "summary": "s", "source_file": "f", "start_line": 1, "end_line": 1, "raw_tex": "y", "plain_text": "y"}, "context_window": "ctx"},
        ]
    )
    assert results[11].label == "real_open_conjecture"
    assert results[12].label == "uncertain"


def test_gpt5mini_filter_recovers_nested_json_in_rationale() -> None:
    client = FakeClient(
        '{"results":[{"conjecture_id":21,"label":"uncertain","confidence":0.0,'
        '"rationale":"{\\"label\\":\\"real_open_conjecture\\",\\"confidence\\":0.93,\\"rationale\\":\\"open\\",'
        '\\"evidence_snippet\\":\\"we conjecture\\"}","evidence_snippet":""}]}'
    )
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)
    results = filterer.classify_batch(
        items=[
            {
                "conjecture_id": 21,
                "record": {
                    "arxiv_id": "a",
                    "title": "t",
                    "summary": "s",
                    "source_file": "f",
                    "start_line": 1,
                    "end_line": 1,
                    "raw_tex": "x",
                    "plain_text": "x",
                },
                "context_window": "ctx",
            }
        ]
    )
    assert results[21].label == "real_open_conjecture"
    assert results[21].confidence == 0.93
    assert results[21].rationale == "open"


def test_gpt5mini_filter_retries_missing_batch_ids() -> None:
    client = FakeClient(
        [
            '{"results":[{"conjecture_id":11,"label":"real_open_conjecture","confidence":0.9,"rationale":"open","evidence_snippet":"text"}]}',
            '{"conjecture_id":12,"label":"not_real_conjecture","confidence":0.91,"rationale":"resolved","evidence_snippet":"proved"}',
        ]
    )
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)
    results = filterer.classify_batch(
        items=[
            {
                "conjecture_id": 11,
                "record": {
                    "arxiv_id": "a",
                    "title": "t",
                    "summary": "s",
                    "source_file": "f",
                    "start_line": 1,
                    "end_line": 1,
                    "raw_tex": "x",
                    "plain_text": "x",
                },
                "context_window": "ctx",
            },
            {
                "conjecture_id": 12,
                "record": {
                    "arxiv_id": "b",
                    "title": "t",
                    "summary": "s",
                    "source_file": "f",
                    "start_line": 1,
                    "end_line": 1,
                    "raw_tex": "y",
                    "plain_text": "y",
                },
                "context_window": "ctx",
            },
        ]
    )
    assert results[11].label == "real_open_conjecture"
    assert results[12].label == "not_real_conjecture"
    assert client.responses.calls == 2


def test_llm_filter_runner_batches(tmp_path) -> None:
    db = Database(tmp_path / "c.sqlite")
    db.init_schema()
    paper = _sample_paper()
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture(), _sample_conjecture_two()])

    client = FakeClient(
        '{"results":[{"conjecture_id":1,"label":"real_open_conjecture","confidence":0.91,"rationale":"open","evidence_snippet":"a"},'
        '{"conjecture_id":2,"label":"not_real_conjecture","confidence":0.88,"rationale":"resolved","evidence_snippet":"b"}]}'
    )
    filterer = GPT5MiniConjectureFilter(model="gpt-5-mini", client=client)
    runner = LLMFilterRunner(db=db, classifier=filterer, context_provider=StaticContextProvider())
    summary = runner.run(model="gpt-5-mini", only_unlabeled=True, batch_size=2)

    assert summary.total_candidates == 2
    assert summary.processed == 2
    assert summary.failures == 0
    assert summary.label_counts["real_open_conjecture"] == 1
    assert summary.label_counts["not_real_conjecture"] == 1
    db.close()
