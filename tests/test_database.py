import builtins
from datetime import datetime
import json
import sys

import pytest

from conjectures_arxiv.conjecture_extractor import ExtractedConjecture
from conjectures_arxiv.database import Database
from conjectures_arxiv.models import Paper


def _sample_paper() -> Paper:
    return Paper(
        arxiv_id="2603.00001v1",
        title="Test",
        summary="Summary",
        authors=["Alice", "Bob"],
        categories=["math.AG"],
        published_at=datetime(2026, 3, 1, 10, 0, 0),
        updated_at=datetime(2026, 3, 1, 10, 0, 0),
        abs_url="https://arxiv.org/abs/2603.00001v1",
        pdf_url="https://arxiv.org/pdf/2603.00001v1.pdf",
        source_url="https://arxiv.org/e-print/2603.00001v1",
    )


def _sample_conjecture() -> ExtractedConjecture:
    return ExtractedConjecture(
        source_file="main.tex",
        index_in_file=1,
        start_line=3,
        end_line=5,
        raw_tex="\\begin{conjecture}X\\end{conjecture}",
        body_tex="X",
        plain_text="X",
        content_hash="abc123",
    )


def test_database_insert_dedup_and_export(tmp_path) -> None:
    db_path = tmp_path / "conjectures.sqlite"
    output_dir = tmp_path / "exports"

    db = Database(db_path)
    db.init_schema()

    paper = _sample_paper()
    db.upsert_paper(paper)

    c = _sample_conjecture()
    first_insert = db.insert_conjectures(paper.arxiv_id, [c])
    second_insert = db.insert_conjectures(paper.arxiv_id, [c])

    assert first_insert == 1
    assert second_insert == 0

    exported = db.export(output_dir)
    db.close()

    assert exported["conjectures_jsonl"].exists()
    assert exported["conjectures_csv"].exists()
    assert exported["papers_jsonl"].exists()

    lines = exported["conjectures_jsonl"].read_text(encoding="utf-8").strip().splitlines()
    assert len(lines) == 1
    record = json.loads(lines[0])
    assert record["arxiv_id"] == "2603.00001v1"
    assert record["plain_text"] == "X"


def test_with_partitions_adds_year_month_fields() -> None:
    records = [
        {"published_at": "2026-03-01T10:00:00Z"},
        {"published_at": "invalid"},
    ]
    partitioned = Database._with_partitions(records, datetime_field="published_at")

    assert partitioned[0]["published_year"] == 2026
    assert partitioned[0]["published_month"] == 3
    assert partitioned[1]["published_year"] == 0
    assert partitioned[1]["published_month"] == 0


def test_export_parquet_requires_pyarrow(tmp_path, monkeypatch) -> None:
    db = Database(tmp_path / "conjectures.sqlite")
    db.init_schema()
    paper = _sample_paper()
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture()])

    original_import = builtins.__import__

    def fake_import(name, *args, **kwargs):
        if name == "pyarrow" or name.startswith("pyarrow."):
            raise ModuleNotFoundError("No module named 'pyarrow'")
        return original_import(name, *args, **kwargs)

    sys.modules.pop("pyarrow", None)
    sys.modules.pop("pyarrow.dataset", None)
    monkeypatch.setattr(builtins, "__import__", fake_import)

    with pytest.raises(RuntimeError, match="pyarrow"):
        db.export_parquet(tmp_path / "exports")

    db.close()


def test_llm_label_roundtrip_and_exports(tmp_path) -> None:
    db = Database(tmp_path / "conjectures.sqlite")
    db.init_schema()
    paper = _sample_paper()
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture()])

    unlabeled = db.list_conjectures_for_llm(model="gpt-5-mini", only_unlabeled=True)
    assert len(unlabeled) == 1
    conjecture_id = int(unlabeled[0]["conjecture_id"])

    db.upsert_llm_label(
        conjecture_id=conjecture_id,
        model="gpt-5-mini",
        label="real_open_conjecture",
        confidence=0.92,
        rationale="Actively posed as open.",
        evidence_snippet="We conjecture...",
        raw_response_json='{"label":"real_open_conjecture"}',
    )

    still_unlabeled = db.list_conjectures_for_llm(model="gpt-5-mini", only_unlabeled=True)
    assert still_unlabeled == []

    counts = db.llm_label_counts(model="gpt-5-mini")
    assert counts["real_open_conjecture"] == 1

    exported = db.export_llm_real_conjectures(
        model="gpt-5-mini",
        output_dir=tmp_path / "exports",
        min_confidence=0.8,
    )
    assert exported["real_conjectures_jsonl"].exists()
    assert exported["real_conjectures_csv"].exists()
    db.close()
