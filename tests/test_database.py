import builtins
from datetime import datetime
import json
import sys
import sqlite3

import pytest

from conjectures_arxiv.conjecture_extractor import ExtractedConjecture
from conjectures_arxiv.database import Database
from conjectures_arxiv.license_policy import PUBLICATION_POLICY_VERSION
from conjectures_arxiv.models import Paper


def _sample_paper(*, license_url: str = "http://creativecommons.org/licenses/by/4.0/") -> Paper:
    return Paper(
        arxiv_id="2603.00001v1",
        title="Test",
        summary="Summary",
        authors=["Alice", "Bob"],
        categories=["math.AG"],
        primary_category="math.AG",
        doi="10.1000/example-doi",
        journal_ref="J. Example Math. 10 (2026), 1-20",
        comments="15 pages, 3 figures",
        published_at=datetime(2026, 3, 1, 10, 0, 0),
        updated_at=datetime(2026, 3, 1, 10, 0, 0),
        abs_url="https://arxiv.org/abs/2603.00001v1",
        pdf_url="https://arxiv.org/pdf/2603.00001v1.pdf",
        source_url="https://arxiv.org/e-print/2603.00001v1",
        license_url=license_url,
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
    assert record["primary_category"] == "math.AG"
    assert record["doi"] == "10.1000/example-doi"
    assert record["journal_ref"] == "J. Example Math. 10 (2026), 1-20"
    assert record["comments"] == "15 pages, 3 figures"
    assert record["license_url"] == "http://creativecommons.org/licenses/by/4.0/"
    assert record["publication_text_allowed"] is True
    assert record["publication_decision"] == "publish_text"
    assert record["publication_text_reason"] == "creativecommons_license_treated_as_publishable"
    assert record["publication_policy_version"] == PUBLICATION_POLICY_VERSION

    paper_lines = exported["papers_jsonl"].read_text(encoding="utf-8").strip().splitlines()
    assert len(paper_lines) == 1
    paper_record = json.loads(paper_lines[0])
    assert paper_record["primary_category"] == "math.AG"
    assert paper_record["doi"] == "10.1000/example-doi"
    assert paper_record["journal_ref"] == "J. Example Math. 10 (2026), 1-20"
    assert paper_record["comments"] == "15 pages, 3 figures"
    assert paper_record["license_url"] == "http://creativecommons.org/licenses/by/4.0/"
    assert paper_record["publication_text_allowed"] is True
    assert paper_record["publication_decision"] == "publish_text"


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
        interestingness_score=0.84,
        interestingness_confidence=0.75,
        interestingness_rationale="Touches multiple deep tools.",
        viability_score=0.61,
        viability_confidence=0.58,
        viability_rationale="Appears recently framed with concrete structure.",
        assessment_version="test-v1",
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
    row = json.loads(exported["real_conjectures_jsonl"].read_text(encoding="utf-8").strip())
    assert row["interestingness_score"] == 0.84
    assert row["viability_score"] == 0.61
    assert row["assessment_version"] == "test-v1"
    db.close()


def test_init_schema_migrates_llm_label_columns(tmp_path) -> None:
    db_path = tmp_path / "legacy.sqlite"
    conn = sqlite3.connect(db_path)
    conn.execute(
        """
        CREATE TABLE conjecture_llm_labels (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            conjecture_id INTEGER NOT NULL,
            model TEXT NOT NULL,
            label TEXT NOT NULL,
            confidence REAL NOT NULL,
            rationale TEXT NOT NULL,
            evidence_snippet TEXT NOT NULL,
            raw_response_json TEXT NOT NULL,
            created_at TEXT NOT NULL,
            UNIQUE(conjecture_id, model)
        )
        """
    )
    conn.commit()
    conn.close()

    db = Database(db_path)
    db.init_schema()
    columns = {row[1] for row in db.conn.execute("PRAGMA table_info(conjecture_llm_labels)").fetchall()}
    db.close()

    assert "interestingness_score" in columns
    assert "interestingness_confidence" in columns
    assert "interestingness_rationale" in columns
    assert "viability_score" in columns
    assert "viability_confidence" in columns
    assert "viability_rationale" in columns
    assert "assessment_version" in columns


def test_init_schema_migrates_papers_metadata_columns(tmp_path) -> None:
    db_path = tmp_path / "legacy_papers.sqlite"
    conn = sqlite3.connect(db_path)
    conn.execute(
        """
        CREATE TABLE papers (
            arxiv_id TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            summary TEXT NOT NULL,
            authors_json TEXT NOT NULL,
            categories_json TEXT NOT NULL,
            published_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            abs_url TEXT NOT NULL,
            pdf_url TEXT NOT NULL,
            source_url TEXT NOT NULL,
            ingested_at TEXT NOT NULL
        )
        """
    )
    conn.commit()
    conn.close()

    db = Database(db_path)
    db.init_schema()
    columns = {row[1] for row in db.conn.execute("PRAGMA table_info(papers)").fetchall()}
    db.close()

    assert "primary_category" in columns
    assert "doi" in columns
    assert "journal_ref" in columns
    assert "comments" in columns
    assert "license_url" in columns


def test_export_huggingface_dataset_redacts_restricted_text(tmp_path) -> None:
    db = Database(tmp_path / "conjectures.sqlite")
    db.init_schema()
    paper = _sample_paper(license_url="https://arxiv.org/licenses/nonexclusive-distrib/1.0/")
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture()])
    conjecture_id = db.list_conjectures_for_llm(model="gpt-5-mini")[0]["conjecture_id"]
    db.upsert_llm_label(
        conjecture_id=int(conjecture_id),
        model="gpt-5-mini",
        label="real_open_conjecture",
        confidence=0.82,
        interestingness_score=0.65,
        interestingness_confidence=0.62,
        interestingness_rationale="First label.",
        viability_score=0.41,
        viability_confidence=0.4,
        viability_rationale="First viability.",
        assessment_version="test-v1",
        rationale="First rationale.",
        evidence_snippet="First snippet.",
        raw_response_json='{"label":"real_open_conjecture"}',
    )
    db.upsert_llm_label(
        conjecture_id=int(conjecture_id),
        model="gpt-5",
        label="real_open_conjecture",
        confidence=0.91,
        interestingness_score=0.88,
        interestingness_confidence=0.86,
        interestingness_rationale="Latest label.",
        viability_score=0.73,
        viability_confidence=0.71,
        viability_rationale="Latest viability.",
        assessment_version="test-v2",
        rationale="Latest rationale.",
        evidence_snippet="Latest snippet.",
        raw_response_json='{"label":"real_open_conjecture","version":"latest"}',
    )

    exported = db.export_huggingface_dataset(tmp_path / "hf_dataset", repo_id="alice/conjectures-arxiv")
    db.close()

    conjecture_line = exported["hf_conjectures_jsonl"].read_text(encoding="utf-8").strip()
    conjecture_record = json.loads(conjecture_line)
    assert conjecture_record["publication_text_allowed"] is False
    assert conjecture_record["publication_decision"] == "withhold_text"
    assert conjecture_record["publication_text_reason"] == "arxiv_nonexclusive_distribution_license"
    assert conjecture_record["license_family"] == "arxiv_nonexclusive_distrib"
    assert conjecture_record["text_withheld"] is True
    assert conjecture_record["body_tex"] == ""
    assert conjecture_record["plain_text"] == ""
    assert conjecture_record["abs_url"] == "https://arxiv.org/abs/2603.00001v1"
    assert conjecture_record["latest_label_model"] == "gpt-5"
    assert conjecture_record["latest_label"] == "real_open_conjecture"
    assert conjecture_record["latest_label_confidence"] == 0.91
    assert conjecture_record["latest_interestingness_score"] == 0.88
    assert conjecture_record["latest_viability_score"] == 0.73
    assert conjecture_record["latest_assessment_version"] == "test-v2"
    assert conjecture_record["latest_label_rationale"] == "Latest rationale."
    assert conjecture_record["latest_evidence_snippet"] == "Latest snippet."
    assert conjecture_record["latest_labeled_at"]

    paper_line = exported["hf_papers_jsonl"].read_text(encoding="utf-8").strip()
    paper_record = json.loads(paper_line)
    assert paper_record["conjecture_count"] == 1
    assert paper_record["conjectures_with_public_text"] == 0
    assert paper_record["conjectures_withheld_text"] == 1

    manifest = json.loads(exported["hf_manifest_json"].read_text(encoding="utf-8"))
    assert manifest["repo_id"] == "alice/conjectures-arxiv"
    assert manifest["conjectures_total"] == 1
    assert manifest["conjectures_with_public_text"] == 0
    assert manifest["conjectures_withheld_text"] == 1
    assert manifest["conjectures_with_latest_label"] == 1
    assert manifest["publication_policy_version"] == PUBLICATION_POLICY_VERSION

    readme_text = exported["hf_readme"].read_text(encoding="utf-8")
    assert "alice/conjectures-arxiv" in readme_text
    assert "nonexclusive-distrib" in readme_text
    assert "latest LLM label metadata" in readme_text


def test_solver_attempt_roundtrip_and_candidate_listing(tmp_path) -> None:
    db = Database(tmp_path / "conjectures.sqlite")
    db.init_schema()
    paper = _sample_paper()
    db.upsert_paper(paper)
    db.insert_conjectures(paper.arxiv_id, [_sample_conjecture()])

    unlabeled = db.list_conjectures_for_llm(model="gpt-5-mini", only_unlabeled=True)
    conjecture_id = int(unlabeled[0]["conjecture_id"])

    db.upsert_llm_label(
        conjecture_id=conjecture_id,
        model="gpt-5-mini",
        label="real_open_conjecture",
        confidence=0.91,
        interestingness_score=0.45,
        interestingness_confidence=0.62,
        interestingness_rationale="Useful but niche.",
        viability_score=0.73,
        viability_confidence=0.64,
        viability_rationale="Technical gap looks tractable.",
        assessment_version="test-v1",
        rationale="Explicitly stated as open.",
        evidence_snippet="Conjecture.",
        raw_response_json='{"label":"real_open_conjecture"}',
    )

    records = db.list_real_conjectures_for_solver(
        label_model="gpt-5-mini",
        min_confidence=0.9,
        min_viability=0.7,
        conjecture_id=conjecture_id,
    )
    assert len(records) == 1
    assert records[0]["conjecture_id"] == conjecture_id
    assert records[0]["viability_score"] == 0.73
    assert records[0]["abs_url"] == paper.abs_url

    db.create_solver_attempt(
        conjecture_id=conjecture_id,
        label_model="gpt-5-mini",
        solver_model="gpt-5.4",
        prompt_version="solver-test-v1",
        reasoning_effort="xhigh",
        search_context_size="high",
        response_id="resp_123",
        status="queued",
        instructions="system",
        prompt_text="user",
    )
    queued = db.get_solver_attempt(response_id="resp_123")
    assert queued is not None
    assert queued["status"] == "queued"
    assert queued["solver_model"] == "gpt-5.4"

    db.update_solver_attempt(
        "resp_123",
        status="completed",
        output_text="Proof sketch.",
        sources_json='[{"url":"https://example.com"}]',
        raw_response_json='{"id":"resp_123"}',
        error_json="",
        completed_at="2026-03-08T12:00:00Z",
    )
    completed = db.get_solver_attempt(response_id="resp_123")
    assert completed is not None
    assert completed["status"] == "completed"
    assert completed["output_text"] == "Proof sketch."
    assert completed["completed_at"] == "2026-03-08T12:00:00Z"

    listed = db.list_solver_attempts(conjecture_id=conjecture_id)
    assert len(listed) == 1
    assert listed[0]["attempt_id"] == queued["id"]
    assert listed[0]["output_length"] == len("Proof sketch.")
    assert listed[0]["viability_score"] == 0.73

    exported = db.export_solver_attempts(output_dir=tmp_path / "solver_exports")
    assert exported["solver_attempts_jsonl"].exists()
    assert exported["solver_attempts_csv"].exists()
    exported_row = json.loads(exported["solver_attempts_jsonl"].read_text(encoding="utf-8").strip())
    assert exported_row["response_id"] == "resp_123"
    assert exported_row["status"] == "completed"
    db.close()
