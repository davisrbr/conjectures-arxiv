from datetime import datetime
import json

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
