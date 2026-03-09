from datetime import datetime

from conjectures_arxiv.cli import main
from conjectures_arxiv.conjecture_extractor import ExtractedConjecture
from conjectures_arxiv.database import Database
from conjectures_arxiv.models import Paper


def _seed_database(db_path) -> None:  # noqa: ANN001
    db = Database(db_path)
    db.init_schema()
    db.upsert_paper(
        Paper(
            arxiv_id="2603.00999v1",
            title="CLI Test",
            summary="Summary",
            authors=["Alice"],
            categories=["math.CO"],
            primary_category="math.CO",
            doi="",
            journal_ref="",
            comments="",
            published_at=datetime(2026, 3, 1, 10, 0, 0),
            updated_at=datetime(2026, 3, 1, 10, 0, 0),
            abs_url="https://arxiv.org/abs/2603.00999v1",
            pdf_url="https://arxiv.org/pdf/2603.00999v1.pdf",
            source_url="https://arxiv.org/e-print/2603.00999v1",
            license_url="https://creativecommons.org/licenses/by-nc-nd/4.0/",
        )
    )
    db.insert_conjectures(
        "2603.00999v1",
        [
            ExtractedConjecture(
                source_file="main.tex",
                index_in_file=1,
                start_line=10,
                end_line=12,
                raw_tex="\\begin{conjecture}X\\end{conjecture}",
                body_tex="X",
                plain_text="X",
                content_hash="hash-cli",
            )
        ],
    )
    conjecture_id = int(db.list_conjectures_for_llm(model="gpt-5-mini")[0]["conjecture_id"])
    db.upsert_llm_label(
        conjecture_id=conjecture_id,
        model="gpt-5-mini",
        label="real_open_conjecture",
        confidence=0.87,
        interestingness_score=0.81,
        interestingness_confidence=0.78,
        interestingness_rationale="Interesting CLI test.",
        viability_score=0.66,
        viability_confidence=0.63,
        viability_rationale="Viable CLI test.",
        assessment_version="cli-test-v1",
        rationale="CLI rationale.",
        evidence_snippet="CLI evidence.",
        raw_response_json='{"label":"real_open_conjecture"}',
    )
    db.close()


def test_publish_hf_dry_run_prepares_snapshot(tmp_path, capsys) -> None:
    db_path = tmp_path / "conjectures.sqlite"
    output_dir = tmp_path / "hf_dataset"
    _seed_database(db_path)

    exit_code = main(
        [
            "publish-hf",
            "--db-path",
            str(db_path),
            "--output-dir",
            str(output_dir),
            "--repo-id",
            "alice/conjectures-arxiv",
            "--dry-run",
        ]
    )

    assert exit_code == 0
    assert (output_dir / "README.md").exists()
    assert (output_dir / "data" / "conjectures.jsonl").exists()
    stdout = capsys.readouterr().out
    assert "withheld_text=0" in stdout
    assert "published_text=1" in stdout
    assert "latest_labels=1" in stdout
    assert "Dry run" in stdout


def test_export_hf_command_builds_snapshot(tmp_path) -> None:
    db_path = tmp_path / "conjectures.sqlite"
    output_dir = tmp_path / "hf_dataset"
    _seed_database(db_path)

    exit_code = main(
        [
            "export-hf",
            "--db-path",
            str(db_path),
            "--output-dir",
            str(output_dir),
        ]
    )

    assert exit_code == 0
    assert (output_dir / "README.md").exists()
    assert (output_dir / "data" / "publication_manifest.json").exists()
    conjectures_text = (output_dir / "data" / "conjectures.jsonl").read_text(encoding="utf-8")
    assert '"latest_viability_score": 0.66' in conjectures_text
