from __future__ import annotations

import csv
from datetime import datetime
import json
from pathlib import Path
import shutil
import sqlite3
from typing import Any

from .conjecture_extractor import ExtractedConjecture
from .models import Paper


TIMESTAMP_FMT = "%Y-%m-%dT%H:%M:%SZ"


def utc_now_str() -> str:
    return datetime.utcnow().strftime(TIMESTAMP_FMT)


class Database:
    def __init__(self, db_path: str | Path) -> None:
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(self.db_path)
        self.conn.execute("PRAGMA foreign_keys = ON")

    def close(self) -> None:
        self.conn.close()

    def init_schema(self) -> None:
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS papers (
                arxiv_id TEXT PRIMARY KEY,
                title TEXT NOT NULL,
                summary TEXT NOT NULL,
                authors_json TEXT NOT NULL,
                categories_json TEXT NOT NULL,
                primary_category TEXT NOT NULL DEFAULT '',
                doi TEXT NOT NULL DEFAULT '',
                journal_ref TEXT NOT NULL DEFAULT '',
                comments TEXT NOT NULL DEFAULT '',
                published_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                abs_url TEXT NOT NULL,
                pdf_url TEXT NOT NULL,
                source_url TEXT NOT NULL,
                license_url TEXT NOT NULL DEFAULT '',
                ingested_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS conjectures (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                arxiv_id TEXT NOT NULL,
                source_file TEXT NOT NULL,
                index_in_file INTEGER NOT NULL,
                start_line INTEGER NOT NULL,
                end_line INTEGER NOT NULL,
                raw_tex TEXT NOT NULL,
                body_tex TEXT NOT NULL,
                plain_text TEXT NOT NULL,
                content_hash TEXT NOT NULL,
                created_at TEXT NOT NULL,
                UNIQUE(arxiv_id, content_hash),
                FOREIGN KEY(arxiv_id) REFERENCES papers(arxiv_id) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS ingestion_runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                started_at TEXT NOT NULL,
                completed_at TEXT,
                from_date TEXT NOT NULL,
                to_date TEXT NOT NULL,
                status TEXT NOT NULL,
                papers_seen INTEGER NOT NULL DEFAULT 0,
                papers_stored INTEGER NOT NULL DEFAULT 0,
                conjectures_stored INTEGER NOT NULL DEFAULT 0,
                notes TEXT
            );

            CREATE TABLE IF NOT EXISTS conjecture_llm_labels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                conjecture_id INTEGER NOT NULL,
                model TEXT NOT NULL,
                label TEXT NOT NULL,
                confidence REAL NOT NULL,
                interestingness_score REAL NOT NULL DEFAULT 0.0,
                interestingness_confidence REAL NOT NULL DEFAULT 0.0,
                interestingness_rationale TEXT NOT NULL DEFAULT '',
                assessment_version TEXT NOT NULL DEFAULT '',
                rationale TEXT NOT NULL,
                evidence_snippet TEXT NOT NULL,
                raw_response_json TEXT NOT NULL,
                created_at TEXT NOT NULL,
                UNIQUE(conjecture_id, model),
                FOREIGN KEY(conjecture_id) REFERENCES conjectures(id) ON DELETE CASCADE
            );
            """
        )
        self._ensure_paper_columns()
        self._ensure_llm_label_columns()
        self.conn.commit()

    def _ensure_paper_columns(self) -> None:
        self._ensure_column(
            table_name="papers",
            column_name="primary_category",
            definition="TEXT NOT NULL DEFAULT ''",
        )
        self._ensure_column(
            table_name="papers",
            column_name="doi",
            definition="TEXT NOT NULL DEFAULT ''",
        )
        self._ensure_column(
            table_name="papers",
            column_name="journal_ref",
            definition="TEXT NOT NULL DEFAULT ''",
        )
        self._ensure_column(
            table_name="papers",
            column_name="comments",
            definition="TEXT NOT NULL DEFAULT ''",
        )
        self._ensure_column(
            table_name="papers",
            column_name="license_url",
            definition="TEXT NOT NULL DEFAULT ''",
        )

    def _ensure_llm_label_columns(self) -> None:
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="interestingness_score",
            definition="REAL NOT NULL DEFAULT 0.0",
        )
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="interestingness_confidence",
            definition="REAL NOT NULL DEFAULT 0.0",
        )
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="interestingness_rationale",
            definition="TEXT NOT NULL DEFAULT ''",
        )
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="assessment_version",
            definition="TEXT NOT NULL DEFAULT ''",
        )

    def _ensure_column(self, *, table_name: str, column_name: str, definition: str) -> None:
        cursor = self.conn.execute(f"PRAGMA table_info({table_name})")
        existing = {str(row[1]) for row in cursor.fetchall()}
        if column_name in existing:
            return
        self.conn.execute(f"ALTER TABLE {table_name} ADD COLUMN {column_name} {definition}")

    def start_run(self, from_date: str, to_date: str) -> int:
        cursor = self.conn.execute(
            """
            INSERT INTO ingestion_runs (
                started_at,
                from_date,
                to_date,
                status
            )
            VALUES (?, ?, ?, ?)
            """,
            (utc_now_str(), from_date, to_date, "running"),
        )
        self.conn.commit()
        return int(cursor.lastrowid)

    def finish_run(
        self,
        run_id: int,
        *,
        status: str,
        papers_seen: int,
        papers_stored: int,
        conjectures_stored: int,
        notes: str = "",
    ) -> None:
        self.conn.execute(
            """
            UPDATE ingestion_runs
            SET completed_at = ?,
                status = ?,
                papers_seen = ?,
                papers_stored = ?,
                conjectures_stored = ?,
                notes = ?
            WHERE id = ?
            """,
            (
                utc_now_str(),
                status,
                papers_seen,
                papers_stored,
                conjectures_stored,
                notes,
                run_id,
            ),
        )
        self.conn.commit()

    def upsert_paper(self, paper: Paper) -> None:
        self.conn.execute(
            """
            INSERT INTO papers (
                arxiv_id,
                title,
                summary,
                authors_json,
                categories_json,
                primary_category,
                doi,
                journal_ref,
                comments,
                published_at,
                updated_at,
                abs_url,
                pdf_url,
                source_url,
                license_url,
                ingested_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(arxiv_id) DO UPDATE SET
                title = excluded.title,
                summary = excluded.summary,
                authors_json = excluded.authors_json,
                categories_json = excluded.categories_json,
                primary_category = excluded.primary_category,
                doi = excluded.doi,
                journal_ref = excluded.journal_ref,
                comments = excluded.comments,
                published_at = excluded.published_at,
                updated_at = excluded.updated_at,
                abs_url = excluded.abs_url,
                pdf_url = excluded.pdf_url,
                source_url = excluded.source_url,
                license_url = excluded.license_url,
                ingested_at = excluded.ingested_at
            """,
            (
                paper.arxiv_id,
                paper.title,
                paper.summary,
                json.dumps(paper.authors),
                json.dumps(paper.categories),
                paper.primary_category,
                paper.doi,
                paper.journal_ref,
                paper.comments,
                paper.published_at.strftime(TIMESTAMP_FMT),
                paper.updated_at.strftime(TIMESTAMP_FMT),
                paper.abs_url,
                paper.pdf_url,
                paper.source_url,
                paper.license_url,
                utc_now_str(),
            ),
        )
        self.conn.commit()

    def insert_conjectures(self, arxiv_id: str, conjectures: list[ExtractedConjecture]) -> int:
        inserted = 0
        for conjecture in conjectures:
            cursor = self.conn.execute(
                """
                INSERT OR IGNORE INTO conjectures (
                    arxiv_id,
                    source_file,
                    index_in_file,
                    start_line,
                    end_line,
                    raw_tex,
                    body_tex,
                    plain_text,
                    content_hash,
                    created_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    arxiv_id,
                    conjecture.source_file,
                    conjecture.index_in_file,
                    conjecture.start_line,
                    conjecture.end_line,
                    conjecture.raw_tex,
                    conjecture.body_tex,
                    conjecture.plain_text,
                    conjecture.content_hash,
                    utc_now_str(),
                ),
            )
            inserted += cursor.rowcount
        self.conn.commit()
        return inserted

    def export(self, output_dir: str | Path) -> dict[str, Path]:
        out_dir = Path(output_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        conjectures_jsonl = out_dir / "conjectures.jsonl"
        conjectures_csv = out_dir / "conjectures.csv"
        papers_jsonl = out_dir / "papers.jsonl"

        records = self._joined_conjecture_records()
        self._write_jsonl(conjectures_jsonl, records)
        self._write_csv(conjectures_csv, records)

        paper_records = self._paper_records()
        self._write_jsonl(papers_jsonl, paper_records)

        return {
            "conjectures_jsonl": conjectures_jsonl,
            "conjectures_csv": conjectures_csv,
            "papers_jsonl": papers_jsonl,
        }

    def list_conjectures_for_llm(
        self,
        *,
        model: str,
        limit: int | None = None,
        only_unlabeled: bool = True,
    ) -> list[dict[str, Any]]:
        sql = """
            SELECT
                c.id,
                c.arxiv_id,
                p.title,
                p.summary,
                p.authors_json,
                p.source_url,
                c.source_file,
                c.start_line,
                c.end_line,
                c.raw_tex,
                c.body_tex,
                c.plain_text
            FROM conjectures c
            JOIN papers p ON p.arxiv_id = c.arxiv_id
        """

        params: list[Any] = []
        if only_unlabeled:
            sql += """
            LEFT JOIN conjecture_llm_labels l
                ON l.conjecture_id = c.id
               AND l.model = ?
            WHERE l.id IS NULL
            """
            params.append(model)

        sql += " ORDER BY c.id"
        if limit is not None:
            sql += " LIMIT ?"
            params.append(limit)

        cursor = self.conn.execute(sql, params)
        records: list[dict[str, Any]] = []
        for row in cursor.fetchall():
            records.append(
                {
                    "conjecture_id": row[0],
                    "arxiv_id": row[1],
                    "title": row[2],
                    "summary": row[3],
                    "authors": json.loads(row[4]),
                    "source_url": row[5],
                    "source_file": row[6],
                    "start_line": row[7],
                    "end_line": row[8],
                    "raw_tex": row[9],
                    "body_tex": row[10],
                    "plain_text": row[11],
                }
            )
        return records

    def upsert_llm_label(
        self,
        *,
        conjecture_id: int,
        model: str,
        label: str,
        confidence: float,
        rationale: str,
        evidence_snippet: str,
        raw_response_json: str,
        interestingness_score: float = 0.0,
        interestingness_confidence: float = 0.0,
        interestingness_rationale: str = "",
        assessment_version: str = "",
    ) -> None:
        self.conn.execute(
            """
            INSERT INTO conjecture_llm_labels (
                conjecture_id,
                model,
                label,
                confidence,
                interestingness_score,
                interestingness_confidence,
                interestingness_rationale,
                assessment_version,
                rationale,
                evidence_snippet,
                raw_response_json,
                created_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(conjecture_id, model) DO UPDATE SET
                label = excluded.label,
                confidence = excluded.confidence,
                interestingness_score = excluded.interestingness_score,
                interestingness_confidence = excluded.interestingness_confidence,
                interestingness_rationale = excluded.interestingness_rationale,
                assessment_version = excluded.assessment_version,
                rationale = excluded.rationale,
                evidence_snippet = excluded.evidence_snippet,
                raw_response_json = excluded.raw_response_json,
                created_at = excluded.created_at
            """,
            (
                conjecture_id,
                model,
                label,
                confidence,
                interestingness_score,
                interestingness_confidence,
                interestingness_rationale,
                assessment_version,
                rationale,
                evidence_snippet,
                raw_response_json,
                utc_now_str(),
            ),
        )
        self.conn.commit()

    def llm_label_counts(self, *, model: str) -> dict[str, int]:
        cursor = self.conn.execute(
            """
            SELECT label, COUNT(*)
            FROM conjecture_llm_labels
            WHERE model = ?
            GROUP BY label
            """,
            (model,),
        )
        return {str(row[0]): int(row[1]) for row in cursor.fetchall()}

    def export_llm_real_conjectures(
        self,
        *,
        model: str,
        output_dir: str | Path,
        min_confidence: float = 0.0,
    ) -> dict[str, Path]:
        out_dir = Path(output_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        jsonl_path = out_dir / f"real_conjectures_{model.replace('/', '_')}.jsonl"
        csv_path = out_dir / f"real_conjectures_{model.replace('/', '_')}.csv"

        cursor = self.conn.execute(
            """
            SELECT
                c.id,
                c.arxiv_id,
                p.title,
                p.abs_url,
                p.pdf_url,
                p.source_url,
                c.source_file,
                c.start_line,
                c.end_line,
                c.body_tex,
                c.plain_text,
                l.label,
                l.confidence,
                l.interestingness_score,
                l.interestingness_confidence,
                l.interestingness_rationale,
                l.assessment_version,
                l.rationale,
                l.evidence_snippet,
                l.created_at
            FROM conjectures c
            JOIN papers p ON p.arxiv_id = c.arxiv_id
            JOIN conjecture_llm_labels l ON l.conjecture_id = c.id
            WHERE l.model = ?
              AND l.label = 'real_open_conjecture'
              AND l.confidence >= ?
            ORDER BY l.confidence DESC, c.id
            """,
            (model, min_confidence),
        )

        records: list[dict[str, Any]] = []
        for row in cursor.fetchall():
            records.append(
                {
                    "conjecture_id": row[0],
                    "arxiv_id": row[1],
                    "title": row[2],
                    "abs_url": row[3],
                    "pdf_url": row[4],
                    "source_url": row[5],
                    "source_file": row[6],
                    "start_line": row[7],
                    "end_line": row[8],
                    "body_tex": row[9],
                    "plain_text": row[10],
                    "label": row[11],
                    "confidence": row[12],
                    "interestingness_score": row[13],
                    "interestingness_confidence": row[14],
                    "interestingness_rationale": row[15],
                    "assessment_version": row[16],
                    "rationale": row[17],
                    "evidence_snippet": row[18],
                    "labeled_at": row[19],
                }
            )

        self._write_jsonl(jsonl_path, records)
        self._write_csv(csv_path, records)
        return {"real_conjectures_jsonl": jsonl_path, "real_conjectures_csv": csv_path}

    def export_parquet(self, output_dir: str | Path) -> dict[str, Path]:
        out_dir = Path(output_dir)
        parquet_root = out_dir / "parquet"
        conjectures_dir = parquet_root / "conjectures"
        papers_dir = parquet_root / "papers"

        for directory in (conjectures_dir, papers_dir):
            if directory.exists():
                shutil.rmtree(directory)
            directory.mkdir(parents=True, exist_ok=True)

        conjecture_records = self._with_partitions(self._joined_conjecture_records(), datetime_field="published_at")
        paper_records = self._with_partitions(self._paper_records(), datetime_field="published_at")

        self._write_parquet_dataset(conjecture_records, conjectures_dir)
        self._write_parquet_dataset(paper_records, papers_dir)

        return {
            "parquet_root": parquet_root,
            "conjectures_parquet": conjectures_dir,
            "papers_parquet": papers_dir,
        }

    def _joined_conjecture_records(self) -> list[dict[str, Any]]:
        cursor = self.conn.execute(
            """
            SELECT
                c.id,
                c.arxiv_id,
                p.title,
                p.published_at,
                p.updated_at,
                p.authors_json,
                p.categories_json,
                p.primary_category,
                p.doi,
                p.journal_ref,
                p.comments,
                p.abs_url,
                p.pdf_url,
                p.source_url,
                p.license_url,
                c.source_file,
                c.index_in_file,
                c.start_line,
                c.end_line,
                c.body_tex,
                c.plain_text,
                c.content_hash
            FROM conjectures c
            JOIN papers p ON p.arxiv_id = c.arxiv_id
            ORDER BY p.published_at DESC, c.arxiv_id, c.index_in_file
            """
        )

        records = []
        for row in cursor.fetchall():
            records.append(
                {
                    "id": row[0],
                    "arxiv_id": row[1],
                    "title": row[2],
                    "published_at": row[3],
                    "updated_at": row[4],
                    "authors": json.loads(row[5]),
                    "categories": json.loads(row[6]),
                    "primary_category": row[7],
                    "doi": row[8],
                    "journal_ref": row[9],
                    "comments": row[10],
                    "abs_url": row[11],
                    "pdf_url": row[12],
                    "source_url": row[13],
                    "license_url": row[14],
                    "source_file": row[15],
                    "index_in_file": row[16],
                    "start_line": row[17],
                    "end_line": row[18],
                    "body_tex": row[19],
                    "plain_text": row[20],
                    "content_hash": row[21],
                }
            )
        return records

    def _paper_records(self) -> list[dict[str, Any]]:
        cursor = self.conn.execute(
            """
            SELECT
                arxiv_id,
                title,
                summary,
                authors_json,
                categories_json,
                primary_category,
                doi,
                journal_ref,
                comments,
                published_at,
                updated_at,
                abs_url,
                pdf_url,
                source_url,
                license_url,
                ingested_at
            FROM papers
            ORDER BY published_at DESC
            """
        )

        records = []
        for row in cursor.fetchall():
            records.append(
                {
                    "arxiv_id": row[0],
                    "title": row[1],
                    "summary": row[2],
                    "authors": json.loads(row[3]),
                    "categories": json.loads(row[4]),
                    "primary_category": row[5],
                    "doi": row[6],
                    "journal_ref": row[7],
                    "comments": row[8],
                    "published_at": row[9],
                    "updated_at": row[10],
                    "abs_url": row[11],
                    "pdf_url": row[12],
                    "source_url": row[13],
                    "license_url": row[14],
                    "ingested_at": row[15],
                }
            )
        return records

    @staticmethod
    def _write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
        with path.open("w", encoding="utf-8") as handle:
            for record in records:
                handle.write(json.dumps(record, ensure_ascii=False))
                handle.write("\n")

    @staticmethod
    def _write_csv(path: Path, records: list[dict[str, Any]]) -> None:
        if not records:
            with path.open("w", newline="", encoding="utf-8"):
                return

        fieldnames = list(records[0].keys())
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            for record in records:
                csv_record = record.copy()
                if isinstance(csv_record.get("authors"), list):
                    csv_record["authors"] = ";".join(csv_record["authors"])
                if isinstance(csv_record.get("categories"), list):
                    csv_record["categories"] = ";".join(csv_record["categories"])
                writer.writerow(csv_record)

    @staticmethod
    def _write_parquet_dataset(records: list[dict[str, Any]], output_dir: Path) -> None:
        if not records:
            return

        try:
            import pyarrow as pa
            import pyarrow.dataset as ds
        except (ModuleNotFoundError, ImportError) as exc:
            raise RuntimeError("Parquet export requires pyarrow. Install with: pip install pyarrow") from exc

        table = pa.Table.from_pylist(records)
        ds.write_dataset(
            table,
            base_dir=str(output_dir),
            format="parquet",
            partitioning=["published_year", "published_month"],
            existing_data_behavior="overwrite_or_ignore",
        )

    @staticmethod
    def _with_partitions(records: list[dict[str, Any]], *, datetime_field: str) -> list[dict[str, Any]]:
        partitioned: list[dict[str, Any]] = []
        for record in records:
            copy = record.copy()
            timestamp = str(copy.get(datetime_field, ""))
            try:
                parsed = datetime.strptime(timestamp, TIMESTAMP_FMT)
                copy["published_year"] = parsed.year
                copy["published_month"] = parsed.month
            except ValueError:
                copy["published_year"] = 0
                copy["published_month"] = 0
            partitioned.append(copy)
        return partitioned
