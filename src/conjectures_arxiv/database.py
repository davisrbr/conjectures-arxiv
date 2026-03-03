from __future__ import annotations

import csv
from datetime import datetime
import json
from pathlib import Path
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
                published_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                abs_url TEXT NOT NULL,
                pdf_url TEXT NOT NULL,
                source_url TEXT NOT NULL,
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
            """
        )
        self.conn.commit()

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
                published_at,
                updated_at,
                abs_url,
                pdf_url,
                source_url,
                ingested_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(arxiv_id) DO UPDATE SET
                title = excluded.title,
                summary = excluded.summary,
                authors_json = excluded.authors_json,
                categories_json = excluded.categories_json,
                published_at = excluded.published_at,
                updated_at = excluded.updated_at,
                abs_url = excluded.abs_url,
                pdf_url = excluded.pdf_url,
                source_url = excluded.source_url,
                ingested_at = excluded.ingested_at
            """,
            (
                paper.arxiv_id,
                paper.title,
                paper.summary,
                json.dumps(paper.authors),
                json.dumps(paper.categories),
                paper.published_at.strftime(TIMESTAMP_FMT),
                paper.updated_at.strftime(TIMESTAMP_FMT),
                paper.abs_url,
                paper.pdf_url,
                paper.source_url,
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
                p.abs_url,
                p.pdf_url,
                p.source_url,
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
                    "abs_url": row[7],
                    "pdf_url": row[8],
                    "source_url": row[9],
                    "source_file": row[10],
                    "index_in_file": row[11],
                    "start_line": row[12],
                    "end_line": row[13],
                    "body_tex": row[14],
                    "plain_text": row[15],
                    "content_hash": row[16],
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
                published_at,
                updated_at,
                abs_url,
                pdf_url,
                source_url,
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
                    "published_at": row[5],
                    "updated_at": row[6],
                    "abs_url": row[7],
                    "pdf_url": row[8],
                    "source_url": row[9],
                    "ingested_at": row[10],
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
