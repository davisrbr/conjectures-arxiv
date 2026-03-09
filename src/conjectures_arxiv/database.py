from __future__ import annotations

from collections import Counter
import csv
from datetime import UTC, datetime
import json
from pathlib import Path
import shutil
import sqlite3
from typing import Any

from .conjecture_extractor import ExtractedConjecture
from .license_policy import PUBLICATION_POLICY_VERSION, publication_metadata_from_license
from .models import Paper


TIMESTAMP_FMT = "%Y-%m-%dT%H:%M:%SZ"


def utc_now_str() -> str:
    return datetime.now(UTC).strftime(TIMESTAMP_FMT)


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
                viability_score REAL NOT NULL DEFAULT 0.0,
                viability_confidence REAL NOT NULL DEFAULT 0.0,
                viability_rationale TEXT NOT NULL DEFAULT '',
                assessment_version TEXT NOT NULL DEFAULT '',
                rationale TEXT NOT NULL,
                evidence_snippet TEXT NOT NULL,
                raw_response_json TEXT NOT NULL,
                created_at TEXT NOT NULL,
                UNIQUE(conjecture_id, model),
                FOREIGN KEY(conjecture_id) REFERENCES conjectures(id) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS conjecture_solver_attempts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                conjecture_id INTEGER NOT NULL,
                label_model TEXT NOT NULL DEFAULT '',
                solver_model TEXT NOT NULL,
                prompt_version TEXT NOT NULL DEFAULT '',
                reasoning_effort TEXT NOT NULL DEFAULT '',
                search_context_size TEXT NOT NULL DEFAULT '',
                response_id TEXT NOT NULL UNIQUE,
                status TEXT NOT NULL,
                instructions TEXT NOT NULL DEFAULT '',
                prompt_text TEXT NOT NULL DEFAULT '',
                output_text TEXT NOT NULL DEFAULT '',
                sources_json TEXT NOT NULL DEFAULT '[]',
                raw_response_json TEXT NOT NULL DEFAULT '{}',
                error_json TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                completed_at TEXT,
                FOREIGN KEY(conjecture_id) REFERENCES conjectures(id) ON DELETE CASCADE
            );

            CREATE INDEX IF NOT EXISTS idx_solver_attempts_conjecture
                ON conjecture_solver_attempts (conjecture_id);

            CREATE INDEX IF NOT EXISTS idx_solver_attempts_status
                ON conjecture_solver_attempts (status);
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
            column_name="viability_score",
            definition="REAL NOT NULL DEFAULT 0.0",
        )
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="viability_confidence",
            definition="REAL NOT NULL DEFAULT 0.0",
        )
        self._ensure_column(
            table_name="conjecture_llm_labels",
            column_name="viability_rationale",
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

    def export_huggingface_dataset(
        self,
        output_dir: str | Path,
        *,
        repo_id: str = "",
    ) -> dict[str, Path]:
        out_dir = Path(output_dir)
        data_dir = out_dir / "data"
        if data_dir.exists():
            shutil.rmtree(data_dir)
        data_dir.mkdir(parents=True, exist_ok=True)

        public_conjectures = self._public_conjecture_records()
        public_papers = self._public_paper_records(public_conjectures)
        manifest = self._publication_manifest(public_conjectures, public_papers, repo_id=repo_id)

        conjectures_jsonl = data_dir / "conjectures.jsonl"
        conjectures_csv = data_dir / "conjectures.csv"
        papers_jsonl = data_dir / "papers.jsonl"
        papers_csv = data_dir / "papers.csv"
        manifest_json = data_dir / "publication_manifest.json"
        readme_path = out_dir / "README.md"

        self._write_jsonl(conjectures_jsonl, public_conjectures)
        self._write_csv(conjectures_csv, public_conjectures)
        self._write_jsonl(papers_jsonl, public_papers)
        self._write_csv(papers_csv, public_papers)
        self._write_json(manifest_json, manifest)
        readme_path.write_text(
            self._build_huggingface_readme(manifest, repo_id=repo_id),
            encoding="utf-8",
        )

        return {
            "hf_readme": readme_path,
            "hf_conjectures_jsonl": conjectures_jsonl,
            "hf_conjectures_csv": conjectures_csv,
            "hf_papers_jsonl": papers_jsonl,
            "hf_papers_csv": papers_csv,
            "hf_manifest_json": manifest_json,
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

    def list_real_conjectures_for_solver(
        self,
        *,
        label_model: str,
        limit: int | None = None,
        min_confidence: float = 0.0,
        min_viability: float = 0.0,
        conjecture_id: int | None = None,
    ) -> list[dict[str, Any]]:
        sql = """
            SELECT
                c.id,
                c.arxiv_id,
                p.title,
                p.summary,
                p.authors_json,
                p.abs_url,
                p.pdf_url,
                p.source_url,
                c.source_file,
                c.start_line,
                c.end_line,
                c.raw_tex,
                c.body_tex,
                c.plain_text,
                l.label,
                l.confidence,
                l.interestingness_score,
                l.interestingness_confidence,
                l.interestingness_rationale,
                l.viability_score,
                l.viability_confidence,
                l.viability_rationale,
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
              AND l.viability_score >= ?
        """

        params: list[Any] = [label_model, min_confidence, min_viability]
        if conjecture_id is not None:
            sql += " AND c.id = ?"
            params.append(conjecture_id)

        sql += " ORDER BY l.viability_score DESC, l.interestingness_score DESC, c.id"
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
                    "abs_url": row[5],
                    "pdf_url": row[6],
                    "source_url": row[7],
                    "source_file": row[8],
                    "start_line": row[9],
                    "end_line": row[10],
                    "raw_tex": row[11],
                    "body_tex": row[12],
                    "plain_text": row[13],
                    "label": row[14],
                    "confidence": row[15],
                    "interestingness_score": row[16],
                    "interestingness_confidence": row[17],
                    "interestingness_rationale": row[18],
                    "viability_score": row[19],
                    "viability_confidence": row[20],
                    "viability_rationale": row[21],
                    "assessment_version": row[22],
                    "rationale": row[23],
                    "evidence_snippet": row[24],
                    "labeled_at": row[25],
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
        viability_score: float = 0.0,
        viability_confidence: float = 0.0,
        viability_rationale: str = "",
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
                viability_score,
                viability_confidence,
                viability_rationale,
                assessment_version,
                rationale,
                evidence_snippet,
                raw_response_json,
                created_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(conjecture_id, model) DO UPDATE SET
                label = excluded.label,
                confidence = excluded.confidence,
                interestingness_score = excluded.interestingness_score,
                interestingness_confidence = excluded.interestingness_confidence,
                interestingness_rationale = excluded.interestingness_rationale,
                viability_score = excluded.viability_score,
                viability_confidence = excluded.viability_confidence,
                viability_rationale = excluded.viability_rationale,
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
                viability_score,
                viability_confidence,
                viability_rationale,
                assessment_version,
                rationale,
                evidence_snippet,
                raw_response_json,
                utc_now_str(),
            ),
        )
        self.conn.commit()

    def create_solver_attempt(
        self,
        *,
        conjecture_id: int,
        label_model: str,
        solver_model: str,
        prompt_version: str,
        reasoning_effort: str,
        search_context_size: str,
        response_id: str,
        status: str,
        instructions: str,
        prompt_text: str,
        output_text: str = "",
        sources_json: str = "[]",
        raw_response_json: str = "{}",
        error_json: str = "",
        completed_at: str | None = None,
    ) -> None:
        now = utc_now_str()
        self.conn.execute(
            """
            INSERT INTO conjecture_solver_attempts (
                conjecture_id,
                label_model,
                solver_model,
                prompt_version,
                reasoning_effort,
                search_context_size,
                response_id,
                status,
                instructions,
                prompt_text,
                output_text,
                sources_json,
                raw_response_json,
                error_json,
                created_at,
                updated_at,
                completed_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                conjecture_id,
                label_model,
                solver_model,
                prompt_version,
                reasoning_effort,
                search_context_size,
                response_id,
                status,
                instructions,
                prompt_text,
                output_text,
                sources_json,
                raw_response_json,
                error_json,
                now,
                now,
                completed_at,
            ),
        )
        self.conn.commit()

    def update_solver_attempt(
        self,
        response_id: str,
        *,
        status: str,
        output_text: str = "",
        sources_json: str = "[]",
        raw_response_json: str = "{}",
        error_json: str = "",
        completed_at: str | None = None,
    ) -> None:
        self.conn.execute(
            """
            UPDATE conjecture_solver_attempts
            SET status = ?,
                output_text = ?,
                sources_json = ?,
                raw_response_json = ?,
                error_json = ?,
                updated_at = ?,
                completed_at = ?
            WHERE response_id = ?
            """,
            (
                status,
                output_text,
                sources_json,
                raw_response_json,
                error_json,
                utc_now_str(),
                completed_at,
                response_id,
            ),
        )
        self.conn.commit()

    def get_solver_attempt(self, *, response_id: str) -> dict[str, Any] | None:
        cursor = self.conn.execute(
            """
            SELECT
                id,
                conjecture_id,
                label_model,
                solver_model,
                prompt_version,
                reasoning_effort,
                search_context_size,
                response_id,
                status,
                instructions,
                prompt_text,
                output_text,
                sources_json,
                raw_response_json,
                error_json,
                created_at,
                updated_at,
                completed_at
            FROM conjecture_solver_attempts
            WHERE response_id = ?
            """,
            (response_id,),
        )
        row = cursor.fetchone()
        if row is None:
            return None
        return {
            "id": row[0],
            "conjecture_id": row[1],
            "label_model": row[2],
            "solver_model": row[3],
            "prompt_version": row[4],
            "reasoning_effort": row[5],
            "search_context_size": row[6],
            "response_id": row[7],
            "status": row[8],
            "instructions": row[9],
            "prompt_text": row[10],
            "output_text": row[11],
            "sources_json": row[12],
            "raw_response_json": row[13],
            "error_json": row[14],
            "created_at": row[15],
            "updated_at": row[16],
            "completed_at": row[17],
        }

    def list_solver_attempts(
        self,
        *,
        limit: int | None = None,
        response_id: str | None = None,
        conjecture_id: int | None = None,
        status: str | None = None,
    ) -> list[dict[str, Any]]:
        sql = """
            SELECT
                a.id,
                a.conjecture_id,
                c.arxiv_id,
                p.title,
                a.label_model,
                a.solver_model,
                a.prompt_version,
                a.reasoning_effort,
                a.search_context_size,
                a.response_id,
                a.status,
                a.instructions,
                a.prompt_text,
                a.output_text,
                a.sources_json,
                a.raw_response_json,
                a.error_json,
                a.created_at,
                a.updated_at,
                a.completed_at,
                COALESCE(l.viability_score, 0.0),
                COALESCE(l.interestingness_score, 0.0)
            FROM conjecture_solver_attempts a
            JOIN conjectures c ON c.id = a.conjecture_id
            JOIN papers p ON p.arxiv_id = c.arxiv_id
            LEFT JOIN conjecture_llm_labels l
                ON l.conjecture_id = a.conjecture_id
               AND l.model = a.label_model
            WHERE 1 = 1
        """

        params: list[Any] = []
        if response_id:
            sql += " AND a.response_id = ?"
            params.append(response_id)
        if conjecture_id is not None:
            sql += " AND a.conjecture_id = ?"
            params.append(conjecture_id)
        if status:
            sql += " AND a.status = ?"
            params.append(status)

        sql += " ORDER BY a.id DESC"
        if limit is not None:
            sql += " LIMIT ?"
            params.append(limit)

        cursor = self.conn.execute(sql, params)
        records: list[dict[str, Any]] = []
        for row in cursor.fetchall():
            output_text = str(row[13] or "")
            records.append(
                {
                    "attempt_id": row[0],
                    "conjecture_id": row[1],
                    "arxiv_id": row[2],
                    "title": row[3],
                    "label_model": row[4],
                    "solver_model": row[5],
                    "prompt_version": row[6],
                    "reasoning_effort": row[7],
                    "search_context_size": row[8],
                    "response_id": row[9],
                    "status": row[10],
                    "instructions": row[11],
                    "prompt_text": row[12],
                    "output_text": output_text,
                    "output_length": len(output_text),
                    "sources_json": row[14],
                    "raw_response_json": row[15],
                    "error_json": row[16],
                    "created_at": row[17],
                    "updated_at": row[18],
                    "completed_at": row[19],
                    "viability_score": row[20],
                    "interestingness_score": row[21],
                }
            )
        return records

    def export_solver_attempts(
        self,
        *,
        output_dir: str | Path,
        limit: int | None = None,
        response_id: str | None = None,
        conjecture_id: int | None = None,
        status: str | None = None,
    ) -> dict[str, Path]:
        out_dir = Path(output_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        jsonl_path = out_dir / "solver_attempts.jsonl"
        csv_path = out_dir / "solver_attempts.csv"

        records = self.list_solver_attempts(
            limit=limit,
            response_id=response_id,
            conjecture_id=conjecture_id,
            status=status,
        )
        self._write_jsonl(jsonl_path, records)
        self._write_csv(csv_path, records)
        return {"solver_attempts_jsonl": jsonl_path, "solver_attempts_csv": csv_path}

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
                l.viability_score,
                l.viability_confidence,
                l.viability_rationale,
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
                    "viability_score": row[16],
                    "viability_confidence": row[17],
                    "viability_rationale": row[18],
                    "assessment_version": row[19],
                    "rationale": row[20],
                    "evidence_snippet": row[21],
                    "labeled_at": row[22],
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

    def _public_conjecture_records(self) -> list[dict[str, Any]]:
        latest_labels = self._latest_llm_label_records()
        records = []
        for record in self._joined_conjecture_records():
            public_record = record.copy()
            public_record.update(
                latest_labels.get(
                    int(public_record["id"]),
                    self._empty_latest_llm_label_record(),
                )
            )
            public_record["text_withheld"] = not bool(public_record["publication_text_allowed"])
            if public_record["text_withheld"]:
                public_record["body_tex"] = ""
                public_record["plain_text"] = ""
            records.append(public_record)
        return records

    def _public_paper_records(self, public_conjectures: list[dict[str, Any]]) -> list[dict[str, Any]]:
        paper_counts: dict[str, Counter[str]] = {}
        for record in public_conjectures:
            arxiv_id = str(record["arxiv_id"])
            counts = paper_counts.setdefault(arxiv_id, Counter())
            counts["total"] += 1
            counts[str(record["publication_decision"])] += 1

        papers = []
        for record in self._paper_records():
            counts = paper_counts.get(str(record["arxiv_id"]), Counter())
            public_record = record.copy()
            public_record["conjecture_count"] = counts.get("total", 0)
            public_record["conjectures_with_public_text"] = counts.get("publish_text", 0)
            public_record["conjectures_withheld_text"] = counts.get("withhold_text", 0)
            papers.append(public_record)
        return papers

    def _publication_manifest(
        self,
        public_conjectures: list[dict[str, Any]],
        public_papers: list[dict[str, Any]],
        *,
        repo_id: str,
    ) -> dict[str, Any]:
        decision_counts = Counter(str(record["publication_decision"]) for record in public_conjectures)
        reason_counts = Counter(str(record["publication_text_reason"]) for record in public_conjectures)
        family_counts = Counter(str(record["license_family"]) for record in public_conjectures)
        license_counts = Counter(str(record["normalized_license_url"] or "(missing)") for record in public_conjectures)
        labeled_count = sum(1 for record in public_conjectures if record["latest_label"] is not None)

        return {
            "generated_at": utc_now_str(),
            "repo_id": repo_id,
            "publication_policy_version": PUBLICATION_POLICY_VERSION,
            "papers_total": len(public_papers),
            "conjectures_total": len(public_conjectures),
            "conjectures_with_public_text": decision_counts.get("publish_text", 0),
            "conjectures_withheld_text": decision_counts.get("withhold_text", 0),
            "conjectures_with_latest_label": labeled_count,
            "conjectures_by_decision": dict(sorted(decision_counts.items())),
            "conjectures_by_reason": dict(sorted(reason_counts.items())),
            "conjectures_by_license_family": dict(sorted(family_counts.items())),
            "conjectures_by_license_url": dict(sorted(license_counts.items())),
        }

    def _build_huggingface_readme(self, manifest: dict[str, Any], *, repo_id: str) -> str:
        repo_line = f"- Target repo: `{repo_id}`\n" if repo_id else ""
        return (
            "---\n"
            "license: other\n"
            "pretty_name: Conjectures from Recent arXiv Math Papers\n"
            "tags:\n"
            "- mathematics\n"
            "- arxiv\n"
            "- license-filtered\n"
            "---\n\n"
            "# Conjectures from Recent arXiv Math Papers\n\n"
            "This dataset contains conjecture candidates extracted from recent arXiv math papers.\n"
            "It is prepared from the local SQLite snapshot in this repository.\n\n"
            "## Snapshot Summary\n\n"
            f"- Papers: {manifest['papers_total']}\n"
            f"- Conjectures: {manifest['conjectures_total']}\n"
            f"- Conjectures with text published: {manifest['conjectures_with_public_text']}\n"
            f"- Conjectures with text withheld: {manifest['conjectures_withheld_text']}\n"
            f"- Conjectures with latest LLM label metadata: {manifest['conjectures_with_latest_label']}\n"
            f"- Publication policy version: `{manifest['publication_policy_version']}`\n"
            f"{repo_line}"
            "\n"
            "## Licensing Policy\n\n"
            "This publication pipeline is intentionally aggressive by default:\n"
            "if a paper license is missing or unfamiliar, the conjecture text is still published.\n"
            "Text is withheld only when the license is clearly restrictive for broad republication.\n\n"
            "This Hugging Face release is prepared as a noncommercial dataset release, so "
            "`CC BY-NC*` material is included.\n\n"
            "Current withhold rules:\n\n"
            "- arXiv non-exclusive distribution license (`arxiv.org/licenses/nonexclusive-distrib/1.0/`)\n\n"
            "When text is withheld, the record still includes the paper identifier, URLs, and source location.\n"
            "This policy metadata is exposed per record in `publication_decision`, `publication_text_reason`, "
            "and `publication_policy_version`.\n\n"
            "## Labels and Scores\n\n"
            "The public conjecture rows also include the newest available LLM label metadata for each conjecture.\n"
            "If multiple label runs exist, the latest one wins.\n"
            "These fields are preserved even when the conjecture text itself is withheld.\n\n"
            "## Files\n\n"
            "- `data/conjectures.jsonl`: public conjecture records with text redacted only when policy requires it\n"
            "- `data/papers.jsonl`: paper metadata plus counts of redacted versus published conjectures per paper\n"
            "- `data/publication_manifest.json`: aggregate counts for the publication decision pipeline\n\n"
            "## Notes\n\n"
            "- `license: other` is used because the dataset mixes paper-level licenses and publication decisions.\n"
            "- This is operational guidance for dataset publication, not legal advice.\n"
        )

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
            record = {
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
            record.update(publication_metadata_from_license(str(record["license_url"])))
            records.append(record)
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
            record = {
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
            record.update(publication_metadata_from_license(str(record["license_url"])))
            records.append(record)
        return records

    def _latest_llm_label_records(self) -> dict[int, dict[str, Any]]:
        cursor = self.conn.execute(
            """
            SELECT
                id,
                conjecture_id,
                model,
                label,
                confidence,
                interestingness_score,
                interestingness_confidence,
                interestingness_rationale,
                viability_score,
                viability_confidence,
                viability_rationale,
                assessment_version,
                rationale,
                evidence_snippet,
                created_at
            FROM conjecture_llm_labels
            ORDER BY created_at DESC, id DESC
            """
        )

        latest_by_conjecture: dict[int, dict[str, Any]] = {}
        for row in cursor.fetchall():
            conjecture_id = int(row[1])
            if conjecture_id in latest_by_conjecture:
                continue
            latest_by_conjecture[conjecture_id] = {
                "latest_label_model": row[2],
                "latest_label": row[3],
                "latest_label_confidence": row[4],
                "latest_interestingness_score": row[5],
                "latest_interestingness_confidence": row[6],
                "latest_interestingness_rationale": row[7],
                "latest_viability_score": row[8],
                "latest_viability_confidence": row[9],
                "latest_viability_rationale": row[10],
                "latest_assessment_version": row[11],
                "latest_label_rationale": row[12],
                "latest_evidence_snippet": row[13],
                "latest_labeled_at": row[14],
            }
        return latest_by_conjecture

    @staticmethod
    def _empty_latest_llm_label_record() -> dict[str, Any]:
        return {
            "latest_label_model": None,
            "latest_label": None,
            "latest_label_confidence": None,
            "latest_interestingness_score": None,
            "latest_interestingness_confidence": None,
            "latest_interestingness_rationale": None,
            "latest_viability_score": None,
            "latest_viability_confidence": None,
            "latest_viability_rationale": None,
            "latest_assessment_version": None,
            "latest_label_rationale": None,
            "latest_evidence_snippet": None,
            "latest_labeled_at": None,
        }

    @staticmethod
    def _write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
        with path.open("w", encoding="utf-8") as handle:
            for record in records:
                handle.write(json.dumps(record, ensure_ascii=False))
                handle.write("\n")

    @staticmethod
    def _write_json(path: Path, payload: dict[str, Any]) -> None:
        path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

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
