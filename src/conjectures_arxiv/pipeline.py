from __future__ import annotations

from dataclasses import dataclass
from datetime import date
import logging
import time

from .arxiv_client import ArxivClient
from .conjecture_extractor import extract_conjectures_from_documents
from .database import Database
from .source_fetcher import SourceFetcher


@dataclass(frozen=True)
class IngestionResult:
    papers_seen: int
    papers_stored: int
    conjectures_stored: int
    errors: int
    run_id: int


class IngestionPipeline:
    def __init__(
        self,
        db: Database,
        arxiv_client: ArxivClient | None = None,
        source_fetcher: SourceFetcher | None = None,
        logger: logging.Logger | None = None,
    ) -> None:
        self.db = db
        self.arxiv_client = arxiv_client or ArxivClient()
        self.source_fetcher = source_fetcher or SourceFetcher()
        self.logger = logger or logging.getLogger(__name__)

    def ingest(
        self,
        *,
        from_date: date,
        to_date: date,
        max_papers: int | None = None,
        sleep_seconds: float = 0.2,
    ) -> IngestionResult:
        run_id = self.db.start_run(from_date=from_date.isoformat(), to_date=to_date.isoformat())

        papers_seen = 0
        papers_stored = 0
        conjectures_stored = 0
        errors = 0
        notes: list[str] = []

        try:
            for paper in self.arxiv_client.iter_math_papers(
                from_date=from_date,
                to_date=to_date,
                max_results=max_papers,
            ):
                papers_seen += 1
                self.db.upsert_paper(paper)
                papers_stored += 1

                try:
                    documents = self.source_fetcher.fetch_documents(paper.source_url)
                    extracted = extract_conjectures_from_documents(documents)
                    inserted = self.db.insert_conjectures(paper.arxiv_id, extracted)
                    conjectures_stored += inserted
                except Exception as exc:  # noqa: BLE001
                    errors += 1
                    note = f"{paper.arxiv_id}: {exc}"
                    notes.append(note)
                    self.logger.warning("Failed extracting %s: %s", paper.arxiv_id, exc)

                if sleep_seconds > 0:
                    time.sleep(sleep_seconds)

            status = "success" if errors == 0 else "partial_success"
            self.db.finish_run(
                run_id,
                status=status,
                papers_seen=papers_seen,
                papers_stored=papers_stored,
                conjectures_stored=conjectures_stored,
                notes=" | ".join(notes[:25]),
            )
        except Exception:  # noqa: BLE001
            self.db.finish_run(
                run_id,
                status="failed",
                papers_seen=papers_seen,
                papers_stored=papers_stored,
                conjectures_stored=conjectures_stored,
                notes=" | ".join(notes[:25]),
            )
            raise

        return IngestionResult(
            papers_seen=papers_seen,
            papers_stored=papers_stored,
            conjectures_stored=conjectures_stored,
            errors=errors,
            run_id=run_id,
        )
