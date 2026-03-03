from datetime import date, datetime

from conjectures_arxiv.database import Database
from conjectures_arxiv.models import LatexDocument, Paper
from conjectures_arxiv.pipeline import IngestionPipeline


class FakeArxivClient:
    def iter_math_papers(self, from_date, to_date, max_results=None):
        del from_date, to_date, max_results
        yield Paper(
            arxiv_id="2603.00077v1",
            title="Pipeline Test",
            summary="",
            authors=["A"],
            categories=["math.CO"],
            primary_category="math.CO",
            doi="",
            journal_ref="",
            comments="",
            published_at=datetime(2026, 3, 2, 0, 0, 0),
            updated_at=datetime(2026, 3, 2, 0, 0, 0),
            abs_url="https://arxiv.org/abs/2603.00077v1",
            pdf_url="https://arxiv.org/pdf/2603.00077v1.pdf",
            source_url="https://arxiv.org/e-print/2603.00077v1",
        )


class FakeSourceFetcher:
    def fetch_documents(self, source_url):
        del source_url
        return [
            LatexDocument(
                filename="main.tex",
                content="\\begin{conjecture}Test claim\\end{conjecture}",
            )
        ]


def test_pipeline_ingest(tmp_path) -> None:
    db = Database(tmp_path / "c.sqlite")
    db.init_schema()

    pipeline = IngestionPipeline(db=db, arxiv_client=FakeArxivClient(), source_fetcher=FakeSourceFetcher())
    result = pipeline.ingest(from_date=date(2026, 2, 25), to_date=date(2026, 3, 3), sleep_seconds=0)

    assert result.papers_seen == 1
    assert result.papers_stored == 1
    assert result.conjectures_stored == 1
    assert result.errors == 0

    db.close()
