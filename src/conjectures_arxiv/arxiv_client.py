from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime
import xml.etree.ElementTree as ET

import requests

from .models import Paper


ARXIV_API_URL = "https://export.arxiv.org/api/query"
ATOM_NS = {
    "atom": "http://www.w3.org/2005/Atom",
    "opensearch": "http://a9.com/-/spec/opensearch/1.1/",
    "arxiv": "http://arxiv.org/schemas/atom",
}


@dataclass(frozen=True)
class FeedPage:
    total_results: int
    papers: list[Paper]


def format_arxiv_date_range(from_date: date, to_date: date) -> str:
    start = from_date.strftime("%Y%m%d") + "0000"
    end = to_date.strftime("%Y%m%d") + "2359"
    return f"[{start} TO {end}]"


class ArxivClient:
    def __init__(self, session: requests.Session | None = None, page_size: int = 200) -> None:
        self.session = session or requests.Session()
        self.page_size = page_size
        self.session.headers.setdefault("User-Agent", "conjectures-arxiv/0.1.0")

    def iter_math_papers(
        self,
        from_date: date,
        to_date: date,
        max_results: int | None = None,
    ):
        range_expr = format_arxiv_date_range(from_date=from_date, to_date=to_date)
        search_query = f"cat:math* AND submittedDate:{range_expr}"

        start = 0
        yielded = 0
        total_results = None

        while True:
            params = {
                "search_query": search_query,
                "sortBy": "submittedDate",
                "sortOrder": "descending",
                "start": start,
                "max_results": self.page_size,
            }
            response = self.session.get(ARXIV_API_URL, params=params, timeout=60)
            response.raise_for_status()

            page = self.parse_atom_feed(response.text)
            if total_results is None:
                total_results = page.total_results

            if not page.papers:
                break

            for paper in page.papers:
                if max_results is not None and yielded >= max_results:
                    return
                yield paper
                yielded += 1

            start += len(page.papers)
            if start >= total_results:
                break

    def parse_atom_feed(self, xml_text: str) -> FeedPage:
        root = ET.fromstring(xml_text)

        total_results_text = root.findtext("opensearch:totalResults", default="0", namespaces=ATOM_NS)
        total_results = int(total_results_text)

        entries = root.findall("atom:entry", namespaces=ATOM_NS)
        papers = [self._parse_entry(entry) for entry in entries]
        return FeedPage(total_results=total_results, papers=papers)

    def _parse_entry(self, entry: ET.Element) -> Paper:
        abs_url = entry.findtext("atom:id", default="", namespaces=ATOM_NS).strip()
        if not abs_url:
            raise ValueError("Missing arXiv entry id URL")

        arxiv_id = self._extract_arxiv_id(abs_url)
        pdf_url = self._extract_pdf_url(entry, arxiv_id=arxiv_id)
        source_url = f"https://arxiv.org/e-print/{arxiv_id}"

        authors = [
            author.findtext("atom:name", default="", namespaces=ATOM_NS).strip()
            for author in entry.findall("atom:author", namespaces=ATOM_NS)
        ]
        categories = [category.attrib.get("term", "") for category in entry.findall("atom:category", namespaces=ATOM_NS)]

        published_text = entry.findtext("atom:published", default="", namespaces=ATOM_NS)
        updated_text = entry.findtext("atom:updated", default="", namespaces=ATOM_NS)
        license_url = entry.findtext("arxiv:license", default="", namespaces=ATOM_NS).strip()

        return Paper(
            arxiv_id=arxiv_id,
            title=_normalize_ws(entry.findtext("atom:title", default="", namespaces=ATOM_NS)),
            summary=_normalize_ws(entry.findtext("atom:summary", default="", namespaces=ATOM_NS)),
            authors=[name for name in authors if name],
            categories=[term for term in categories if term],
            published_at=_parse_timestamp(published_text),
            updated_at=_parse_timestamp(updated_text),
            abs_url=abs_url,
            pdf_url=pdf_url,
            source_url=source_url,
            license_url=license_url,
        )

    @staticmethod
    def _extract_arxiv_id(abs_url: str) -> str:
        marker = "/abs/"
        if marker not in abs_url:
            raise ValueError(f"Unexpected arXiv id URL format: {abs_url}")
        return abs_url.split(marker, maxsplit=1)[1]

    def _extract_pdf_url(self, entry: ET.Element, arxiv_id: str) -> str:
        for link in entry.findall("atom:link", namespaces=ATOM_NS):
            href = link.attrib.get("href", "")
            link_type = link.attrib.get("type", "")
            title = link.attrib.get("title", "")
            if link_type == "application/pdf" or title == "pdf" or "/pdf/" in href:
                return href
        return f"https://arxiv.org/pdf/{arxiv_id}.pdf"


def _normalize_ws(text: str) -> str:
    return " ".join(text.split())


def _parse_timestamp(value: str) -> datetime:
    if not value:
        raise ValueError("Missing timestamp in arXiv feed entry")
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
