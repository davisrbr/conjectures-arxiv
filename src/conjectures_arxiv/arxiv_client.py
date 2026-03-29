from __future__ import annotations

from dataclasses import dataclass, replace
from datetime import date, datetime, timedelta
import html
import re
import time
import xml.etree.ElementTree as ET

import requests

from .models import Paper


ARXIV_API_URL = "https://export.arxiv.org/api/query"
ARXIV_MATH_PASTWEEK_URL = "https://arxiv.org/list/math/pastweek?show=2000"
ATOM_NS = {
    "atom": "http://www.w3.org/2005/Atom",
    "opensearch": "http://a9.com/-/spec/opensearch/1.1/",
    "arxiv": "http://arxiv.org/schemas/atom",
}
RECENT_SECTION_PATTERN = re.compile(r"<h3>(?P<label>.*?)</h3>(?P<body>.*?)(?=<h3>|</dl>)", flags=re.DOTALL)
RECENT_ARXIV_ID_PATTERN = re.compile(r"arXiv:(?P<id>\d{4}\.\d{5})(?:v\d+)?")
META_TAG_PATTERN = re.compile(
    r"""<meta[^>]*\bname\s*=\s*["'](?P<name>[^"']+)["'][^>]*\bcontent\s*=\s*["'](?P<content>[^"']*)["'][^>]*>""",
    flags=re.IGNORECASE,
)
PRIMARY_SUBJECT_CODE_PATTERN = re.compile(
    r"""<span[^>]*class\s*=\s*["'][^"']*\bprimary-subject\b[^"']*["'][^>]*>.*?</span>\s*</td>\s*<td[^>]*>\((?P<code>[^)]+)\)""",
    flags=re.IGNORECASE | re.DOTALL,
)
LICENSE_REL_PATTERN = re.compile(
    r"""<a[^>]*\brel\s*=\s*["'][^"']*\blicense\b[^"']*["'][^>]*\bhref\s*=\s*["'](?P<href>[^"']+)["']""",
    flags=re.IGNORECASE,
)
LICENSE_URL_PATTERN = re.compile(
    r"""https?://(?:creativecommons\.org/licenses/[^"'<> ]+|arxiv\.org/licenses/[^"'<> ]+)""",
    flags=re.IGNORECASE,
)


@dataclass(frozen=True)
class FeedPage:
    total_results: int
    papers: list[Paper]


def format_arxiv_date_range(from_date: date, to_date: date) -> str:
    start = from_date.strftime("%Y%m%d") + "0000"
    end = to_date.strftime("%Y%m%d") + "2359"
    return f"[{start} TO {end}]"


class ArxivClient:
    def __init__(
        self,
        session: requests.Session | None = None,
        page_size: int = 100,
        request_timeout: int = 120,
        page_retry_attempts: int = 5,
        retry_sleep_seconds: float = 5.0,
    ) -> None:
        self.session = session or requests.Session()
        self.page_size = page_size
        self.request_timeout = request_timeout
        self.page_retry_attempts = max(1, page_retry_attempts)
        self.retry_sleep_seconds = max(0.0, retry_sleep_seconds)
        self.session.headers.setdefault("User-Agent", "conjectures-arxiv/0.1.0")

    def iter_math_papers(
        self,
        from_date: date,
        to_date: date,
        max_results: int | None = None,
        start_offset: int = 0,
    ):
        recent_cutoff = date.today() - timedelta(days=7)
        if from_date >= recent_cutoff:
            announced_ids = self._fetch_recent_math_announcement_ids(from_date=from_date, to_date=to_date)
            if announced_ids:
                selected_ids = announced_ids[max(0, start_offset) :]
                if max_results is not None:
                    selected_ids = selected_ids[:max_results]
                try:
                    yield from self._iter_papers_by_ids(selected_ids)
                except Exception as exc:  # noqa: BLE001
                    if not self._is_rate_limit_error(exc):
                        raise
                    yield from self._iter_papers_by_abs_pages(selected_ids)
                return

        range_expr = format_arxiv_date_range(from_date=from_date, to_date=to_date)
        search_query = f"cat:math* AND submittedDate:{range_expr}"

        start = max(0, start_offset)
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
            response = self._get_feed_page(params=params)

            page = self.parse_atom_feed(response.text)
            if total_results is None:
                total_results = page.total_results

            if not page.papers:
                break

            for paper in page.papers:
                if not paper.license_url:
                    fallback = self._fetch_license_from_abs(abs_url=paper.abs_url)
                    if fallback:
                        paper = replace(paper, license_url=fallback)
                if max_results is not None and yielded >= max_results:
                    return
                yield paper
                yielded += 1

            start += len(page.papers)
            if start >= total_results:
                break

    def _fetch_recent_math_announcement_ids(self, *, from_date: date, to_date: date) -> list[str]:
        response = self.session.get(ARXIV_MATH_PASTWEEK_URL, timeout=self.request_timeout)
        response.raise_for_status()
        html_text = response.text

        announced_ids: list[str] = []
        for match in RECENT_SECTION_PATTERN.finditer(html_text):
            label_text = html.unescape(match.group("label"))
            date_text = label_text.split("(", maxsplit=1)[0].strip()
            try:
                section_date = datetime.strptime(date_text, "%a, %d %b %Y").date()
            except ValueError:
                continue
            if not (from_date <= section_date <= to_date):
                continue
            body = match.group("body")
            announced_ids.extend(id_match.group("id") for id_match in RECENT_ARXIV_ID_PATTERN.finditer(body))

        return list(dict.fromkeys(announced_ids))

    def _iter_papers_by_ids(self, arxiv_ids: list[str]):
        for start in range(0, len(arxiv_ids), self.page_size):
            batch = arxiv_ids[start : start + self.page_size]
            if not batch:
                continue
            params = {
                "id_list": ",".join(batch),
                "start": 0,
                "max_results": len(batch),
            }
            response = self._get_feed_page(params=params)
            page = self.parse_atom_feed(response.text)
            papers_by_id = {paper.arxiv_id.split("v", maxsplit=1)[0]: paper for paper in page.papers}
            for arxiv_id in batch:
                paper = papers_by_id.get(arxiv_id)
                if paper is None:
                    continue
                if not paper.license_url:
                    fallback = self._fetch_license_from_abs(abs_url=paper.abs_url)
                    if fallback:
                        paper = replace(paper, license_url=fallback)
                yield paper

    def _iter_papers_by_abs_pages(self, arxiv_ids: list[str]):
        for arxiv_id in arxiv_ids:
            abs_url = f"https://arxiv.org/abs/{arxiv_id}"
            response = self.session.get(abs_url, timeout=self.request_timeout)
            response.raise_for_status()
            paper = self._paper_from_abs_html(arxiv_id=arxiv_id, html_text=response.text)
            if not paper.license_url:
                fallback = self._extract_license_from_abs_html(response.text)
                if fallback:
                    paper = replace(paper, license_url=fallback)
            yield paper
            # Keep fallback scraping polite without making weekly ingestion unreasonably slow.
            time.sleep(0.2)

    def _get_feed_page(self, *, params: dict[str, object]):
        last_exc: Exception | None = None
        for attempt in range(self.page_retry_attempts):
            try:
                response = self.session.get(ARXIV_API_URL, params=params, timeout=self.request_timeout)
                response.raise_for_status()
                body = response.text.lstrip()
                if body.startswith("Rate exceeded."):
                    raise RuntimeError("arXiv API rate limit exceeded")
                return response
            except (requests.RequestException, RuntimeError) as exc:
                last_exc = exc
                if attempt + 1 >= self.page_retry_attempts:
                    break
                if self.retry_sleep_seconds > 0:
                    time.sleep(self.retry_sleep_seconds * (attempt + 1))
        if last_exc is not None:
            raise last_exc
        raise RuntimeError("Failed to fetch arXiv feed page")

    def _paper_from_abs_html(self, *, arxiv_id: str, html_text: str) -> Paper:
        title = self._extract_meta_values(html_text, "citation_title")
        abstract = self._extract_meta_values(html_text, "citation_abstract")
        authors = self._extract_meta_values(html_text, "citation_author")
        citation_date = next(iter(self._extract_meta_values(html_text, "citation_date")), "")
        pdf_url = next(iter(self._extract_meta_values(html_text, "citation_pdf_url")), "")

        published_at = self._parse_citation_date(citation_date) if citation_date else datetime.utcnow()
        primary_category = self._extract_primary_category_from_abs_html(html_text)
        categories = [primary_category] if primary_category else []

        return Paper(
            arxiv_id=arxiv_id,
            title=title[0] if title else "",
            summary=abstract[0] if abstract else "",
            authors=authors,
            categories=categories,
            published_at=published_at,
            updated_at=published_at,
            abs_url=f"https://arxiv.org/abs/{arxiv_id}",
            pdf_url=pdf_url or f"https://arxiv.org/pdf/{arxiv_id}.pdf",
            source_url=f"https://arxiv.org/e-print/{arxiv_id}",
            primary_category=primary_category,
            license_url=self._extract_license_from_abs_html(html_text),
        )

    def _extract_meta_values(self, html_text: str, name: str) -> list[str]:
        values: list[str] = []
        name_lc = name.lower()
        for match in META_TAG_PATTERN.finditer(html_text):
            if match.group("name").lower() != name_lc:
                continue
            values.append(_normalize_ws(html.unescape(match.group("content"))))
        return [value for value in values if value]

    def _extract_primary_category_from_abs_html(self, html_text: str) -> str:
        match = PRIMARY_SUBJECT_CODE_PATTERN.search(html_text)
        if not match:
            return ""
        return _normalize_ws(html.unescape(match.group("code")))

    def _parse_citation_date(self, date_text: str) -> datetime:
        for fmt in ("%Y/%m/%d", "%Y-%m-%d"):
            try:
                return datetime.strptime(date_text, fmt)
            except ValueError:
                continue
        raise ValueError(f"Invalid citation date: {date_text}")

    def _is_rate_limit_error(self, exc: Exception) -> bool:
        if isinstance(exc, RuntimeError) and "rate limit" in str(exc).lower():
            return True
        if isinstance(exc, requests.HTTPError) and exc.response is not None:
            if exc.response.status_code == 429:
                return True
            body = exc.response.text.strip().lower()
            return body.startswith("rate exceeded")
        text = str(exc).lower()
        return "rate exceeded" in text or "429" in text

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
        primary_category = self._extract_primary_category(entry)
        doi = _normalize_ws(entry.findtext("arxiv:doi", default="", namespaces=ATOM_NS))
        journal_ref = _normalize_ws(entry.findtext("arxiv:journal_ref", default="", namespaces=ATOM_NS))
        comments = _normalize_ws(entry.findtext("arxiv:comment", default="", namespaces=ATOM_NS))

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
            primary_category=primary_category,
            doi=doi,
            journal_ref=journal_ref,
            comments=comments,
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

    def _extract_primary_category(self, entry: ET.Element) -> str:
        node = entry.find("arxiv:primary_category", namespaces=ATOM_NS)
        if node is None:
            return ""
        return str(node.attrib.get("term", "")).strip()

    def _fetch_license_from_abs(self, *, abs_url: str) -> str:
        try:
            response = self.session.get(abs_url, timeout=self.request_timeout)
            response.raise_for_status()
        except requests.RequestException:
            return ""
        return self._extract_license_from_abs_html(response.text)

    def _extract_license_from_abs_html(self, html_text: str) -> str:
        match = LICENSE_REL_PATTERN.search(html_text)
        if match:
            return html.unescape(match.group("href")).strip()

        url_match = LICENSE_URL_PATTERN.search(html_text)
        if url_match:
            return html.unescape(url_match.group(0)).strip()
        return ""


def _normalize_ws(text: str) -> str:
    return " ".join(text.split())


def _parse_timestamp(value: str) -> datetime:
    if not value:
        raise ValueError("Missing timestamp in arXiv feed entry")
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
