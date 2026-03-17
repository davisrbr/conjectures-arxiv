from datetime import date

import requests

from conjectures_arxiv.arxiv_client import ArxivClient, format_arxiv_date_range


SAMPLE_FEED = """<?xml version='1.0' encoding='UTF-8'?>
<feed xmlns='http://www.w3.org/2005/Atom'
      xmlns:opensearch='http://a9.com/-/spec/opensearch/1.1/'
      xmlns:arxiv='http://arxiv.org/schemas/atom'>
  <title>arXiv Query: search_query</title>
  <id>http://arxiv.org/api/abc</id>
  <updated>2026-03-03T12:00:00Z</updated>
  <opensearch:totalResults>1</opensearch:totalResults>
  <opensearch:startIndex>0</opensearch:startIndex>
  <opensearch:itemsPerPage>1</opensearch:itemsPerPage>
  <entry>
    <id>http://arxiv.org/abs/2603.00001v1</id>
    <updated>2026-03-02T20:00:00Z</updated>
    <published>2026-03-01T10:00:00Z</published>
    <title>  A Test Math Paper </title>
    <summary> Some summary text. </summary>
    <author><name>First Author</name></author>
    <author><name>Second Author</name></author>
    <arxiv:primary_category term='math.AG' scheme='http://arxiv.org/schemas/atom'/>
    <category term='math.AG' scheme='http://arxiv.org/schemas/atom'/>
    <arxiv:doi>10.1000/example-doi</arxiv:doi>
    <arxiv:journal_ref>J. Example Math. 10 (2026), 1-20</arxiv:journal_ref>
    <arxiv:comment>15 pages, 3 figures</arxiv:comment>
    <arxiv:license>http://creativecommons.org/licenses/by/4.0/</arxiv:license>
    <link href='http://arxiv.org/abs/2603.00001v1' rel='alternate' type='text/html'/>
    <link title='pdf' href='http://arxiv.org/pdf/2603.00001v1' rel='related' type='application/pdf'/>
  </entry>
</feed>
"""

SAMPLE_RECENT_LIST = """
<html>
  <body>
    <dl id='articles'>
      <h3>Tue, 17 Mar 2026 (showing 2 of 2 entries )</h3>
      <dt><a href="/abs/2603.15613">arXiv:2603.15613</a></dt>
      <dd>Paper 1</dd>
      <dt><a href="/abs/2603.15606">arXiv:2603.15606</a></dt>
      <dd>Paper 2</dd>
      <h3>Mon, 16 Mar 2026 (showing 1 of 1 entries )</h3>
      <dt><a href="/abs/2603.14000">arXiv:2603.14000</a></dt>
      <dd>Paper 3</dd>
    </dl>
  </body>
</html>
"""

SAMPLE_FEED_NO_LICENSE = SAMPLE_FEED.replace(
    "<arxiv:license>http://creativecommons.org/licenses/by/4.0/</arxiv:license>\n", ""
)
SAMPLE_ABS_HTML = """
<html>
  <body>
    <a rel="license" href="https://creativecommons.org/licenses/by/4.0/">License</a>
  </body>
</html>
"""


class _FakeResponse:
    def __init__(self, text: str) -> None:
        self.text = text

    def raise_for_status(self) -> None:
        return None


class _FakeSession:
    def __init__(self) -> None:
        self.headers = {}
        self.calls: list[tuple[str, dict | None]] = []

    def get(self, url, params=None, timeout=60):  # noqa: ANN001
        del timeout
        self.calls.append((url, params))
        if "api/query" in url:
            return _FakeResponse(SAMPLE_FEED_NO_LICENSE)
        if "list/math/pastweek" in url:
            return _FakeResponse(SAMPLE_RECENT_LIST)
        if "/abs/" in url:
            return _FakeResponse(SAMPLE_ABS_HTML)
        raise AssertionError(f"Unexpected URL: {url}")


class _RetrySession:
    def __init__(self) -> None:
        self.headers = {}
        self.calls = 0

    def get(self, url, params=None, timeout=60):  # noqa: ANN001
        del url, params, timeout
        self.calls += 1
        if self.calls == 1:
            raise requests.ReadTimeout("timed out")
        return _FakeResponse(SAMPLE_FEED)


class _RateLimitSession:
    def __init__(self) -> None:
        self.headers = {}
        self.calls = 0

    def get(self, url, params=None, timeout=60):  # noqa: ANN001
        del url, params, timeout
        self.calls += 1
        if self.calls == 1:
            return _FakeResponse("Rate exceeded.")
        return _FakeResponse(SAMPLE_FEED)


class _RecentListSession:
    def __init__(self) -> None:
        self.headers = {}
        self.calls: list[tuple[str, dict | None]] = []

    def get(self, url, params=None, timeout=60):  # noqa: ANN001
        del timeout
        self.calls.append((url, params))
        if "list/math/pastweek" in url:
            return _FakeResponse(SAMPLE_RECENT_LIST)
        if "api/query" in url and params and params.get("id_list") == "2603.15613,2603.15606":
            return _FakeResponse(
                SAMPLE_FEED.replace("2603.00001v1", "2603.15613v1")
                .replace("A Test Math Paper", "Recent Paper One")
                .replace("<opensearch:totalResults>1</opensearch:totalResults>", "<opensearch:totalResults>2</opensearch:totalResults>")
                .replace(
                    "</entry>\n</feed>",
                    """
  </entry>
  <entry>
    <id>http://arxiv.org/abs/2603.15606v1</id>
    <updated>2026-03-17T20:00:00Z</updated>
    <published>2026-03-17T20:00:00Z</published>
    <title>Recent Paper Two</title>
    <summary>Some summary text.</summary>
    <author><name>Third Author</name></author>
    <arxiv:primary_category term='math.AG' scheme='http://arxiv.org/schemas/atom'/>
    <category term='math.AG' scheme='http://arxiv.org/schemas/atom'/>
    <link href='http://arxiv.org/abs/2603.15606v1' rel='alternate' type='text/html'/>
    <link title='pdf' href='http://arxiv.org/pdf/2603.15606v1' rel='related' type='application/pdf'/>
  </entry>
</feed>
""",
                    )
                )
        if "/abs/" in url:
            return _FakeResponse(SAMPLE_ABS_HTML)
        raise AssertionError(f"Unexpected URL: {url} {params}")


def test_format_arxiv_date_range() -> None:
    assert format_arxiv_date_range(date(2026, 3, 1), date(2026, 3, 3)) == "[202603010000 TO 202603032359]"


def test_parse_atom_feed() -> None:
    client = ArxivClient()
    page = client.parse_atom_feed(SAMPLE_FEED)

    assert page.total_results == 1
    assert len(page.papers) == 1

    paper = page.papers[0]
    assert paper.arxiv_id == "2603.00001v1"
    assert paper.title == "A Test Math Paper"
    assert paper.summary == "Some summary text."
    assert paper.authors == ["First Author", "Second Author"]
    assert paper.categories == ["math.AG"]
    assert paper.primary_category == "math.AG"
    assert paper.doi == "10.1000/example-doi"
    assert paper.journal_ref == "J. Example Math. 10 (2026), 1-20"
    assert paper.comments == "15 pages, 3 figures"
    assert paper.pdf_url == "http://arxiv.org/pdf/2603.00001v1"
    assert paper.source_url == "https://arxiv.org/e-print/2603.00001v1"
    assert paper.license_url == "http://creativecommons.org/licenses/by/4.0/"


def test_iter_math_papers_falls_back_to_abs_license() -> None:
    session = _FakeSession()
    client = ArxivClient(session=session, page_size=1)
    papers = list(client.iter_math_papers(date(2026, 3, 1), date(2026, 3, 3), max_results=1))

    assert len(papers) == 1
    paper = papers[0]
    assert paper.license_url == "https://creativecommons.org/licenses/by/4.0/"
    assert any("/abs/2603.00001v1" in call[0] for call in session.calls)


def test_iter_math_papers_passes_start_offset() -> None:
    session = _FakeSession()
    client = ArxivClient(session=session, page_size=1)

    list(client.iter_math_papers(date(2026, 3, 1), date(2026, 3, 3), max_results=1, start_offset=400))

    api_calls = [call for call in session.calls if "api/query" in call[0]]
    assert api_calls[0][1]["start"] == 400


def test_iter_math_papers_retries_feed_fetch() -> None:
    session = _RetrySession()
    client = ArxivClient(session=session, page_size=1, page_retry_attempts=2, retry_sleep_seconds=0)

    papers = list(client.iter_math_papers(date(2026, 3, 1), date(2026, 3, 3), max_results=1))

    assert len(papers) == 1
    assert session.calls == 2


def test_iter_math_papers_retries_rate_limit_body() -> None:
    session = _RateLimitSession()
    client = ArxivClient(session=session, page_size=1, page_retry_attempts=2, retry_sleep_seconds=0)

    papers = list(client.iter_math_papers(date(2026, 3, 1), date(2026, 3, 3), max_results=1))

    assert len(papers) == 1
    assert session.calls == 2


def test_iter_math_papers_uses_recent_announcement_ids(monkeypatch) -> None:
    class _FakeDate(date):
        @classmethod
        def today(cls):  # noqa: N805
            return cls(2026, 3, 17)

    monkeypatch.setattr("conjectures_arxiv.arxiv_client.date", _FakeDate)
    session = _RecentListSession()
    client = ArxivClient(session=session, page_size=10)

    papers = list(client.iter_math_papers(_FakeDate(2026, 3, 17), _FakeDate(2026, 3, 17)))

    assert [paper.arxiv_id for paper in papers] == ["2603.15613v1", "2603.15606v1"]
    api_calls = [call for call in session.calls if "api/query" in call[0]]
    assert len(api_calls) == 1
    assert api_calls[0][1]["id_list"] == "2603.15613,2603.15606"
