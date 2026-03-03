from datetime import date

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
        self.calls: list[str] = []

    def get(self, url, params=None, timeout=60):  # noqa: ANN001
        del params, timeout
        self.calls.append(url)
        if "api/query" in url:
            return _FakeResponse(SAMPLE_FEED_NO_LICENSE)
        if "/abs/" in url:
            return _FakeResponse(SAMPLE_ABS_HTML)
        raise AssertionError(f"Unexpected URL: {url}")


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
    assert any("/abs/2603.00001v1" in call for call in session.calls)
