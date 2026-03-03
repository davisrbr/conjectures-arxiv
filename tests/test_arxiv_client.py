from datetime import date

from conjectures_arxiv.arxiv_client import ArxivClient, format_arxiv_date_range


SAMPLE_FEED = """<?xml version='1.0' encoding='UTF-8'?>
<feed xmlns='http://www.w3.org/2005/Atom'
      xmlns:opensearch='http://a9.com/-/spec/opensearch/1.1/'>
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
    <category term='math.AG' scheme='http://arxiv.org/schemas/atom'/>
    <link href='http://arxiv.org/abs/2603.00001v1' rel='alternate' type='text/html'/>
    <link title='pdf' href='http://arxiv.org/pdf/2603.00001v1' rel='related' type='application/pdf'/>
  </entry>
</feed>
"""


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
    assert paper.pdf_url == "http://arxiv.org/pdf/2603.00001v1"
    assert paper.source_url == "https://arxiv.org/e-print/2603.00001v1"
