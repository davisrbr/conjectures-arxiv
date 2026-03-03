from conjectures_arxiv.conjecture_extractor import extract_conjectures, latex_to_plain_text


def test_extract_conjectures_finds_multiple_blocks() -> None:
    text = """
intro
\\begin{conjecture}
If $n$ is prime, then something holds.
\\end{conjecture}
middle
\\begin{conjecture*}
Second statement with \\emph{formatting}.
\\end{conjecture*}
outro
"""
    results = extract_conjectures(text, source_file="main.tex")

    assert len(results) == 2
    assert results[0].index_in_file == 1
    assert results[0].source_file == "main.tex"
    assert "prime" in results[0].plain_text
    assert results[1].index_in_file == 2
    assert "formatting" in results[1].plain_text
    assert results[0].start_line < results[0].end_line


def test_latex_to_plain_text_strips_common_commands() -> None:
    text = r"A \emph{bold} claim with \cite{abc} and \label{c1}."
    plain = latex_to_plain_text(text)
    assert plain == "A bold claim with and ."
