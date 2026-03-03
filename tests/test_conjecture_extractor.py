from conjectures_arxiv.conjecture_extractor import extract_conjectures, extract_conjectures_from_documents, latex_to_plain_text
from conjectures_arxiv.models import LatexDocument


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


def test_extract_conjectures_from_newtheorem_custom_env() -> None:
    docs = [
        LatexDocument(filename="defs.tex", content=r"\newtheorem{mainconj}{Main Conjecture}"),
        LatexDocument(
            filename="main.tex",
            content=r"\begin{mainconj}Every object has a decomposition.\end{mainconj}",
        ),
    ]
    results = extract_conjectures_from_documents(docs)

    assert len(results) == 1
    assert "decomposition" in results[0].plain_text


def test_extract_conjectures_from_declaretheorem_custom_env() -> None:
    docs = [
        LatexDocument(filename="defs.tex", content=r"\declaretheorem[name=Conjecture]{bigclaim}"),
        LatexDocument(filename="main.tex", content=r"\begin{bigclaim}Statement\end{bigclaim}"),
    ]
    results = extract_conjectures_from_documents(docs)

    assert len(results) == 1
    assert results[0].plain_text == "Statement"


def test_extract_conjectures_ignores_commented_and_iffalse_blocks() -> None:
    text = r"""
%\begin{conjecture}
% Comment-only conjecture.
%\end{conjecture}
\iffalse
\begin{conjecture}
Inside iffalse should be ignored.
\end{conjecture}
\fi
\begin{conjecture}
This one is active.
\end{conjecture}
"""
    results = extract_conjectures(text, source_file="main.tex")
    assert len(results) == 1
    assert results[0].plain_text == "This one is active."
