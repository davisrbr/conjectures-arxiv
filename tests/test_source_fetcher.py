from __future__ import annotations

import gzip
from io import BytesIO
import tarfile

from conjectures_arxiv.source_fetcher import extract_latex_documents


def _build_tar(files: dict[str, bytes]) -> bytes:
    stream = BytesIO()
    with tarfile.open(fileobj=stream, mode="w:gz") as archive:
        for name, payload in files.items():
            info = tarfile.TarInfo(name=name)
            info.size = len(payload)
            archive.addfile(info, BytesIO(payload))
    return stream.getvalue()


def test_extract_latex_documents_from_tar() -> None:
    payload = _build_tar(
        {
            "paper/main.tex": b"\\documentclass{article}\\begin{document}x\\end{document}",
            "paper/readme.txt": b"ignore me",
        }
    )
    docs = extract_latex_documents(payload)

    assert len(docs) == 1
    assert docs[0].filename == "paper/main.tex"
    assert "\\documentclass" in docs[0].content


def test_extract_latex_documents_from_gzip_plain_tex() -> None:
    tex = b"\\begin{conjecture}A\\end{conjecture}"
    payload = gzip.compress(tex)
    docs = extract_latex_documents(payload)

    assert len(docs) == 1
    assert docs[0].filename == "source.tex"
    assert "\\begin{conjecture}" in docs[0].content


def test_extract_latex_documents_from_plain_tex() -> None:
    payload = b"\\documentclass{article}\\begin{document}Body\\end{document}"
    docs = extract_latex_documents(payload)

    assert len(docs) == 1
    assert docs[0].filename == "source.tex"
