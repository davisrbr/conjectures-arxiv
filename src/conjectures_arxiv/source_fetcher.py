from __future__ import annotations

from io import BytesIO
import gzip
import tarfile

import requests

from .models import LatexDocument


LATEX_EXTENSIONS = (".tex", ".ltx", ".latex")


class SourceFetcher:
    def __init__(self, session: requests.Session | None = None, timeout: int = 120) -> None:
        self.session = session or requests.Session()
        self.timeout = timeout
        self.session.headers.setdefault("User-Agent", "conjectures-arxiv/0.1.0")

    def fetch_documents(self, source_url: str) -> list[LatexDocument]:
        response = self.session.get(source_url, timeout=self.timeout)
        response.raise_for_status()
        return extract_latex_documents(response.content)


def extract_latex_documents(payload: bytes) -> list[LatexDocument]:
    docs = _extract_from_tar(payload)
    if docs:
        return docs

    unzipped = _gunzip_if_needed(payload)
    if unzipped is not None:
        docs = _extract_from_tar(unzipped)
        if docs:
            return docs
        text = _decode_bytes(unzipped)
        if _looks_like_latex(text):
            return [LatexDocument(filename="source.tex", content=text)]

    text = _decode_bytes(payload)
    if _looks_like_latex(text):
        return [LatexDocument(filename="source.tex", content=text)]

    return []


def _extract_from_tar(payload: bytes) -> list[LatexDocument]:
    docs: list[LatexDocument] = []
    try:
        with tarfile.open(fileobj=BytesIO(payload), mode="r:*") as archive:
            for member in archive.getmembers():
                if not member.isfile() or not member.name.lower().endswith(LATEX_EXTENSIONS):
                    continue
                extracted = archive.extractfile(member)
                if extracted is None:
                    continue
                data = extracted.read()
                content = _decode_bytes(data)
                docs.append(LatexDocument(filename=member.name, content=content))
    except tarfile.ReadError:
        return []
    return docs


def _gunzip_if_needed(payload: bytes) -> bytes | None:
    try:
        return gzip.decompress(payload)
    except OSError:
        return None


def _decode_bytes(payload: bytes) -> str:
    for encoding in ("utf-8", "latin-1", "cp1252"):
        try:
            return payload.decode(encoding)
        except UnicodeDecodeError:
            continue
    return payload.decode("utf-8", errors="replace")


def _looks_like_latex(text: str) -> bool:
    lowered = text.lower()
    return "\\begin{" in lowered or "\\documentclass" in lowered
