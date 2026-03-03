from __future__ import annotations

from io import BytesIO
import gzip
import posixpath
import re
import tarfile

import requests

from .models import LatexDocument


LATEX_EXTENSIONS = (".tex", ".ltx", ".latex")
INCLUDE_PATTERN = re.compile(r"\\(?:input|include)\s*\{(?P<target>[^{}]+)\}", flags=re.IGNORECASE)


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


def assemble_latex_documents(documents: list[LatexDocument]) -> list[LatexDocument]:
    if not documents:
        return []

    file_map: dict[str, str] = {}
    for document in documents:
        normalized = _normalize_path(document.filename)
        if normalized not in file_map:
            file_map[normalized] = document.content

    roots = _find_root_documents(file_map)
    assembled: list[LatexDocument] = []
    for root in roots:
        content = _resolve_includes(root, file_map=file_map, stack=[])
        assembled.append(LatexDocument(filename=root, content=content))
    return assembled


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


def _find_root_documents(file_map: dict[str, str]) -> list[str]:
    roots = []
    for filename, content in file_map.items():
        lowered = content.lower()
        if "\\documentclass" in lowered or "\\begin{document}" in lowered:
            roots.append(filename)
    if roots:
        return sorted(roots)
    return sorted(file_map.keys())


def _resolve_includes(document_path: str, *, file_map: dict[str, str], stack: list[str]) -> str:
    if document_path in stack:
        return f"\n% include cycle skipped: {document_path}\n"
    if len(stack) > 25:
        return f"\n% include depth limit reached at: {document_path}\n"

    source = file_map.get(document_path)
    if source is None:
        return f"\n% missing include file: {document_path}\n"

    current_dir = posixpath.dirname(document_path)

    def replace_match(match: re.Match[str]) -> str:
        target = match.group("target").strip()
        resolved = _resolve_target(target, current_dir=current_dir, file_map=file_map)
        if resolved is None:
            return f"\n% missing include target: {target}\n"
        return _resolve_includes(resolved, file_map=file_map, stack=stack + [document_path])

    return INCLUDE_PATTERN.sub(replace_match, source)


def _resolve_target(target: str, *, current_dir: str, file_map: dict[str, str]) -> str | None:
    base_target = _normalize_path(target)
    if not base_target:
        return None

    candidates: list[str] = []
    for base_dir in (current_dir, ""):
        joined = _normalize_path(posixpath.join(base_dir, base_target))
        candidates.append(joined)
        if not joined.lower().endswith(LATEX_EXTENSIONS):
            for ext in LATEX_EXTENSIONS:
                candidates.append(f"{joined}{ext}")

    seen: set[str] = set()
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        if candidate in file_map:
            return candidate

    base_name = posixpath.basename(base_target)
    unique = _resolve_by_unique_basename(base_name, file_map=file_map)
    if unique:
        return unique
    if not base_name.lower().endswith(LATEX_EXTENSIONS):
        for ext in LATEX_EXTENSIONS:
            unique = _resolve_by_unique_basename(f"{base_name}{ext}", file_map=file_map)
            if unique:
                return unique
    return None


def _resolve_by_unique_basename(base_name: str, *, file_map: dict[str, str]) -> str | None:
    matches = [name for name in file_map if posixpath.basename(name) == base_name]
    if len(matches) == 1:
        return matches[0]
    return None


def _normalize_path(value: str) -> str:
    normalized = value.replace("\\", "/").strip()
    normalized = posixpath.normpath(normalized)
    if normalized in {".", "/"}:
        return ""
    if normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized
