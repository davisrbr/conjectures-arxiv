from __future__ import annotations

from dataclasses import dataclass
import hashlib
import re

from .models import LatexDocument


CONJECTURE_PATTERN = re.compile(
    r"\\begin\{(?P<env>conjecture\*?)\}(?P<body>.*?)\\end\{(?P=env)\}",
    flags=re.IGNORECASE | re.DOTALL,
)


@dataclass(frozen=True)
class ExtractedConjecture:
    source_file: str
    index_in_file: int
    start_line: int
    end_line: int
    raw_tex: str
    body_tex: str
    plain_text: str
    content_hash: str


def extract_conjectures_from_documents(documents: list[LatexDocument]) -> list[ExtractedConjecture]:
    matches: list[ExtractedConjecture] = []
    for document in documents:
        matches.extend(extract_conjectures(document.content, source_file=document.filename))
    return matches


def extract_conjectures(text: str, source_file: str) -> list[ExtractedConjecture]:
    extracted: list[ExtractedConjecture] = []
    for index, match in enumerate(CONJECTURE_PATTERN.finditer(text), start=1):
        raw = match.group(0).strip()
        body = match.group("body").strip()
        plain = latex_to_plain_text(body)

        start_line = text.count("\n", 0, match.start()) + 1
        end_line = text.count("\n", 0, match.end()) + 1
        content_hash = hashlib.sha256(raw.encode("utf-8")).hexdigest()

        extracted.append(
            ExtractedConjecture(
                source_file=source_file,
                index_in_file=index,
                start_line=start_line,
                end_line=end_line,
                raw_tex=raw,
                body_tex=body,
                plain_text=plain,
                content_hash=content_hash,
            )
        )
    return extracted


def latex_to_plain_text(text: str) -> str:
    no_comments = re.sub(r"(?<!\\)%.*", "", text)
    no_labels = re.sub(r"\\(label|ref|eqref|cite|url|footnote)\*?(\[[^\]]*\])?\{[^{}]*\}", "", no_comments)

    # Keep common formatting-command bodies while dropping command names.
    keep_body_commands = re.sub(r"\\[a-zA-Z]+\*?\{([^{}]*)\}", r"\1", no_labels)
    no_remaining_commands = re.sub(r"\\[a-zA-Z]+\*?(\[[^\]]*\])?", "", keep_body_commands)
    no_braces = no_remaining_commands.replace("{", " ").replace("}", " ")

    normalized = " ".join(no_braces.split())
    return normalized
