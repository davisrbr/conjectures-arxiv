from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime


@dataclass(frozen=True)
class Paper:
    arxiv_id: str
    title: str
    summary: str
    authors: list[str]
    categories: list[str]
    published_at: datetime
    updated_at: datetime
    abs_url: str
    pdf_url: str
    source_url: str


@dataclass(frozen=True)
class LatexDocument:
    filename: str
    content: str
