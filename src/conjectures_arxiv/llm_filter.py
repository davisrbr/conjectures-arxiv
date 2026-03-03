from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import json
import posixpath
import re
import time
from typing import Any

from .database import Database
from .source_fetcher import SourceFetcher, assemble_latex_documents


SECTION_PATTERN = re.compile(r"\\(section|subsection|subsubsection)\*?\{(?P<title>[^{}]+)\}", flags=re.IGNORECASE)
ALLOWED_LABELS = {"real_open_conjecture", "not_real_conjecture", "uncertain"}
ASSESSMENT_VERSION = "gpt5mini-v2-interestingness-v1"


@dataclass(frozen=True)
class LLMClassification:
    label: str
    confidence: float
    interestingness_score: float
    interestingness_confidence: float
    interestingness_rationale: str
    assessment_version: str
    rationale: str
    evidence_snippet: str
    raw_response_json: str


@dataclass(frozen=True)
class LLMFilterRunSummary:
    total_candidates: int
    processed: int
    failures: int
    label_counts: dict[str, int]


class SourceContextProvider:
    def __init__(self, fetcher: SourceFetcher | None = None) -> None:
        self.fetcher = fetcher or SourceFetcher()
        self._cache: dict[str, dict[str, str]] = {}

    def get_context(self, record: dict[str, Any], *, window_lines: int = 12) -> str:
        arxiv_id = str(record["arxiv_id"])
        file_map = self._load_paper_sources(arxiv_id=arxiv_id, source_url=str(record["source_url"]))
        source_file = str(record["source_file"])
        selected = self._select_document(source_file=source_file, file_map=file_map)

        if selected is None:
            return ""

        text = file_map[selected]
        return self._extract_window(
            text=text,
            start_line=int(record["start_line"]),
            end_line=int(record["end_line"]),
            window_lines=window_lines,
        )

    def _load_paper_sources(self, *, arxiv_id: str, source_url: str) -> dict[str, str]:
        cached = self._cache.get(arxiv_id)
        if cached is not None:
            return cached

        documents = self.fetcher.fetch_documents(source_url)
        assembled = assemble_latex_documents(documents)
        chosen = assembled or documents

        file_map: dict[str, str] = {}
        for document in chosen:
            key = self._normalize_path(document.filename)
            if key and key not in file_map:
                file_map[key] = document.content

        self._cache[arxiv_id] = file_map
        return file_map

    def _select_document(self, *, source_file: str, file_map: dict[str, str]) -> str | None:
        normalized = self._normalize_path(source_file)
        if normalized in file_map:
            return normalized

        base_name = posixpath.basename(normalized)
        matches = [name for name in file_map if posixpath.basename(name) == base_name]
        if len(matches) == 1:
            return matches[0]
        return None

    def _extract_window(self, *, text: str, start_line: int, end_line: int, window_lines: int) -> str:
        lines = text.splitlines()
        if not lines:
            return ""

        lo = max(1, start_line - window_lines)
        hi = min(len(lines), end_line + window_lines)

        section = self._find_section_heading(lines=lines, line_no=start_line)
        window = "\n".join(f"{idx:4d}: {lines[idx - 1]}" for idx in range(lo, hi + 1))

        if section:
            return f"Section: {section}\n{window}"
        return window

    def _find_section_heading(self, *, lines: list[str], line_no: int) -> str:
        for idx in range(min(line_no - 1, len(lines) - 1), -1, -1):
            match = SECTION_PATTERN.search(lines[idx])
            if match:
                return match.group("title").strip()
        return ""

    @staticmethod
    def _normalize_path(value: str) -> str:
        cleaned = value.replace("\\", "/").strip()
        normalized = posixpath.normpath(cleaned)
        if normalized in {".", "/"}:
            return ""
        if normalized.startswith("./"):
            normalized = normalized[2:]
        return normalized


class GPT5MiniConjectureFilter:
    def __init__(self, *, model: str = "gpt-5-mini", client=None) -> None:
        self.model = model
        if client is not None:
            self.client = client
            return

        try:
            from openai import OpenAI  # type: ignore
        except ModuleNotFoundError as exc:
            raise RuntimeError("LLM filtering requires the openai package. Install with: pip install openai") from exc

        try:
            self.client = OpenAI()
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError(
                "LLM filtering requires OPENAI_API_KEY to be set in the environment."
            ) from exc

    def classify(self, *, record: dict[str, Any], context_window: str) -> LLMClassification:
        conjecture_id = int(record.get("conjecture_id", 0))
        if conjecture_id <= 0:
            conjecture_id = 1

        item = {
            "conjecture_id": conjecture_id,
            "record": record,
            "context_window": context_window,
        }
        results = self.classify_batch(items=[item])
        return results.get(conjecture_id, self._empty_uncertain())

    def classify_batch(self, *, items: list[dict[str, Any]]) -> dict[int, LLMClassification]:
        if not items:
            return {}

        output_text = self._request_model(
            system_prompt=self._label_system_prompt(),
            user_prompt=self._batch_user_prompt(items=items),
        )
        entries = self._entries_from_output_text(output_text)

        results: dict[int, LLMClassification] = {}
        for entry in entries:
            conjecture_id = self._parse_conjecture_id(entry)
            if conjecture_id is None:
                continue
            results[conjecture_id] = self._classification_from_payload(entry)

        # Recover from malformed batched output on a per-item basis.
        for item in items:
            conjecture_id = int(item["conjecture_id"])
            classification = results.get(conjecture_id)
            if classification is not None and not self._looks_like_parse_artifact(classification):
                continue

            recovered = self._classify_single_label_item(item=item)
            if recovered is None:
                results.pop(conjecture_id, None)
                continue
            results[conjecture_id] = recovered

        # Score interestingness only for real/open conjectures.
        for item in items:
            conjecture_id = int(item["conjecture_id"])
            classification = results.get(conjecture_id)
            if classification is None:
                continue
            if classification.label != "real_open_conjecture":
                results[conjecture_id] = self._without_interestingness(classification)
                continue

            scored = self._score_interestingness(item=item, base=classification)
            if scored is None:
                continue
            results[conjecture_id] = scored

        return results

    def _classify_single_label_item(self, *, item: dict[str, Any], max_attempts: int = 2) -> LLMClassification | None:
        conjecture_id = int(item["conjecture_id"])
        for _ in range(max_attempts):
            output_text = self._request_model(
                system_prompt=self._label_system_prompt(),
                user_prompt=self._single_user_prompt(item=item),
            )
            entries = self._entries_from_output_text(output_text)
            if not entries:
                continue

            entry = self._find_entry_for_id(entries=entries, conjecture_id=conjecture_id)
            if entry is None:
                continue

            classification = self._classification_from_payload(entry)
            if self._looks_like_parse_artifact(classification):
                continue
            return classification
        return None

    def _score_interestingness(self, *, item: dict[str, Any], base: LLMClassification, max_attempts: int = 2) -> LLMClassification | None:
        conjecture_id = int(item["conjecture_id"])
        for _ in range(max_attempts):
            output_text = self._request_model(
                system_prompt=self._interestingness_system_prompt(),
                user_prompt=self._interestingness_user_prompt(item=item),
            )
            entries = self._entries_from_output_text(output_text)
            if entries:
                payload = self._find_entry_for_id(entries=entries, conjecture_id=conjecture_id) or entries[0]
            else:
                parsed = self._parse_any_json(output_text)
                payload = parsed if isinstance(parsed, dict) else None

            if payload is None or not self._has_interestingness_payload(payload):
                continue

            score = self._clip_confidence(payload.get("interestingness_score", 0.0))
            confidence = self._clip_confidence(payload.get("interestingness_confidence", 0.0))
            rationale = str(payload.get("interestingness_rationale", "")).strip()[:600]
            raw_json = self._merge_raw_responses(
                label_raw=base.raw_response_json,
                interestingness_payload=payload,
            )
            return LLMClassification(
                label=base.label,
                confidence=base.confidence,
                interestingness_score=score,
                interestingness_confidence=confidence,
                interestingness_rationale=rationale,
                assessment_version=ASSESSMENT_VERSION,
                rationale=base.rationale,
                evidence_snippet=base.evidence_snippet,
                raw_response_json=raw_json,
            )
        return None

    def _request_model(self, *, system_prompt: str, user_prompt: str) -> str:
        response = self.client.responses.create(
            model=self.model,
            input=[
                {"role": "system", "content": [{"type": "input_text", "text": system_prompt}]},
                {"role": "user", "content": [{"type": "input_text", "text": user_prompt}]},
            ],
        )
        return self._extract_output_text(response)

    def _entries_from_output_text(self, output_text: str) -> list[dict[str, Any]]:
        parsed = self._parse_any_json(output_text)
        return self._entries_from_parsed(parsed)

    @staticmethod
    def _entries_from_parsed(parsed: Any) -> list[dict[str, Any]]:
        if isinstance(parsed, dict):
            if isinstance(parsed.get("results"), list):
                return [entry for entry in parsed["results"] if isinstance(entry, dict)]
            return [parsed]
        if isinstance(parsed, list):
            return [entry for entry in parsed if isinstance(entry, dict)]
        return []

    @staticmethod
    def _find_entry_for_id(*, entries: list[dict[str, Any]], conjecture_id: int) -> dict[str, Any] | None:
        for entry in entries:
            value = entry.get("conjecture_id", entry.get("id"))
            try:
                parsed = int(value)
            except (TypeError, ValueError):
                continue
            if parsed == conjecture_id:
                return entry
        if len(entries) == 1:
            return entries[0]
        return None

    @staticmethod
    def _extract_output_text(response: Any) -> str:
        if hasattr(response, "output_text") and isinstance(response.output_text, str):
            return response.output_text

        pieces: list[str] = []
        output = getattr(response, "output", None)
        if isinstance(output, list):
            for item in output:
                content = getattr(item, "content", None)
                if not isinstance(content, list):
                    continue
                for block in content:
                    text = getattr(block, "text", None)
                    if isinstance(text, str):
                        pieces.append(text)
        return "\n".join(pieces)

    @staticmethod
    def _parse_any_json(text: str) -> Any:
        text = text.strip()
        if not text:
            return {}

        try:
            return json.loads(text)
        except json.JSONDecodeError:
            pass

        code_block_match = re.search(r"```(?:json)?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
        if code_block_match is not None:
            code_block = code_block_match.group(1).strip()
            try:
                return json.loads(code_block)
            except json.JSONDecodeError:
                pass

        decoder = json.JSONDecoder()
        for match in re.finditer(r"[\[{]", text):
            start = match.start()
            try:
                parsed, _ = decoder.raw_decode(text[start:])
                return parsed
            except json.JSONDecodeError:
                continue
        return {}

    @staticmethod
    def _clip_confidence(value: Any) -> float:
        try:
            numeric = float(value)
        except (TypeError, ValueError):
            return 0.0
        return max(0.0, min(1.0, numeric))

    @staticmethod
    def _label_system_prompt() -> str:
        return (
            "You classify whether a LaTeX conjecture block is a real, currently-open conjecture in this paper. "
            "Respond with JSON only.\n\n"
            "Label definitions:\n"
            "- real_open_conjecture: an actively posed open conjecture in this work or immediate related literature context.\n"
            "- not_real_conjecture: inactive/commented statement, resolved/known/immediate-from-known theorem, or purely historical mention.\n"
            "- uncertain: insufficient context.\n\n"
            "Return JSON object with a top-level key 'results' that is a list.\n"
            "Each list item must have: conjecture_id, label, confidence (0..1), rationale, evidence_snippet.\n\n"
            "Keep rationale and evidence_snippet concise (max 40 words each). "
            "Do not include JSON inside rationale or evidence_snippet.\n\n"
            "Few-shot examples:\n"
            "Example 1 (not real): conjecture appears inside \\iffalse...\\fi or fully commented with % lines.\n"
            "Example 2 (not real): text says the conjecture follows immediately from Four Color Theorem.\n"
            "Example 3 (real): 'A minimally nonperfectly divisible graph contains no clique cutset.' presented as an open conjecture and investigated in paper."
        )

    @staticmethod
    def _interestingness_system_prompt() -> str:
        return (
            "You rate interestingness for conjectures already classified as currently-open. "
            "Respond with JSON only.\n\n"
            "Define interestingness_score (0..1) as likelihood the conjecture is meaningfully difficult/deep "
            "and likely important to specialists if solved.\n"
            "Define interestingness_confidence (0..1) as confidence in the estimate.\n"
            "interestingness_rationale should be concise (max 40 words) and grounded in provided local context.\n\n"
            "Do not output a label. Do not include nested JSON in text fields.\n"
            "Return one JSON object with keys: conjecture_id, interestingness_score, interestingness_confidence, interestingness_rationale."
        )

    @staticmethod
    def _batch_user_prompt(*, items: list[dict[str, Any]]) -> str:
        blocks: list[str] = []
        for item in items:
            record = item["record"]
            context_window = item["context_window"]
            blocks.append(
                (
                    f"### conjecture_id={item['conjecture_id']}\n"
                    f"arXiv ID: {record['arxiv_id']}\n"
                    f"Title: {record['title']}\n"
                    f"Authors: {', '.join(record.get('authors', []))}\n"
                    f"Abstract: {record['summary']}\n"
                    f"Source file: {record['source_file']}\n"
                    f"Line span: {record['start_line']}-{record['end_line']}\n\n"
                    f"Conjecture raw TeX:\n{record['raw_tex']}\n\n"
                    f"Conjecture body (normalized):\n{record['plain_text']}\n\n"
                    f"Local source context:\n{context_window}\n"
                )
            )
        return (
            "Classify each conjecture item below and return one JSON result per conjecture_id.\n\n"
            + "\n\n".join(blocks)
        )

    @staticmethod
    def _single_user_prompt(*, item: dict[str, Any]) -> str:
        record = item["record"]
        context_window = item["context_window"]
        return (
            "Classify this conjecture and return one JSON object with keys: "
            "conjecture_id, label, confidence, rationale, evidence_snippet.\n\n"
            "All fields are required. Use a 0..1 float for confidence.\n\n"
            f"conjecture_id={item['conjecture_id']}\n"
            f"arXiv ID: {record['arxiv_id']}\n"
            f"Title: {record['title']}\n"
            f"Authors: {', '.join(record.get('authors', []))}\n"
            f"Abstract: {record['summary']}\n"
            f"Source file: {record['source_file']}\n"
            f"Line span: {record['start_line']}-{record['end_line']}\n\n"
            f"Conjecture raw TeX:\n{record['raw_tex']}\n\n"
            f"Conjecture body (normalized):\n{record['plain_text']}\n\n"
            f"Local source context:\n{context_window}\n"
        )

    @staticmethod
    def _interestingness_user_prompt(*, item: dict[str, Any]) -> str:
        record = item["record"]
        context_window = item["context_window"]
        return (
            "Rate interestingness for this open conjecture and return one JSON object with keys: "
            "conjecture_id, interestingness_score, interestingness_confidence, interestingness_rationale.\n\n"
            f"conjecture_id={item['conjecture_id']}\n"
            f"arXiv ID: {record['arxiv_id']}\n"
            f"Title: {record['title']}\n"
            f"Authors: {', '.join(record.get('authors', []))}\n"
            f"Abstract: {record['summary']}\n"
            f"Source file: {record['source_file']}\n"
            f"Line span: {record['start_line']}-{record['end_line']}\n\n"
            f"Conjecture raw TeX:\n{record['raw_tex']}\n\n"
            f"Conjecture body (normalized):\n{record['plain_text']}\n\n"
            f"Local source context:\n{context_window}\n"
        )

    @staticmethod
    def _parse_conjecture_id(payload: dict[str, Any]) -> int | None:
        value = payload.get("conjecture_id", payload.get("id"))
        try:
            parsed = int(value)
        except (TypeError, ValueError):
            return None
        return parsed if parsed > 0 else None

    def _classification_from_payload(self, payload: dict[str, Any], *, _depth: int = 0) -> LLMClassification:
        label = str(payload.get("label", "uncertain")).strip()
        if label not in ALLOWED_LABELS:
            label = "uncertain"

        confidence = self._clip_confidence(payload.get("confidence", 0.0))
        interestingness_score = self._clip_confidence(payload.get("interestingness_score", 0.0))
        interestingness_confidence = self._clip_confidence(payload.get("interestingness_confidence", 0.0))
        interestingness_rationale = str(payload.get("interestingness_rationale", "")).strip()[:600]
        rationale = str(payload.get("rationale", "")).strip()[:600]
        evidence = str(payload.get("evidence_snippet", "")).strip()[:600]

        # Some malformed outputs serialize a nested JSON object into rationale.
        if _depth < 2 and self._looks_like_embedded_json(rationale):
            nested_payload = self._extract_nested_payload(rationale)
            if nested_payload is not None:
                nested = self._classification_from_payload(nested_payload, _depth=_depth + 1)
                if not self._looks_like_parse_artifact(nested):
                    return nested

        return LLMClassification(
            label=label,
            confidence=confidence,
            interestingness_score=interestingness_score,
            interestingness_confidence=interestingness_confidence,
            interestingness_rationale=interestingness_rationale,
            assessment_version=ASSESSMENT_VERSION,
            rationale=rationale,
            evidence_snippet=evidence,
            raw_response_json=json.dumps(payload, ensure_ascii=False),
        )

    @staticmethod
    def _has_interestingness_payload(payload: dict[str, Any]) -> bool:
        return any(
            key in payload
            for key in ("interestingness_score", "interestingness_confidence", "interestingness_rationale")
        )

    @staticmethod
    def _merge_raw_responses(*, label_raw: str, interestingness_payload: dict[str, Any]) -> str:
        try:
            label_payload: Any = json.loads(label_raw)
        except (TypeError, ValueError, json.JSONDecodeError):
            label_payload = label_raw
        return json.dumps(
            {
                "label_response": label_payload,
                "interestingness_response": interestingness_payload,
            },
            ensure_ascii=False,
        )

    @staticmethod
    def _empty_uncertain() -> LLMClassification:
        return LLMClassification(
            label="uncertain",
            confidence=0.0,
            interestingness_score=0.0,
            interestingness_confidence=0.0,
            interestingness_rationale="",
            assessment_version=ASSESSMENT_VERSION,
            rationale="No parsable model output.",
            evidence_snippet="",
            raw_response_json="{}",
        )

    @staticmethod
    def _without_interestingness(classification: LLMClassification) -> LLMClassification:
        return LLMClassification(
            label=classification.label,
            confidence=classification.confidence,
            interestingness_score=0.0,
            interestingness_confidence=0.0,
            interestingness_rationale="",
            assessment_version=ASSESSMENT_VERSION,
            rationale=classification.rationale,
            evidence_snippet=classification.evidence_snippet,
            raw_response_json=classification.raw_response_json,
        )

    @staticmethod
    def _looks_like_embedded_json(value: str) -> bool:
        stripped = value.strip()
        if not stripped:
            return False
        return stripped.startswith("{") or stripped.startswith("[")

    def _extract_nested_payload(self, text: str) -> dict[str, Any] | None:
        nested = self._parse_any_json(text)
        entries = self._entries_from_parsed(nested)
        if not entries:
            return None
        return entries[0]

    @staticmethod
    def _looks_like_parse_artifact(classification: LLMClassification) -> bool:
        if classification.label != "uncertain":
            return False
        if classification.confidence > 0.01:
            return False
        if classification.evidence_snippet.strip():
            return False
        rationale = classification.rationale.strip()
        if not rationale:
            return False
        if rationale.startswith("{") or rationale.startswith("["):
            return True
        return '"label"' in rationale and "conjecture_id" in rationale

class LLMFilterRunner:
    def __init__(
        self,
        *,
        db: Database,
        classifier: GPT5MiniConjectureFilter,
        context_provider: SourceContextProvider | None = None,
    ) -> None:
        self.db = db
        self.classifier = classifier
        self.context_provider = context_provider or SourceContextProvider()

    def run(
        self,
        *,
        model: str,
        limit: int | None = None,
        only_unlabeled: bool = True,
        context_window_lines: int = 20,
        batch_size: int = 1,
        sleep_seconds: float = 0.0,
    ) -> LLMFilterRunSummary:
        candidates = self.db.list_conjectures_for_llm(model=model, limit=limit, only_unlabeled=only_unlabeled)

        processed = 0
        failures = 0
        label_counts: Counter[str] = Counter()

        for chunk in _chunked(candidates, max(1, batch_size)):
            batch_items: list[dict[str, Any]] = []
            for candidate in chunk:
                try:
                    context_window = self.context_provider.get_context(candidate, window_lines=context_window_lines)
                    batch_items.append(
                        {
                            "conjecture_id": int(candidate["conjecture_id"]),
                            "record": candidate,
                            "context_window": context_window,
                        }
                    )
                except Exception:  # noqa: BLE001
                    failures += 1

            if not batch_items:
                continue

            try:
                batch_results = self.classifier.classify_batch(items=batch_items)
            except Exception:  # noqa: BLE001
                failures += len(batch_items)
                if sleep_seconds > 0:
                    time.sleep(sleep_seconds)
                continue

            for item in batch_items:
                conjecture_id = int(item["conjecture_id"])
                classification = batch_results.get(conjecture_id)
                if classification is None:
                    failures += 1
                    continue

                self.db.upsert_llm_label(
                    conjecture_id=conjecture_id,
                    model=model,
                    label=classification.label,
                    confidence=classification.confidence,
                    interestingness_score=classification.interestingness_score,
                    interestingness_confidence=classification.interestingness_confidence,
                    interestingness_rationale=classification.interestingness_rationale,
                    assessment_version=classification.assessment_version,
                    rationale=classification.rationale,
                    evidence_snippet=classification.evidence_snippet,
                    raw_response_json=classification.raw_response_json,
                )
                label_counts[classification.label] += 1
                processed += 1

            if sleep_seconds > 0:
                time.sleep(sleep_seconds)

        return LLMFilterRunSummary(
            total_candidates=len(candidates),
            processed=processed,
            failures=failures,
            label_counts=dict(label_counts),
        )


def _chunked(items: list[dict[str, Any]], size: int) -> list[list[dict[str, Any]]]:
    return [items[i : i + size] for i in range(0, len(items), size)]
