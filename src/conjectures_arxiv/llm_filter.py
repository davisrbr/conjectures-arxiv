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
ASSESSMENT_VERSION = "gpt5mini-v5-open-exact-v1"


@dataclass(frozen=True)
class LLMClassification:
    label: str
    confidence: float
    interestingness_score: float
    interestingness_confidence: float
    interestingness_rationale: str
    viability_score: float
    viability_confidence: float
    viability_rationale: str
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

        # Score interestingness/viability only for real/open conjectures.
        open_items: list[dict[str, Any]] = []
        for item in items:
            conjecture_id = int(item["conjecture_id"])
            classification = results.get(conjecture_id)
            if classification is None:
                continue
            if classification.label != "real_open_conjecture":
                results[conjecture_id] = self._without_interestingness(classification)
                continue
            open_items.append(item)

        if not open_items:
            return results

        interestingness_updates = self._score_interestingness_batch(items=open_items, results=results)
        for conjecture_id, classification in interestingness_updates.items():
            results[conjecture_id] = classification

        viability_updates = self._score_viability_batch(items=open_items, results=results)
        for conjecture_id, classification in viability_updates.items():
            results[conjecture_id] = classification

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
                viability_score=base.viability_score,
                viability_confidence=base.viability_confidence,
                viability_rationale=base.viability_rationale,
                assessment_version=ASSESSMENT_VERSION,
                rationale=base.rationale,
                evidence_snippet=base.evidence_snippet,
                raw_response_json=raw_json,
            )
        return None

    def _score_interestingness_batch(
        self,
        *,
        items: list[dict[str, Any]],
        results: dict[int, LLMClassification],
        max_attempts: int = 2,
    ) -> dict[int, LLMClassification]:
        updates: dict[int, LLMClassification] = {}
        if not items:
            return updates

        for _ in range(max_attempts):
            output_text = self._request_model(
                system_prompt=self._interestingness_system_prompt(),
                user_prompt=self._interestingness_batch_user_prompt(items=items),
            )
            entries = self._entries_from_output_text(output_text)
            if not entries:
                continue

            for item in items:
                conjecture_id = int(item["conjecture_id"])
                base = results.get(conjecture_id)
                if base is None or base.label != "real_open_conjecture":
                    continue
                payload = self._find_entry_for_id_strict(entries=entries, conjecture_id=conjecture_id)
                if payload is None or not self._has_interestingness_payload(payload):
                    continue

                score = self._clip_confidence(payload.get("interestingness_score", 0.0))
                confidence = self._clip_confidence(payload.get("interestingness_confidence", 0.0))
                rationale = str(payload.get("interestingness_rationale", "")).strip()[:600]
                raw_json = self._merge_raw_responses(
                    label_raw=base.raw_response_json,
                    interestingness_payload=payload,
                )
                updates[conjecture_id] = LLMClassification(
                    label=base.label,
                    confidence=base.confidence,
                    interestingness_score=score,
                    interestingness_confidence=confidence,
                    interestingness_rationale=rationale,
                    viability_score=base.viability_score,
                    viability_confidence=base.viability_confidence,
                    viability_rationale=base.viability_rationale,
                    assessment_version=ASSESSMENT_VERSION,
                    rationale=base.rationale,
                    evidence_snippet=base.evidence_snippet,
                    raw_response_json=raw_json,
                )

            if len(updates) == len(items):
                return updates

        for item in items:
            conjecture_id = int(item["conjecture_id"])
            if conjecture_id in updates:
                continue
            base = results.get(conjecture_id)
            if base is None or base.label != "real_open_conjecture":
                continue
            scored = self._score_interestingness(item=item, base=base)
            if scored is not None:
                updates[conjecture_id] = scored

        return updates

    def _score_viability(self, *, item: dict[str, Any], base: LLMClassification, max_attempts: int = 2) -> LLMClassification | None:
        conjecture_id = int(item["conjecture_id"])
        for _ in range(max_attempts):
            output_text = self._request_model(
                system_prompt=self._viability_system_prompt(),
                user_prompt=self._viability_user_prompt(item=item),
            )
            entries = self._entries_from_output_text(output_text)
            if entries:
                payload = self._find_entry_for_id(entries=entries, conjecture_id=conjecture_id) or entries[0]
            else:
                parsed = self._parse_any_json(output_text)
                payload = parsed if isinstance(parsed, dict) else None

            if payload is None or not self._has_viability_payload(payload):
                continue

            score = self._clip_confidence(payload.get("viability_score", 0.0))
            confidence = self._clip_confidence(payload.get("viability_confidence", 0.0))
            rationale = str(payload.get("viability_rationale", "")).strip()[:600]
            raw_json = self._merge_raw_responses(
                label_raw=base.raw_response_json,
                viability_payload=payload,
            )
            return LLMClassification(
                label=base.label,
                confidence=base.confidence,
                interestingness_score=base.interestingness_score,
                interestingness_confidence=base.interestingness_confidence,
                interestingness_rationale=base.interestingness_rationale,
                viability_score=score,
                viability_confidence=confidence,
                viability_rationale=rationale,
                assessment_version=ASSESSMENT_VERSION,
                rationale=base.rationale,
                evidence_snippet=base.evidence_snippet,
                raw_response_json=raw_json,
            )
        return None

    def _score_viability_batch(
        self,
        *,
        items: list[dict[str, Any]],
        results: dict[int, LLMClassification],
        max_attempts: int = 2,
    ) -> dict[int, LLMClassification]:
        updates: dict[int, LLMClassification] = {}
        if not items:
            return updates

        for _ in range(max_attempts):
            output_text = self._request_model(
                system_prompt=self._viability_system_prompt(),
                user_prompt=self._viability_batch_user_prompt(items=items),
            )
            entries = self._entries_from_output_text(output_text)
            if not entries:
                continue

            for item in items:
                conjecture_id = int(item["conjecture_id"])
                base = results.get(conjecture_id)
                if base is None or base.label != "real_open_conjecture":
                    continue
                payload = self._find_entry_for_id_strict(entries=entries, conjecture_id=conjecture_id)
                if payload is None or not self._has_viability_payload(payload):
                    continue

                score = self._clip_confidence(payload.get("viability_score", 0.0))
                confidence = self._clip_confidence(payload.get("viability_confidence", 0.0))
                rationale = str(payload.get("viability_rationale", "")).strip()[:600]
                raw_json = self._merge_raw_responses(
                    label_raw=base.raw_response_json,
                    viability_payload=payload,
                )
                updates[conjecture_id] = LLMClassification(
                    label=base.label,
                    confidence=base.confidence,
                    interestingness_score=base.interestingness_score,
                    interestingness_confidence=base.interestingness_confidence,
                    interestingness_rationale=base.interestingness_rationale,
                    viability_score=score,
                    viability_confidence=confidence,
                    viability_rationale=rationale,
                    assessment_version=ASSESSMENT_VERSION,
                    rationale=base.rationale,
                    evidence_snippet=base.evidence_snippet,
                    raw_response_json=raw_json,
                )

            if len(updates) == len(items):
                return updates

        for item in items:
            conjecture_id = int(item["conjecture_id"])
            if conjecture_id in updates:
                continue
            base = results.get(conjecture_id)
            if base is None or base.label != "real_open_conjecture":
                continue
            scored = self._score_viability(item=item, base=base)
            if scored is not None:
                updates[conjecture_id] = scored

        return updates

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
    def _find_entry_for_id_strict(*, entries: list[dict[str, Any]], conjecture_id: int) -> dict[str, Any] | None:
        for entry in entries:
            value = entry.get("conjecture_id", entry.get("id"))
            try:
                parsed = int(value)
            except (TypeError, ValueError):
                continue
            if parsed == conjecture_id:
                return entry
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
            "You classify whether the exact extracted LaTeX conjecture statement is still a real, currently-open conjecture "
            "after accounting for results and context in this paper. "
            "Respond with JSON only.\n\n"
            "Label definitions:\n"
            "- real_open_conjecture: the exact extracted statement remains unresolved as written and is being posed as an active open target.\n"
            "- not_real_conjecture: the exact extracted statement is already proved/refuted/known, is just a solved special case of a broader parent conjecture, "
            "is only background motivation or survey context, is inactive/commented/empty, or follows immediately from known results.\n"
            "- uncertain: insufficient context.\n\n"
            "Decision rules:\n"
            "- Judge the exact extracted statement, not a broader parent conjecture.\n"
            "- If the paper proves the extracted statement, disproves it, or gives a counterexample, label not_real_conjecture.\n"
            "- If the paper proves a special case (for example k=4) of a broader open conjecture, then that extracted special-case statement is not_real_conjecture even if the parent conjecture remains open.\n"
            "- If the extracted statement is only cited as famous background motivation (for example Hodge/abc/Schanuel) and is not the paper's own still-open target, label not_real_conjecture.\n"
            "- If the paper proves only an analogue, reduction, or nearby variant, keep real_open_conjecture only when the exact extracted statement itself still appears unresolved.\n\n"
            "Return JSON object with a top-level key 'results' that is a list.\n"
            "Each list item must have: conjecture_id, label, confidence (0..1), rationale, evidence_snippet.\n\n"
            "Keep rationale and evidence_snippet concise (max 40 words each). "
            "Do not include JSON inside rationale or evidence_snippet.\n\n"
            "Few-shot examples:\n"
            "Example 1 (not real): conjecture appears inside \\iffalse...\\fi or fully commented with % lines.\n"
            "Example 2 (not real): text says the conjecture follows immediately from Four Color Theorem.\n"
            "Example 3 (not real): extracted statement is the k=4 case of a broader k-uniform conjecture, and the paper proves the k=4 case.\n"
            "Example 4 (not real): paper states a famous classical conjecture only as background motivation before proving a related theorem.\n"
            "Example 5 (real): 'A minimally nonperfectly divisible graph contains no clique cutset.' presented as an open conjecture and investigated in paper."
        )

    @staticmethod
    def _interestingness_system_prompt() -> str:
        return (
            "You rate interestingness for exact still-open conjectures drawn from recent arXiv math papers. "
            "Respond with JSON only.\n\n"
            "Define interestingness_score (0..1) as a blend of mathematical depth and broader significance if solved. "
            "Do not score high merely because a statement is open, technical, numerically supported, or important only to the current paper.\n"
            "Define interestingness_confidence (0..1) as confidence in the estimate.\n"
            "interestingness_rationale should be concise (max 40 words) and grounded in provided local context.\n\n"
            "Calibration anchors:\n"
            "- 0.05-0.25: typo-like, self-referential, or mathematically slight statement.\n"
            "- 0.25-0.45: narrow local technical extension, finite-case completion, or table-filling conjecture.\n"
            "- 0.45-0.65: meaningful specialist conjecture with genuine content but limited scope.\n"
            "- 0.65-0.82: central active problem within a subfield, or a conjecture with clear structural consequences.\n"
            "- 0.82-0.93: major field-level conjecture or an unusually deep bridge between areas.\n"
            "- 0.93-0.99: only for landmark flagship problems with very broad consequences.\n\n"
            "Penalty rules:\n"
            "- Finite-family classifications, local strengthenings, and numerically motivated pattern guesses usually belong at 0.60 or below unless the text shows broad consequences.\n"
            "- If a background flagship conjecture slips through despite the earlier filter, do not automatically assign 0.95+ unless the paper is genuinely centered on resolving it.\n\n"
            "Do not output a label. Do not include nested JSON in text fields.\n"
            "Return one JSON object with keys: conjecture_id, interestingness_score, interestingness_confidence, interestingness_rationale."
        )

    @staticmethod
    def _viability_system_prompt() -> str:
        return (
            "Your job is to scout for the viability of math conjectures.\n"
            "Interestingness is scored separately in another step; this step should only estimate viability.\n\n"
            "You must rely on the text provided plus general mathematical background knowledge. "
            "Do not assume you can look anything up.\n\n"
            "Viability scoring target:\n"
            "- viability_score (0..1): likelihood the exact extracted statement (or a major decisive breakthrough on it) is resolved "
            "in roughly the next 5 years.\n"
            "- viability_confidence (0..1): confidence in the viability estimate (not confidence the conjecture is true).\n\n"
            "Critical distinction:\n"
            "- Do not confuse likely true with likely solved.\n"
            "- Numerics, computer experiments, verification for many cases, asymptotic/large-parameter results, or a proof for sufficiently large n/p/q are weak evidence about 5-year solvability of the full statement.\n"
            "- Strong evidence that the statement is true should not by itself push viability high.\n"
            "- If the provided context suggests the exact extracted statement is already proved/refuted in this paper or is only background motivation, set viability very low (about 0.00-0.05) rather than rewarding it.\n\n"
            "Scoring heuristics for viability (priority):\n"
            "1) Classic named grand conjecture penalty: for famous decades-old flagship problems (e.g., Hodge/abc/Schanuel/Kakeya/major prime-gap statements), "
            "set viability very low unless local text strongly indicates imminent resolution.\n"
            "2) Age/provenance cues: old-year tags, 'open for decades', 'wide open', or 'no approach known' lower viability.\n"
            "3) Local progress cues raise viability only when they shrink the remaining gap in a concrete way: reductions to a few lemmas, finite explicit residue cases, or direct closure of an existing method.\n"
            "4) Asymptotic results, many settled special cases, or strong numerics are only modest positive evidence unless the remaining gap is explicitly finite and mechanically checkable.\n"
            "5) Scope penalties: highly quantified maximally general formulations lower viability; fixed low-dimensional/family-specific targets raise viability.\n"
            "6) 'Only small cases remain' is not enough for very high viability unless the snippet gives a credible explicit route for finishing those cases.\n"
            "7) Field-typical difficulty as tie-breaker only when local cues are weak.\n"
            "8) Title/author cues are weak secondary nudges only.\n\n"
            "Calibration anchors:\n"
            "- 0.00-0.05: already appears solved/refuted here, or classic decades-old grand conjecture with no imminent route.\n"
            "- 0.01-0.05: iconic decades-old grand conjecture or equivalent.\n"
            "- 0.05-0.15: very hard broad long-studied problem, no strong local progress cues.\n"
            "- 0.15-0.35: active area with partial results but still broad/hard, or asymptotic/numerical progress without a concrete closing route.\n"
            "- 0.35-0.60: plausible near-frontier step with strong partial progress and a reasonably concrete path.\n"
            "- 0.60-0.85: appears close because the remaining gap is explicit and technically concentrated.\n"
            "- 0.85-0.95: only if snippet indicates essentially solved modulo routine closure.\n\n"
            "When uncertain, prefer mid viability (0.20-0.40) with lower viability_confidence.\n\n"
            "Output rules:\n"
            "- Respond with JSON only.\n"
            "- Return exactly one JSON object with keys: conjecture_id, viability_score, viability_confidence, viability_rationale.\n"
            "- viability_rationale must be concise (max 40 words), plain text, and grounded in provided cues.\n"
            "- Do not include nested JSON or extra keys."
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
    def _interestingness_batch_user_prompt(*, items: list[dict[str, Any]]) -> str:
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
            "Rate interestingness for each open conjecture below and return one JSON result per conjecture_id.\n\n"
            + "\n\n".join(blocks)
        )

    @staticmethod
    def _viability_user_prompt(*, item: dict[str, Any]) -> str:
        record = item["record"]
        context_window = item["context_window"]
        return (
            "Rate near-term viability for this open conjecture.\n\n"
            f"conjecture_id={item['conjecture_id']}\n"
            f"TITLE: {record['title']}\n"
            f"AUTHORS: {', '.join(record.get('authors', []))}\n"
            f"ABSTRACT: {record['summary']}\n"
            f"SOURCE_FILE: {record['source_file']}\n"
            f"LINE_SPAN: {record['start_line']}-{record['end_line']}\n\n"
            f"CONJECTURE_RAW_TEX:\n{record['raw_tex']}\n\n"
            f"CONJECTURE_BODY:\n{record['plain_text']}\n\n"
            "LOCAL_SOURCE_CONTEXT:\n"
            f"{context_window}\n"
        )

    @staticmethod
    def _viability_batch_user_prompt(*, items: list[dict[str, Any]]) -> str:
        blocks: list[str] = []
        for item in items:
            record = item["record"]
            context_window = item["context_window"]
            blocks.append(
                (
                    f"### conjecture_id={item['conjecture_id']}\n"
                    f"TITLE: {record['title']}\n"
                    f"AUTHORS: {', '.join(record.get('authors', []))}\n"
                    f"ABSTRACT: {record['summary']}\n"
                    f"SOURCE_FILE: {record['source_file']}\n"
                    f"LINE_SPAN: {record['start_line']}-{record['end_line']}\n\n"
                    f"CONJECTURE_RAW_TEX:\n{record['raw_tex']}\n\n"
                    f"CONJECTURE_BODY:\n{record['plain_text']}\n\n"
                    f"LOCAL_SOURCE_CONTEXT:\n{context_window}\n"
                )
            )
        return (
            "Rate near-term viability for each open conjecture below and return one JSON result per conjecture_id.\n\n"
            + "\n\n".join(blocks)
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
        viability_score = self._clip_confidence(payload.get("viability_score", 0.0))
        viability_confidence = self._clip_confidence(payload.get("viability_confidence", 0.0))
        viability_rationale = str(payload.get("viability_rationale", "")).strip()[:600]
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
            viability_score=viability_score,
            viability_confidence=viability_confidence,
            viability_rationale=viability_rationale,
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
    def _has_viability_payload(payload: dict[str, Any]) -> bool:
        return any(
            key in payload
            for key in ("viability_score", "viability_confidence", "viability_rationale")
        )

    @staticmethod
    def _merge_raw_responses(
        *,
        label_raw: str,
        interestingness_payload: dict[str, Any] | None = None,
        viability_payload: dict[str, Any] | None = None,
    ) -> str:
        try:
            label_payload: Any = json.loads(label_raw)
        except (TypeError, ValueError, json.JSONDecodeError):
            label_payload = label_raw
        payload: dict[str, Any] = {"label_response": label_payload}
        if interestingness_payload is not None:
            payload["interestingness_response"] = interestingness_payload
        if viability_payload is not None:
            payload["viability_response"] = viability_payload
        return json.dumps(payload, ensure_ascii=False)

    @staticmethod
    def _empty_uncertain() -> LLMClassification:
        return LLMClassification(
            label="uncertain",
            confidence=0.0,
            interestingness_score=0.0,
            interestingness_confidence=0.0,
            interestingness_rationale="",
            viability_score=0.0,
            viability_confidence=0.0,
            viability_rationale="",
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
            viability_score=0.0,
            viability_confidence=0.0,
            viability_rationale="",
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
                    viability_score=classification.viability_score,
                    viability_confidence=classification.viability_confidence,
                    viability_rationale=classification.viability_rationale,
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
