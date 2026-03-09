from __future__ import annotations

from dataclasses import dataclass
import hashlib
import re

from .models import LatexDocument


DEFAULT_ENVIRONMENTS = {"conjecture"}
NEWTHEOREM_PATTERN = re.compile(
    r"\\newtheorem\*?\s*(?:\[[^\]]*\]\s*)?\{(?P<env>[^{}]+)\}\s*(?:\[[^\]]*\]\s*)?\{(?P<title>[^{}]+)\}",
    flags=re.IGNORECASE,
)
DECLARETHEOREM_PATTERN = re.compile(
    r"\\declaretheorem\s*(?:\[(?P<options>[^\]]*)\])?\s*\{(?P<env>[^{}]+)\}",
    flags=re.IGNORECASE,
)
NAME_OPTION_PATTERN = re.compile(
    r"name\s*=\s*(?:\{(?P<braced>[^{}]*)\}|(?P<plain>[^,\]]+))",
    flags=re.IGNORECASE,
)
IFFALSE_TOKEN_PATTERN = re.compile(r"\\if(?:false|0)\b|\\fi\b", flags=re.IGNORECASE)
STYLE_COMMAND_PATTERN = re.compile(r"\\color\*?(\[[^\]]*\])?\{[^{}]*\}", flags=re.IGNORECASE)
LIST_ENV_PATTERN = re.compile(r"\\(?:begin|end)\{(?:enumerate|itemize|description)\}", flags=re.IGNORECASE)
LINEBREAK_PATTERN = re.compile(r"\\\\")
COMMAND_TOKEN_REPLACEMENTS = {
    "left": "",
    "right": "",
    "in": " in ",
    "to": " to ",
    "mapsto": " maps to ",
    "subset": " subset ",
    "subseteq": " subseteq ",
    "supset": " supset ",
    "supseteq": " supseteq ",
    "cup": " cup ",
    "cap": " cap ",
    "times": " x ",
    "cdot": " * ",
    "leq": " <= ",
    "le": " <= ",
    "geq": " >= ",
    "ge": " >= ",
    "neq": " != ",
    "approx": " approx ",
    "sim": " sim ",
    "ell": " ell ",
}


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
    env_names = discover_conjecture_environment_names(documents)
    matches: list[ExtractedConjecture] = []
    for document in documents:
        matches.extend(extract_conjectures(document.content, source_file=document.filename, env_names=env_names))
    return matches


def extract_conjectures(
    text: str,
    source_file: str,
    env_names: set[str] | None = None,
) -> list[ExtractedConjecture]:
    names = _expand_star_variants(env_names or set(DEFAULT_ENVIRONMENTS))
    pattern = _build_conjecture_pattern(names)
    search_text = preprocess_latex_for_extraction(text)

    extracted: list[ExtractedConjecture] = []
    for index, match in enumerate(pattern.finditer(search_text), start=1):
        raw = text[match.start() : match.end()].strip()
        body = match.group("body").strip()
        plain = latex_to_plain_text(body)

        start_line = search_text.count("\n", 0, match.start()) + 1
        end_line = search_text.count("\n", 0, match.end()) + 1
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


def discover_conjecture_environment_names(documents: list[LatexDocument]) -> set[str]:
    env_names = set(DEFAULT_ENVIRONMENTS)
    for document in documents:
        cleaned = preprocess_latex_for_extraction(document.content)
        env_names.update(_discover_newtheorem_conjecture_envs(cleaned))
        env_names.update(_discover_declaretheorem_conjecture_envs(cleaned))
    return _expand_star_variants(env_names)


def preprocess_latex_for_extraction(text: str) -> str:
    without_comments = _mask_comments_preserve_layout(text)
    return _mask_iffalse_blocks_preserve_layout(without_comments)


def _discover_newtheorem_conjecture_envs(text: str) -> set[str]:
    env_names: set[str] = set()
    for match in NEWTHEOREM_PATTERN.finditer(text):
        env = match.group("env").strip()
        title = match.group("title").strip()
        if not _is_valid_env_name(env):
            continue
        if _looks_like_conjecture_label(title) or "conj" in env.lower():
            env_names.add(env)
    return env_names


def _discover_declaretheorem_conjecture_envs(text: str) -> set[str]:
    env_names: set[str] = set()
    for match in DECLARETHEOREM_PATTERN.finditer(text):
        env = match.group("env").strip()
        if not _is_valid_env_name(env):
            continue

        options = (match.group("options") or "").strip()
        label = _extract_declaretheorem_name(options)

        if (label and _looks_like_conjecture_label(label)) or "conj" in env.lower():
            env_names.add(env)
    return env_names


def _extract_declaretheorem_name(options: str) -> str:
    if not options:
        return ""
    match = NAME_OPTION_PATTERN.search(options)
    if not match:
        return ""
    return (match.group("braced") or match.group("plain") or "").strip()


def _build_conjecture_pattern(env_names: set[str]) -> re.Pattern[str]:
    escaped = sorted((re.escape(name) for name in env_names if name), key=len, reverse=True)
    if not escaped:
        escaped = [re.escape("conjecture")]
    alternation = "|".join(escaped)
    return re.compile(
        rf"\\begin\{{(?P<env>{alternation})\}}(?P<begin_opts>\[[^\]]*\])?(?P<body>.*?)\\end\{{(?P=env)\}}",
        flags=re.IGNORECASE | re.DOTALL,
    )


def _expand_star_variants(env_names: set[str]) -> set[str]:
    expanded = set(env_names)
    for name in list(env_names):
        if not name.endswith("*"):
            expanded.add(f"{name}*")
    return expanded


def _looks_like_conjecture_label(label: str) -> bool:
    return "conjecture" in latex_to_plain_text(label).lower()


def _is_valid_env_name(env: str) -> bool:
    if not env:
        return False
    for banned in (" ", "{", "}", "[", "]", "\\"):
        if banned in env:
            return False
    return True


def _mask_comments_preserve_layout(text: str) -> str:
    chars = list(text)
    i = 0
    n = len(chars)
    while i < n:
        if chars[i] == "%" and not _is_escaped(chars, i):
            j = i
            while j < n and chars[j] != "\n":
                chars[j] = " "
                j += 1
            i = j
        else:
            i += 1
    return "".join(chars)


def _is_escaped(chars: list[str], index: int) -> bool:
    backslashes = 0
    j = index - 1
    while j >= 0 and chars[j] == "\\":
        backslashes += 1
        j -= 1
    return backslashes % 2 == 1


def _mask_iffalse_blocks_preserve_layout(text: str) -> str:
    chars = list(text)
    depth = 0
    block_start: int | None = None

    for match in IFFALSE_TOKEN_PATTERN.finditer(text):
        token = match.group(0).lower()
        if token.startswith("\\if"):
            if depth == 0:
                block_start = match.start()
            depth += 1
            continue

        if token == "\\fi" and depth > 0:
            depth -= 1
            if depth == 0 and block_start is not None:
                _blank_range_preserve_newlines(chars, block_start, match.end())
                block_start = None

    if depth > 0 and block_start is not None:
        _blank_range_preserve_newlines(chars, block_start, len(chars))

    return "".join(chars)


def _blank_range_preserve_newlines(chars: list[str], start: int, end: int) -> None:
    for i in range(start, end):
        if chars[i] != "\n":
            chars[i] = " "


def latex_to_plain_text(text: str) -> str:
    no_comments = re.sub(r"(?<!\\)%.*", "", text)
    no_labels = re.sub(r"\\(label|ref|eqref|cite|url|footnote)\*?(\[[^\]]*\])?\{[^{}]*\}", "", no_comments)
    no_style = STYLE_COMMAND_PATTERN.sub("", no_labels)
    no_list_env = LIST_ENV_PATTERN.sub(" ", no_style)
    itemized = re.sub(r"\\item\b", " ", no_list_env)
    linebroken = LINEBREAK_PATTERN.sub(" ", itemized)
    unspaced = linebroken.replace("~", " ")

    token_normalized = unspaced
    for command, replacement in COMMAND_TOKEN_REPLACEMENTS.items():
        token_normalized = re.sub(rf"\\{command}\b", replacement, token_normalized)
    token_normalized = token_normalized.replace(r"\{", "{").replace(r"\}", "}")

    # Keep common formatting-command bodies while dropping command names.
    keep_body_commands = re.sub(r"\\[a-zA-Z]+\*?\{([^{}]*)\}", r"\1", token_normalized)
    no_remaining_commands = re.sub(r"\\[a-zA-Z]+\*?(\[[^\]]*\])?", "", keep_body_commands)
    no_braces = no_remaining_commands.replace("{", " ").replace("}", " ")

    normalized = " ".join(no_braces.split())
    return normalized
