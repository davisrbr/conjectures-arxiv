# Conjectures from Recent arXiv Math Papers

This project ingests recent `math*` arXiv papers, extracts conjecture blocks from LaTeX source, and publishes a shareable dataset.

## What It Does

- Queries arXiv by date range (default: past 7 days).
- Downloads source (`/e-print/{id}`), resolves `\\input`/`\\include`, and extracts conjecture-like environments.
- Cleans inactive TeX regions before extraction (`%` comments and `\\iffalse ... \\fi`).
- Stores papers + conjectures in SQLite.
- Captures arXiv paper license metadata (`license_url`) from the Atom feed.
- Captures additional arXiv metadata when available: `primary_category`, `doi`, `journal_ref`, `comments`, `license_url` (with abs-page fallback for license).
- Runs a GPT-5 Mini second-stage classifier with fields:
- `label` in `{real_open_conjecture, not_real_conjecture, uncertain}`
- `interestingness_score` (0..1), plus confidence/rationale
- `viability_score` (0..1), plus confidence/rationale for near-term (1-5 year) solvability
- Interestingness is computed only for `real_open_conjecture` items (not for `not_real_conjecture`/`uncertain`) to reduce compute.
- Viability is computed only for `real_open_conjecture` items (not for `not_real_conjecture`/`uncertain`) to reduce compute.
- Model context includes paper title, authors, abstract, conjecture text, and local source window (default `±20` lines).
- Retries malformed batch responses per item to avoid parser-artifact labels.
- Exports JSONL/CSV and uploads to S3.

## Quick Start

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e '.[dev,llm]'
```

Initialize DB:

```bash
conjectures-arxiv init-db --db-path data/conjectures.sqlite
```

Ingest the past week:

```bash
conjectures-arxiv ingest-week --db-path data/conjectures.sqlite --days 7 --output-dir data/exports
```

Run GPT-5 Mini filtering:

```bash
export OPENAI_API_KEY=...
conjectures-arxiv filter-llm \
  --db-path data/conjectures.sqlite \
  --model gpt-5-mini \
  --batch-size 8 \
  --export-real \
  --output-dir data/exports \
  --min-confidence 0.7
```

Upload to S3:

```bash
conjectures-arxiv upload-s3 \
  --db-path data/conjectures.sqlite \
  --exports-dir data/exports \
  --bucket conjectures-arxiv-math-067542072602 \
  --prefix math-conjectures
```

## Canonical Snapshot (Current)

Local canonical dataset:

- `data/conjectures_week_canonical_20260303.sqlite`
- `data/exports_week_canonical_20260303/conjectures.jsonl`
- `data/exports_week_canonical_20260303/conjectures.csv`
- `data/exports_week_canonical_20260303/papers.jsonl`
- `data/exports_week_canonical_20260303/real_conjectures_gpt-5-mini.jsonl`
- `data/exports_week_canonical_20260303/real_conjectures_gpt-5-mini.csv`

Current totals:

- `papers_seen=851`
- `conjecture_candidates=160`
- `real_open_conjecture=147`
- `not_real_conjecture=13`

S3 latest:

- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/`
- Includes the canonical SQLite snapshot, base exports, and `real_conjectures_gpt-5-mini.*`.

## Requesting S3 Access

Send the maintainer:

- AWS account ID
- IAM principal ARN (user/role)
- Requested level (`read-only` is default)
- Scope (`latest/*` only, or include `runs/*`)

Typical read-only permissions:

- `s3:ListBucket` on bucket `conjectures-arxiv-math-067542072602`
- `s3:GetObject` on `math-conjectures/latest/*`

## Project Layout

- `src/conjectures_arxiv/cli.py`: CLI entrypoints
- `src/conjectures_arxiv/pipeline.py`: ingestion orchestration
- `src/conjectures_arxiv/source_fetcher.py`: source download/extraction
- `src/conjectures_arxiv/conjecture_extractor.py`: conjecture parsing
- `src/conjectures_arxiv/llm_filter.py`: GPT-5 Mini labeling
- `src/conjectures_arxiv/database.py`: SQLite schema + exports
- `src/conjectures_arxiv/s3_publish.py`: S3 publishing

## Tests

```bash
pytest -q
```
