# Conjectures from Recent arXiv Math Papers

This repository builds a shareable dataset of open conjectures from recent `math*` arXiv papers. It can ingest papers, expand TeX sources, extract conjecture-like environments, store them in SQLite, label candidates with GPT-5 Mini, and run GPT-5.4 solver attempts on the most tractable items.

## Pipeline

1. Ingest recent arXiv math papers over a date range or rolling weekly window.
2. Download source from arXiv, resolve `\input` and `\include`, and remove inactive TeX regions such as `%` comments and `\iffalse ... \fi`.
3. Extract conjecture-like blocks and store them with paper metadata in SQLite, including arXiv category, DOI, journal reference, comments, and license when available.
4. Optionally label extracted candidates with GPT-5 Mini as `real_open_conjecture`, `not_real_conjecture`, or `uncertain`, and score real conjectures for interestingness and near-term viability.
5. Optionally run GPT-5.4 solver attempts, with web search enabled, on the highest-priority real conjectures.
6. Export JSONL/CSV, optionally export Parquet, and optionally publish artifacts to S3.

## Install

Python `>=3.10` is required.

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e '.[dev,llm]'
```

Optional extras:

- Add `parquet` if you want Parquet export support: `pip install -e '.[dev,llm,parquet]'`
- Set `OPENAI_API_KEY` before running `filter-llm` or `solve-llm`
- Configure AWS credentials before running `upload-s3`

## Quick Start

Create the database:

```bash
conjectures-arxiv init-db --db-path data/conjectures.sqlite
```

Ingest a rolling week of papers:

```bash
conjectures-arxiv ingest-week \
  --db-path data/conjectures.sqlite \
  --days 7 \
  --output-dir data/exports
```

Ingest an explicit date range instead:

```bash
conjectures-arxiv ingest-range \
  --db-path data/conjectures.sqlite \
  --from-date 2026-03-01 \
  --to-date 2026-03-07 \
  --output-dir data/exports
```

Label conjectures with GPT-5 Mini:

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

Submit GPT-5.4 solver attempts on the highest-priority conjectures:

```bash
export OPENAI_API_KEY=...
conjectures-arxiv solve-llm \
  --db-path data/conjectures.sqlite \
  --label-model gpt-5-mini \
  --limit 10
```

`solve-llm` submits attempts asynchronously by default. Use `--wait` if you want to block on completion, or poll/export status with:

```bash
export OPENAI_API_KEY=...
conjectures-arxiv solve-status \
  --db-path data/conjectures.sqlite \
  --limit 10 \
  --refresh-open \
  --output-dir data/exports_solver_status
```

Export the database and current artifact sets:

```bash
conjectures-arxiv export \
  --db-path data/conjectures.sqlite \
  --output-dir data/exports
```

Upload exports to S3:

```bash
conjectures-arxiv upload-s3 \
  --db-path data/conjectures.sqlite \
  --exports-dir data/exports \
  --bucket conjectures-arxiv-math-067542072602 \
  --prefix math-conjectures
```

## Current Snapshot

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

Latest S3 location:

- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/`

## Current Solver Pilot

The current GPT-5.4 solver pilot covers 20 attempts on the highest-priority viable conjectures.

- 6 strong settlement-quality outcomes: 2 confirmations and 4 disconfirmations
- 2 formalization failures
- 4 partial-progress outcomes
- 1 qualified confirmation
- 1 draft question that looks resolved in substance
- 6 unresolved outcomes

These are model-reported results, not independently verified mathematical proofs or counterexamples.

Artifacts:

- `data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.md`
- `data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.csv`
- `data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md`
- `data/exports_solver_status_20260309_attempts20/solver_attempts_20.jsonl`
- `data/exports_solver_status_20260309_attempts20/solver_attempts_20.csv`

## S3 Access

To request access, send the maintainer:

- AWS account ID
- IAM principal ARN
- Requested level, usually `read-only`
- Requested scope, usually `latest/*` or `runs/*`

Typical read-only permissions:

- `s3:ListBucket` on bucket `conjectures-arxiv-math-067542072602`
- `s3:GetObject` on `math-conjectures/latest/*`

## Project Layout

- `src/conjectures_arxiv/cli.py`: CLI entrypoints
- `src/conjectures_arxiv/pipeline.py`: ingestion orchestration
- `src/conjectures_arxiv/arxiv_client.py`: arXiv API client
- `src/conjectures_arxiv/source_fetcher.py`: source download and expansion
- `src/conjectures_arxiv/conjecture_extractor.py`: conjecture parsing
- `src/conjectures_arxiv/llm_filter.py`: GPT-5 Mini labeling
- `src/conjectures_arxiv/solver.py`: GPT-5.4 solver prompt and response handling
- `src/conjectures_arxiv/database.py`: SQLite schema and exports
- `src/conjectures_arxiv/s3_publish.py`: S3 publishing helpers

## Tests

```bash
pytest -q
```
