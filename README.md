# Conjectures from Recent arXiv Math Papers

This project scrapes recent `math*` arXiv papers, pulls out open conjectures, and builds a clean, shareable dataset from them. We use an LLM to label each conjecture by interestingness and tractability, and then use GPT-5.4 Thinking to attempt proofs of the most tractable ones. Early runs have turned up some potential successes.

The current live labeled snapshot in this repo, [data/conjectures_month_live_20260306.sqlite](data/conjectures_month_live_20260306.sqlite), contains 798 conjecture candidates, including 676 labeled `real_open_conjecture`, from papers published between February 2, 2026 and March 4, 2026.

In an initial pilot, GPT-5.4 Thinking (xhigh) tackled 20 high-viability conjectures and produced 6 proofs we think might hold up: 2 proposed confirmations of open conjectures, and 4 apparent disconfirmations. There are  also several potentially useful partial results. Attempts for each conjecture can be found in [solver_attempts_20_summary.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.md), and a higher-level audit of the strongest results is in [solver_attempts_20_audit.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md). These are model-reported results, not independently verified proofs or counterexamples.

## Pipeline

1. Ingest recent arXiv math papers over a date range or rolling weekly window.
2. Extract conjectures and store them with paper metadata (including arXiv category, DOI, journal reference, comments, and license when available).
3. Label the conjectures with gpt-5-mini as `real_open_conjecture`, `not_real_conjecture`, or `uncertain`, and score real conjectures for interestingness and near-term viability.
4. Optionally run GPT-5.4 Thinking (xhigh) on the most tractable conjectures.

## Install

Python `>=3.10` is required.

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e '.[dev,llm]'
```

Optional extras:

- Add `parquet` if you want Parquet export support: `pip install -e '.[dev,llm,parquet]'`
- Add `huggingface` if you want Hugging Face uploads: `pip install -e '.[dev,llm,huggingface]'`
- Set `OPENAI_API_KEY` before running `filter-llm` or `solve-llm`
- Set `HF_TOKEN` before running `publish-hf` unless you already have a cached Hugging Face login
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

Prepare a public Hugging Face snapshot with license-aware redaction:

```bash
conjectures-arxiv export-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/conjectures-arxiv
```

Dry-run the full Hugging Face publish pipeline without uploading:

```bash
conjectures-arxiv publish-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/conjectures-arxiv \
  --dry-run
```

Publish to Hugging Face when ready:

```bash
export HF_TOKEN=...
conjectures-arxiv publish-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/conjectures-arxiv
```

## Hugging Face License Policy

The public Hugging Face snapshot is intentionally aggressive by default:

- If the paper license is missing or unrecognized, the conjecture text is still published.
- If the license is clearly restrictive for broad republication, the conjecture text is withheld and only paper references are published.
- This Hugging Face release is treated as a noncommercial release, so `CC BY-NC*` papers are published.

Current withhold rules:

- arXiv non-exclusive distribution license (`arxiv.org/licenses/nonexclusive-distrib/1.0/`)

The generated snapshot includes per-record decision fields like `publication_decision`, `publication_text_reason`, and `publication_policy_version`, plus a `publication_manifest.json` summary.
The conjecture rows also include the newest available LLM label metadata per conjecture, including the latest label, confidence, interestingness score, and viability score.

## Current Snapshot

Latest local labeled dataset:

- `data/conjectures_month_live_20260306.sqlite`
- `data/exports_month_live_20260306/conjectures.jsonl`
- `data/exports_month_live_20260306/conjectures.csv`
- `data/exports_month_live_20260306/papers.jsonl`
- `data/exports_month_live_20260306/real_conjectures_gpt-5-mini.jsonl`
- `data/exports_month_live_20260306/real_conjectures_gpt-5-mini.csv`

Current totals:

- `papers_seen=4756`
- `conjecture_candidates=798`
- `real_open_conjecture=676`
- `not_real_conjecture=119`
- `uncertain=3`
- `published_at_range=2026-02-02..2026-03-04`

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

- [solver_attempts_20_summary.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.md)
- [solver_attempts_20_summary.csv](data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.csv)
- [solver_attempts_20_audit.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md)
- [solver_attempts_20.jsonl](data/exports_solver_status_20260309_attempts20/solver_attempts_20.jsonl)
- [solver_attempts_20.csv](data/exports_solver_status_20260309_attempts20/solver_attempts_20.csv)

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
- `src/conjectures_arxiv/license_policy.py`: publication license classification
- `src/conjectures_arxiv/hf_publish.py`: Hugging Face dataset uploads
- `src/conjectures_arxiv/s3_publish.py`: S3 publishing helpers

## Tests

```bash
pytest -q
```
