# Conjectures from Recent arXiv Math Papers

This project scrapes recent `math*` arXiv papers, pulls out open conjectures, and builds a dataset from them. We use an LLM to label each conjecture by interestingness and tractability, and then use GPT-5.4 Thinking to attempt proofs of the most tractable ones. Early runs have turned up some potential successes.

The current live labeled snapshot in this repo, [data/conjectures_month_live_20260306.sqlite](data/conjectures_month_live_20260306.sqlite), contains 676 (likely open) conjectures, from papers published between February 2, 2026 and March 4, 2026.

For an initial pilot, we ran GPT-5.4 Thinking (xhigh) to attempt solutions on 20 of the collected conjectures. **Of these 20, the model produced 6 proofs that might hold up: 2 confirmations of open conjectures, and 4 apparent disconfirmations**. There are also several potentially useful partial results. Attempts for each conjecture can be found in [solver_attempts_20_summary.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.md), and a higher-level audit of the results in [solver_attempts_20_audit.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md). These are LLM generated, and the proofs have not been independently verified.

## Pipeline

1. Ingest recent arXiv math papers over a date range (we choose the ~past month).
2. Extract conjecture blocks and store them with paper metadata, including arXiv category, DOI, journal reference, comments, and license.
3. Label extracted candidates with GPT-5 Mini as `real_open_conjecture`, `not_real_conjecture`, or `uncertain`, and score real conjectures for `interestingness` and near-term solution `viability`, i.e. the tractability.
4. Run GPT-5.4 Thinking (xhigh) to attempt solutions on a subset of the most tractable conjectures.

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
- Set `OPENAI_API_KEY` before running `filter-llm` or `solve-llm`, and `HF_TOKEN` before running `publish-hf`

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

`solve-llm` submits attempts asynchronously by default. 

Export the database and current artifact sets:

```bash
conjectures-arxiv export \
  --db-path data/conjectures.sqlite \
  --output-dir data/exports
```

Publish to Hugging Face (with redactions based on the license):

```bash
export HF_TOKEN=...
conjectures-arxiv export-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/conjectures-arxiv
```

```bash
conjectures-arxiv publish-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/conjectures-arxiv
```

## Current Snapshot

Latest labeled datasets can be found in `data/exports_month_live_20260306/*`

Current totals:

- `papers_seen=4756`
- `conjecture_candidates=798`
- `real_open_conjecture=676`
- `not_real_conjecture=119`
- `uncertain=3`
- `published_at_range=2026-02-02..2026-03-04`

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
- [solver_attempts_20_audit.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md)
- [solver_attempts_20.csv](data/exports_solver_status_20260309_attempts20/solver_attempts_20.csv)

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
