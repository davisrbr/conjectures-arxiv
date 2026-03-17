# OpenConjecture, a living dataset of mathematics conjectures from the ArXiv

This project ingests recent papers announced on arXiv's math page, pulls out open conjectures, and builds a dataset from them. We use an LLM to label each conjecture by interestingness and tractability, and then use GPT-5.4 Thinking to attempt proofs of the most tractable ones. Early runs have turned up some potential successes.

The current live labeled snapshot in this repo, [data/conjectures_month_live_20260317.sqlite](data/conjectures_month_live_20260317.sqlite), contains 890 (likely open) conjectures from 6661 papers in the current arXiv math announcement stream. Most of those papers have `published_at` between February 2, 2026 and March 16, 2026.

For an initial pilot, we ran GPT-5.4 Thinking (xhigh) to attempt solutions on 20 of the collected conjectures. **Of these 20, the model produced 6 settlements of the conjecture that might hold up: 2 confirmations of open conjectures and 4 disconfirmations**. The rest currently break down into 3 mathematically useful partial results, 1 qualified confirmation, 1 draft question resolved in substance by its own paper, 2 specification/formalization issues, and 7 unresolved outcomes. Attempts for each conjecture can be found in [solver_attempts_20_summary.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_summary.md), and a higher-level audit of the results in [solver_attempts_20_audit.md](data/exports_solver_status_20260309_attempts20/solver_attempts_20_audit.md). 

Finally, we used Codex (with GPT-5.4) to attempt to formalize 6 of the 20 proof attempts in Lean, [linked here](formalization/notes). In 4 of 6 cases, the system claims that the formalization is successful. These formalization attempts required Codex (GPT-5.4 xhigh Fast) from between a couple hours to well over 30 hours of wall-clock time. These are LLM generated and model-reported, and they have not been independently verified. 

## Pipeline

1. Ingest recent arXiv math announcements over a date range (we choose the ~past month).
2. Extract conjecture blocks and store them with paper metadata, including arXiv category, DOI, journal reference, comments, and license.
3. Label extracted candidates with GPT-5 Mini as `real_open_conjecture`, `not_real_conjecture`, or `uncertain`, and score real conjectures for `interestingness` and near-term solution `viability`, i.e. the tractability.
4. (Optional) Run GPT-5.4 Thinking (xhigh) to attempt solutions on a subset of the most tractable conjectures.
5. (Optional) Formalize the attempted solutions from (4) in Lean.

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

## Lean Formalization Workspace

The Lean 4 formalization workspace lives in [formalization/](formalization/). It is a separate Lake project pinned by [formalization/lean-toolchain](formalization/lean-toolchain).

Recommended setup:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
cd formalization
lake exe cache get
lake build QuasimodularSturm
```

To build a single module instead:

```bash
cd formalization
lake build QuasimodularSturm.Attempts.HilbertDepth
lake build QuasimodularSturm.Attempts.MagnitudeDisproof
lake build QuasimodularSturm.Attempts.SteinDisproof
lake build QuasimodularSturm.Attempts.XiZeroLimit
```

Additional notes on the Lean workspace, module layout, and verification status are in [formalization/README.md](formalization/README.md).

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
  --repo-id your-org/openconjecture
```

```bash
conjectures-arxiv publish-hf \
  --db-path data/conjectures.sqlite \
  --output-dir data/huggingface_dataset \
  --repo-id your-org/openconjecture
```

## Current Snapshot

Latest labeled datasets can be found in `data/exports_month_live_20260317/*`

Current totals:

- `papers_seen=6661`
- `conjecture_candidates=1075`
- `real_open_conjecture=890`
- `not_real_conjecture=182`
- `uncertain=3`
- `published_at_focus_range=2026-02-02..2026-03-16`
- `older_announced_cross_list_papers=7`

## Current Solver Pilot

The current GPT-5.4 solver pilot covers 20 attempts on the highest-priority viable conjectures.

- 6 strong settlement-quality outcomes: 2 confirmations and 4 disconfirmations
- 2 specification/formalization issues
- 3 partial-progress outcomes
- 1 qualified confirmation
- 1 draft question that looks resolved in substance
- 7 unresolved outcomes

These are model-reported results, not independently verified mathematical proofs or counterexamples.

Some of the strongest entries now also have dedicated Lean formalizations in [formalization/](formalization/). In particular, the Hilbert-depth confirmation and the adapted-`\widetilde\Xi_n` zero-limit confirmation now each have end-to-end Lean proofs of the theorem stated by the solver writeup, while the Stein and magnitude counterexamples have Lean formalizations of the concrete disproofs.

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
