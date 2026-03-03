# Conjectures from Recent arXiv Math Papers

This repository ingests recent arXiv math papers, extracts LaTeX conjecture environments, and stores/share results.

## What it does

- Queries arXiv for papers in `cat:math*` over a date range (default: past week).
- Downloads each paper source from `/e-print/{id}`.
- Extracts LaTeX blocks of the form `\\begin{conjecture}` ... `\\end{conjecture}` (including starred variants).
- Stores normalized paper metadata + conjectures in SQLite.
- Exports JSONL/CSV snapshots.
- Uploads DB + exports to S3 for collaboration.

## Project structure

- `src/conjectures_arxiv/arxiv_client.py`: arXiv API querying and Atom parsing.
- `src/conjectures_arxiv/source_fetcher.py`: source download and tar/gzip/plain TeX extraction.
- `src/conjectures_arxiv/conjecture_extractor.py`: conjecture block extraction and normalization.
- `src/conjectures_arxiv/database.py`: SQLite schema and persistence.
- `src/conjectures_arxiv/pipeline.py`: ingestion orchestration.
- `src/conjectures_arxiv/s3_publish.py`: S3 publishing.
- `src/conjectures_arxiv/cli.py`: command-line interface.

## Quick start

```bash
python --version  # requires Python 3.10+
python -m venv .venv
source .venv/bin/activate
pip install -e '.[dev]'
```

Initialize the database:

```bash
conjectures-arxiv init-db --db-path data/conjectures.sqlite
```

Ingest past-week papers:

```bash
conjectures-arxiv ingest-week --db-path data/conjectures.sqlite --days 7
```

Export current records:

```bash
conjectures-arxiv export --db-path data/conjectures.sqlite --output-dir data/exports
```

Upload DB + exports to S3:

```bash
conjectures-arxiv upload-s3 \
  --db-path data/conjectures.sqlite \
  --exports-dir data/exports \
  --bucket conjectures-arxiv-math-067542072602 \
  --prefix math-conjectures \
  --create-bucket \
  --region us-east-1
```

## Data model

SQLite tables:

- `papers`: one row per arXiv paper.
- `conjectures`: one row per extracted conjecture block, deduplicated by `(arxiv_id, content_hash)`.
- `ingestion_runs`: tracking and metrics for each ingestion execution.

S3 layout:

- `s3://<bucket>/<prefix>/runs/<timestamp>/...`: immutable run snapshots.
- `s3://<bucket>/<prefix>/latest/...`: most recent artifacts for collaborators.

## Shared S3 dataset

- Bucket: `conjectures-arxiv-math-067542072602`
- Prefix: `math-conjectures`
- Latest path: `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/`
Latest files:
- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/conjectures_week_live_20260303.sqlite`
- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/conjectures.jsonl`
- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/conjectures.csv`
- `s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/papers.jsonl`

## Requesting S3 access

Send this info to the dataset maintainer when requesting access:

- Your AWS account ID.
- The IAM principal ARN that should get access (user or role).
- Requested access level (`read-only` recommended for most collaborators).
- Requested scope (`latest/*` only, or also `runs/*` history).
- Optional expiration date for temporary access.

Recommended default collaborator permissions:

- `s3:ListBucket` on bucket `conjectures-arxiv-math-067542072602`.
- `s3:GetObject` on `math-conjectures/latest/*`.
- Optional `s3:GetObject` on `math-conjectures/runs/*` for historical snapshots.

Quick access check once permissions are granted:

```bash
aws s3 ls s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/
aws s3 cp s3://conjectures-arxiv-math-067542072602/math-conjectures/latest/conjectures.jsonl - | head
```

## Notes on coverage

- This version targets papers in `cat:math*` returned by the arXiv API date-range query.
- Extraction is source-based and currently focused on explicit LaTeX conjecture environments.
- Papers without accessible source or with nonstandard environments may yield zero conjectures.

## Tests

```bash
pytest -q
```
