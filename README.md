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
python -m venv .venv
source .venv/bin/activate
pip install -e .[dev]
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
  --bucket your-bucket \
  --prefix conjectures-arxiv \
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

## Notes on coverage

- This version targets papers in `cat:math*` returned by the arXiv API date-range query.
- Extraction is source-based and currently focused on explicit LaTeX conjecture environments.
- Papers without accessible source or with nonstandard environments may yield zero conjectures.

## Tests

```bash
pytest -q
```
