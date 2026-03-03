from __future__ import annotations

import argparse
from datetime import date, timedelta
import logging
from pathlib import Path
from typing import Callable

from .database import Database
from .llm_filter import GPT5MiniConjectureFilter, LLMFilterRunner
from .pipeline import IngestionPipeline
from .s3_publish import S3Publisher


def parse_date(value: str) -> date:
    try:
        return date.fromisoformat(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"Invalid date '{value}'. Use YYYY-MM-DD.") from exc


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Ingest recent arXiv math conjectures")
    subparsers = parser.add_subparsers(dest="command", required=True)

    init_parser = subparsers.add_parser("init-db", help="Create SQLite schema")
    init_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    init_parser.set_defaults(handler=cmd_init_db)

    ingest_parser = subparsers.add_parser("ingest-range", help="Ingest papers over an explicit date range")
    _add_ingest_arguments(ingest_parser)
    ingest_parser.add_argument("--from-date", required=True, type=parse_date)
    ingest_parser.add_argument("--to-date", required=True, type=parse_date)
    ingest_parser.set_defaults(handler=cmd_ingest_range)

    week_parser = subparsers.add_parser("ingest-week", help="Ingest papers from past N days")
    _add_ingest_arguments(week_parser)
    week_parser.add_argument("--days", type=int, default=7)
    week_parser.set_defaults(handler=cmd_ingest_week)

    export_parser = subparsers.add_parser("export", help="Export DB to JSONL/CSV")
    export_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    export_parser.add_argument("--output-dir", default="data/exports")
    export_parser.add_argument("--with-parquet", action="store_true")
    export_parser.set_defaults(handler=cmd_export)

    upload_parser = subparsers.add_parser("upload-s3", help="Upload DB and export files to S3")
    upload_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    upload_parser.add_argument("--exports-dir", default="data/exports")
    upload_parser.add_argument("--bucket", required=True)
    upload_parser.add_argument("--prefix", default="conjectures-arxiv")
    upload_parser.add_argument("--create-bucket", action="store_true")
    upload_parser.add_argument("--region", default="")
    upload_parser.set_defaults(handler=cmd_upload_s3)

    filter_parser = subparsers.add_parser("filter-llm", help="Classify conjectures with GPT-5 Mini")
    filter_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    filter_parser.add_argument("--model", default="gpt-5-mini")
    filter_parser.add_argument("--limit", type=int, default=None)
    filter_parser.add_argument("--include-labeled", action="store_true")
    filter_parser.add_argument("--context-window-lines", type=int, default=12)
    filter_parser.add_argument("--batch-size", type=int, default=8)
    filter_parser.add_argument("--sleep-seconds", type=float, default=0.0)
    filter_parser.add_argument("--output-dir", default="data/exports")
    filter_parser.add_argument("--export-real", action="store_true")
    filter_parser.add_argument("--min-confidence", type=float, default=0.0)
    filter_parser.set_defaults(handler=cmd_filter_llm)

    return parser


def _add_ingest_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--db-path", default="data/conjectures.sqlite")
    parser.add_argument("--max-papers", type=int, default=None)
    parser.add_argument("--sleep-seconds", type=float, default=0.2)
    parser.add_argument("--output-dir", default="data/exports")
    parser.add_argument("--with-parquet", action="store_true")
    parser.add_argument("--skip-export", action="store_true")
    parser.add_argument("--bucket", default="")
    parser.add_argument("--prefix", default="conjectures-arxiv")
    parser.add_argument("--create-bucket", action="store_true")
    parser.add_argument("--region", default="")


def cmd_init_db(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    try:
        db.init_schema()
    finally:
        db.close()
    print(f"Initialized database at {args.db_path}")
    return 0


def cmd_ingest_range(args: argparse.Namespace) -> int:
    return _run_ingest(
        db_path=args.db_path,
        from_date=args.from_date,
        to_date=args.to_date,
        max_papers=args.max_papers,
        sleep_seconds=args.sleep_seconds,
        output_dir=args.output_dir,
        with_parquet=args.with_parquet,
        skip_export=args.skip_export,
        bucket=args.bucket,
        prefix=args.prefix,
        create_bucket=args.create_bucket,
        region=args.region,
    )


def cmd_ingest_week(args: argparse.Namespace) -> int:
    to_date = date.today()
    from_date = to_date - timedelta(days=max(args.days - 1, 0))
    return _run_ingest(
        db_path=args.db_path,
        from_date=from_date,
        to_date=to_date,
        max_papers=args.max_papers,
        sleep_seconds=args.sleep_seconds,
        output_dir=args.output_dir,
        with_parquet=args.with_parquet,
        skip_export=args.skip_export,
        bucket=args.bucket,
        prefix=args.prefix,
        create_bucket=args.create_bucket,
        region=args.region,
    )


def _run_ingest(
    *,
    db_path: str,
    from_date: date,
    to_date: date,
    max_papers: int | None,
    sleep_seconds: float,
    output_dir: str,
    with_parquet: bool,
    skip_export: bool,
    bucket: str,
    prefix: str,
    create_bucket: bool,
    region: str,
) -> int:
    if from_date > to_date:
        raise ValueError(f"from-date ({from_date}) cannot be after to-date ({to_date})")

    db = Database(db_path)
    db.init_schema()

    try:
        pipeline = IngestionPipeline(db=db)
        result = pipeline.ingest(
            from_date=from_date,
            to_date=to_date,
            max_papers=max_papers,
            sleep_seconds=sleep_seconds,
        )

        print(
            "Ingestion complete:",
            f"run_id={result.run_id}",
            f"papers_seen={result.papers_seen}",
            f"papers_stored={result.papers_stored}",
            f"conjectures_stored={result.conjectures_stored}",
            f"errors={result.errors}",
        )

        if skip_export:
            return 0

        exported = db.export(output_dir=output_dir)
        print("Exported artifacts:")
        for artifact in exported.values():
            print(f"  - {artifact}")

        if with_parquet:
            try:
                parquet_exported = db.export_parquet(output_dir=output_dir)
            except RuntimeError as exc:
                print(f"Parquet export failed: {exc}")
                return 1
            print("Exported parquet datasets:")
            for artifact in parquet_exported.values():
                print(f"  - {artifact}")

        if bucket:
            publisher = S3Publisher(bucket=bucket, prefix=prefix)
            if create_bucket:
                publisher.ensure_bucket(region=region)
            uploaded = publisher.upload_artifacts(db_path=db_path, exports_dir=output_dir)
            print("Uploaded artifacts:")
            for uri in uploaded:
                print(f"  - {uri}")

        return 0
    finally:
        db.close()


def cmd_export(args: argparse.Namespace) -> int:
    parquet_exported = {}
    db = Database(args.db_path)
    try:
        db.init_schema()
        exported = db.export(args.output_dir)
        if args.with_parquet:
            try:
                parquet_exported = db.export_parquet(args.output_dir)
            except RuntimeError as exc:
                print(f"Parquet export failed: {exc}")
                return 1
    finally:
        db.close()

    print("Exported artifacts:")
    for artifact in exported.values():
        print(f"  - {artifact}")
    if parquet_exported:
        print("Exported parquet datasets:")
        for artifact in parquet_exported.values():
            print(f"  - {artifact}")
    return 0


def cmd_upload_s3(args: argparse.Namespace) -> int:
    publisher = S3Publisher(bucket=args.bucket, prefix=args.prefix)
    if args.create_bucket:
        publisher.ensure_bucket(region=args.region)
    uploaded = publisher.upload_artifacts(db_path=args.db_path, exports_dir=args.exports_dir)
    print("Uploaded artifacts:")
    for uri in uploaded:
        print(f"  - {uri}")
    return 0


def cmd_filter_llm(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    db.init_schema()

    try:
        try:
            classifier = GPT5MiniConjectureFilter(model=args.model)
        except RuntimeError as exc:
            print(f"LLM filter setup failed: {exc}")
            return 1
        runner = LLMFilterRunner(db=db, classifier=classifier)
        summary = runner.run(
            model=args.model,
            limit=args.limit,
            only_unlabeled=not args.include_labeled,
            context_window_lines=args.context_window_lines,
            batch_size=args.batch_size,
            sleep_seconds=args.sleep_seconds,
        )
        print(
            "LLM filtering complete:",
            f"candidates={summary.total_candidates}",
            f"processed={summary.processed}",
            f"failures={summary.failures}",
            f"labels={summary.label_counts}",
        )

        all_counts = db.llm_label_counts(model=args.model)
        print(f"Current label totals for model={args.model}: {all_counts}")

        if args.export_real:
            exported = db.export_llm_real_conjectures(
                model=args.model,
                output_dir=args.output_dir,
                min_confidence=args.min_confidence,
            )
            print("Exported model-filtered real conjectures:")
            for artifact in exported.values():
                print(f"  - {artifact}")
        return 0
    finally:
        db.close()


def main(argv: list[str] | None = None) -> int:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    parser = build_parser()
    args = parser.parse_args(argv)
    handler: Callable[[argparse.Namespace], int] = args.handler
    return handler(args)


if __name__ == "__main__":
    raise SystemExit(main())
