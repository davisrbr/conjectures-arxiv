from __future__ import annotations

import argparse
from datetime import date, timedelta
import json
import logging
from pathlib import Path
import time
from typing import Callable

from .database import Database
from .hf_publish import HuggingFacePublisher
from .llm_filter import GPT5MiniConjectureFilter, LLMFilterRunner, SourceContextProvider
from .pipeline import IngestionPipeline
from .s3_publish import S3Publisher
from .solver import (
    DEFAULT_MAX_OUTPUT_TOKENS,
    DEFAULT_REASONING_EFFORT,
    OpenAIConjectureSolver,
    SOLVER_PROMPT_VERSION,
    TERMINAL_RESPONSE_STATUSES,
)


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

    export_hf_parser = subparsers.add_parser("export-hf", help="Build a license-filtered Hugging Face dataset snapshot")
    export_hf_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    export_hf_parser.add_argument("--output-dir", default="data/huggingface_dataset")
    export_hf_parser.add_argument("--repo-id", default="")
    export_hf_parser.set_defaults(handler=cmd_export_hf)

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
    filter_parser.add_argument("--context-window-lines", type=int, default=20)
    filter_parser.add_argument("--batch-size", type=int, default=8)
    filter_parser.add_argument("--sleep-seconds", type=float, default=0.0)
    filter_parser.add_argument("--output-dir", default="data/exports")
    filter_parser.add_argument("--export-real", action="store_true")
    filter_parser.add_argument("--min-confidence", type=float, default=0.0)
    filter_parser.set_defaults(handler=cmd_filter_llm)

    solve_parser = subparsers.add_parser("solve-llm", help="Run autonomous solver attempts with GPT-5.4 + web search")
    solve_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    solve_parser.add_argument("--label-model", default="gpt-5-mini")
    solve_parser.add_argument("--solver-model", default="gpt-5.4")
    solve_parser.add_argument("--conjecture-id", type=int, default=None)
    solve_parser.add_argument("--limit", type=int, default=1)
    solve_parser.add_argument("--min-confidence", type=float, default=0.0)
    solve_parser.add_argument("--min-viability", type=float, default=0.0)
    solve_parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    solve_parser.add_argument("--search-context-size", default="high")
    solve_parser.add_argument("--max-output-tokens", type=int, default=DEFAULT_MAX_OUTPUT_TOKENS)
    solve_parser.add_argument("--max-tool-calls", type=int, default=32)
    solve_parser.add_argument("--poll-interval-seconds", type=float, default=10.0)
    solve_parser.add_argument("--wait", action="store_true")
    solve_parser.add_argument("--response-id", default="")
    solve_parser.set_defaults(handler=cmd_solve_llm)

    solve_status_parser = subparsers.add_parser("solve-status", help="Inspect and export solver attempt statuses")
    solve_status_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    solve_status_parser.add_argument("--response-id", default="")
    solve_status_parser.add_argument("--conjecture-id", type=int, default=None)
    solve_status_parser.add_argument("--status", default="")
    solve_status_parser.add_argument("--limit", type=int, default=20)
    solve_status_parser.add_argument("--refresh-open", action="store_true")
    solve_status_parser.add_argument("--output-dir", default="")
    solve_status_parser.set_defaults(handler=cmd_solve_status)

    publish_hf_parser = subparsers.add_parser("publish-hf", help="Build and optionally upload a Hugging Face dataset snapshot")
    publish_hf_parser.add_argument("--db-path", default="data/conjectures.sqlite")
    publish_hf_parser.add_argument("--output-dir", default="data/huggingface_dataset")
    publish_hf_parser.add_argument("--repo-id", required=True)
    publish_hf_parser.add_argument("--token", default="")
    publish_hf_parser.add_argument("--private", action="store_true")
    publish_hf_parser.add_argument("--revision", default="main")
    publish_hf_parser.add_argument("--commit-message", default="")
    publish_hf_parser.add_argument("--dry-run", action="store_true")
    publish_hf_parser.set_defaults(handler=cmd_publish_hf)

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


def cmd_export_hf(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    try:
        db.init_schema()
        exported = db.export_huggingface_dataset(args.output_dir, repo_id=args.repo_id)
    finally:
        db.close()

    _print_hf_export_summary(exported)
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


def cmd_publish_hf(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    try:
        db.init_schema()
        exported = db.export_huggingface_dataset(args.output_dir, repo_id=args.repo_id)
    finally:
        db.close()

    _print_hf_export_summary(exported)
    if args.dry_run:
        print(f"Dry run: dataset snapshot prepared for https://huggingface.co/datasets/{args.repo_id}")
        return 0

    publisher = HuggingFacePublisher(token=args.token or None)
    url = publisher.upload_dataset(
        dataset_dir=Path(args.output_dir),
        repo_id=args.repo_id,
        private=args.private,
        revision=args.revision,
        commit_message=args.commit_message,
    )
    print(f"Uploaded dataset snapshot: {url}")
    return 0


def _print_hf_export_summary(exported: dict[str, Path]) -> None:
    manifest = json.loads(exported["hf_manifest_json"].read_text(encoding="utf-8"))
    print(
        "Prepared Hugging Face dataset snapshot:",
        f"papers={manifest['papers_total']}",
        f"conjectures={manifest['conjectures_total']}",
        f"published_text={manifest['conjectures_with_public_text']}",
        f"withheld_text={manifest['conjectures_withheld_text']}",
        f"latest_labels={manifest['conjectures_with_latest_label']}",
        f"policy={manifest['publication_policy_version']}",
    )
    print("Prepared artifacts:")
    for artifact in exported.values():
        print(f"  - {artifact}")


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


def cmd_solve_llm(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    db.init_schema()

    try:
        try:
            solver = OpenAIConjectureSolver(model=args.solver_model)
        except RuntimeError as exc:
            print(f"LLM solver setup failed: {exc}")
            return 1

        if args.response_id:
            snapshot = solver.retrieve(response_id=args.response_id)
            db.update_solver_attempt(
                args.response_id,
                status=snapshot.status,
                output_text=snapshot.output_text,
                sources_json=snapshot.sources_json,
                raw_response_json=snapshot.raw_response_json,
                error_json=snapshot.error_json,
                completed_at=snapshot.completed_at,
            )
            _print_solver_snapshot(
                response_id=args.response_id,
                conjecture_id=None,
                status=snapshot.status,
                output_text=snapshot.output_text,
                completed_at=snapshot.completed_at,
                error_json=snapshot.error_json,
            )
            return 0 if snapshot.status == "completed" else 1

        records = db.list_real_conjectures_for_solver(
            label_model=args.label_model,
            limit=args.limit,
            min_confidence=args.min_confidence,
            min_viability=args.min_viability,
            conjecture_id=args.conjecture_id,
        )
        if not records:
            print("No matching conjectures found for solver run.")
            return 1

        context_provider = SourceContextProvider()
        exit_code = 0
        for record in records:
            context_window = ""
            try:
                context_window = context_provider.get_context(record, window_lines=20)
            except Exception as exc:  # noqa: BLE001
                print(
                    "Context fetch failed:",
                    f"conjecture_id={record['conjecture_id']}",
                    f"arxiv_id={record['arxiv_id']}",
                    f"error={exc}",
                )

            prompt = solver.build_prompt(record=record, context_window=context_window)
            try:
                snapshot = solver.submit(
                    prompt=prompt,
                    record=record,
                    reasoning_effort=args.reasoning_effort,
                    search_context_size=args.search_context_size,
                    max_output_tokens=args.max_output_tokens,
                    max_tool_calls=args.max_tool_calls,
                )
            except Exception as exc:  # noqa: BLE001
                print(
                    "Solver submission failed:",
                    f"conjecture_id={record['conjecture_id']}",
                    f"arxiv_id={record['arxiv_id']}",
                    f"error={exc}",
                )
                exit_code = 1
                continue

            db.create_solver_attempt(
                conjecture_id=int(record["conjecture_id"]),
                label_model=args.label_model,
                solver_model=args.solver_model,
                prompt_version=SOLVER_PROMPT_VERSION,
                reasoning_effort=args.reasoning_effort,
                search_context_size=args.search_context_size,
                response_id=snapshot.response_id,
                status=snapshot.status,
                instructions=prompt.instructions,
                prompt_text=prompt.prompt_text,
                output_text=snapshot.output_text,
                sources_json=snapshot.sources_json,
                raw_response_json=snapshot.raw_response_json,
                error_json=snapshot.error_json,
                completed_at=snapshot.completed_at,
            )

            _print_solver_snapshot(
                response_id=snapshot.response_id,
                conjecture_id=int(record["conjecture_id"]),
                status=snapshot.status,
                output_text=snapshot.output_text,
                completed_at=snapshot.completed_at,
                error_json=snapshot.error_json,
            )

            if not args.wait or snapshot.status in TERMINAL_RESPONSE_STATUSES:
                if snapshot.status in {"failed", "cancelled", "incomplete"}:
                    exit_code = 1
                continue

            snapshot = _poll_solver_attempt(
                solver=solver,
                db=db,
                response_id=snapshot.response_id,
                poll_interval_seconds=args.poll_interval_seconds,
            )
            _print_solver_snapshot(
                response_id=snapshot.response_id,
                conjecture_id=int(record["conjecture_id"]),
                status=snapshot.status,
                output_text=snapshot.output_text,
                completed_at=snapshot.completed_at,
                error_json=snapshot.error_json,
            )
            if snapshot.status in {"failed", "cancelled", "incomplete"}:
                exit_code = 1

        return exit_code
    finally:
        db.close()


def cmd_solve_status(args: argparse.Namespace) -> int:
    db = Database(args.db_path)
    db.init_schema()

    try:
        records = db.list_solver_attempts(
            limit=args.limit,
            response_id=args.response_id or None,
            conjecture_id=args.conjecture_id,
            status=args.status or None,
        )
        if args.refresh_open and records:
            try:
                solver = OpenAIConjectureSolver()
            except RuntimeError as exc:
                print(f"LLM solver setup failed: {exc}")
                return 1
            refreshed, refresh_failures = _refresh_open_attempts(db=db, solver=solver, records=records)
            print(
                "Refreshed solver attempts:",
                f"updated={refreshed}",
                f"failures={refresh_failures}",
            )
            records = db.list_solver_attempts(
                limit=args.limit,
                response_id=args.response_id or None,
                conjecture_id=args.conjecture_id,
                status=args.status or None,
            )

        _print_solver_status_records(records)

        if args.output_dir:
            exported = db.export_solver_attempts(
                output_dir=args.output_dir,
                limit=args.limit,
                response_id=args.response_id or None,
                conjecture_id=args.conjecture_id,
                status=args.status or None,
            )
            print("Exported solver attempt artifacts:")
            for artifact in exported.values():
                print(f"  - {artifact}")
        return 0
    finally:
        db.close()


def _poll_solver_attempt(
    *,
    solver: OpenAIConjectureSolver,
    db: Database,
    response_id: str,
    poll_interval_seconds: float,
):
    while True:
        snapshot = solver.retrieve(response_id=response_id)
        db.update_solver_attempt(
            response_id,
            status=snapshot.status,
            output_text=snapshot.output_text,
            sources_json=snapshot.sources_json,
            raw_response_json=snapshot.raw_response_json,
            error_json=snapshot.error_json,
            completed_at=snapshot.completed_at,
        )
        if snapshot.status in TERMINAL_RESPONSE_STATUSES:
            return snapshot
        print(f"Polling response_id={response_id} status={snapshot.status}")
        time.sleep(poll_interval_seconds)


def _refresh_open_attempts(
    *,
    db: Database,
    solver: OpenAIConjectureSolver,
    records: list[dict[str, object]],
) -> tuple[int, int]:
    refreshed = 0
    failures = 0
    for record in records:
        status = str(record.get("status", ""))
        if status in TERMINAL_RESPONSE_STATUSES:
            continue
        response_id = str(record.get("response_id", "")).strip()
        if not response_id:
            continue
        try:
            snapshot = solver.retrieve(response_id=response_id)
        except Exception as exc:  # noqa: BLE001
            print(f"Refresh failed: response_id={response_id} error={exc}")
            failures += 1
            continue

        db.update_solver_attempt(
            response_id,
            status=snapshot.status,
            output_text=snapshot.output_text,
            sources_json=snapshot.sources_json,
            raw_response_json=snapshot.raw_response_json,
            error_json=snapshot.error_json,
            completed_at=snapshot.completed_at,
        )
        refreshed += 1
    return refreshed, failures


def _print_solver_status_records(records: list[dict[str, object]]) -> None:
    if not records:
        print("No solver attempts found.")
        return

    counts: dict[str, int] = {}
    for record in records:
        status = str(record.get("status", ""))
        counts[status] = counts.get(status, 0) + 1

    print(
        "Solver attempt summary:",
        f"total={len(records)}",
        f"statuses={counts}",
    )
    for record in records:
        line = (
            f"attempt_id={record['attempt_id']} "
            f"conjecture_id={record['conjecture_id']} "
            f"status={record['status']} "
            f"response_id={record['response_id']} "
            f"viability={record['viability_score']:.2f} "
            f"interestingness={record['interestingness_score']:.2f} "
            f"title={record['title']}"
        )
        completed_at = str(record.get("completed_at", "") or "").strip()
        if completed_at:
            line += f" completed_at={completed_at}"
        output_length = int(record.get("output_length", 0) or 0)
        if output_length:
            line += f" output_len={output_length}"
        reason = _solver_status_reason(str(record.get("status", "")), str(record.get("error_json", "")))
        if reason:
            line += f" note={reason}"
        print(line)


def _print_solver_snapshot(
    *,
    response_id: str,
    conjecture_id: int | None,
    status: str,
    output_text: str,
    completed_at: str | None,
    error_json: str,
) -> None:
    prefix = f"Solver response: response_id={response_id}"
    if conjecture_id is not None:
        prefix += f" conjecture_id={conjecture_id}"
    prefix += f" status={status}"
    if completed_at:
        prefix += f" completed_at={completed_at}"
    print(prefix)
    if output_text.strip():
        print(output_text.strip())
        return

    message = _solver_failure_message(status=status, error_json=error_json)
    if message:
        print(message)


def _solver_status_reason(status: str, error_json: str) -> str:
    message = _solver_failure_message(status=status, error_json=error_json)
    if not message:
        return ""
    if message.endswith("."):
        return message[:-1]
    return message


def _solver_failure_message(*, status: str, error_json: str) -> str:
    if not error_json.strip():
        if status == "incomplete":
            return "Solver ended incomplete with no visible output."
        if status in {"failed", "cancelled"}:
            return f"Solver ended with status={status}."
        return ""

    try:
        payload = json.loads(error_json)
    except json.JSONDecodeError:
        return f"Solver ended with status={status}."

    if status == "incomplete":
        reason = ""
        incomplete_details = payload.get("incomplete_details")
        if isinstance(incomplete_details, dict):
            reason = str(incomplete_details.get("reason", "")).strip()
        if reason:
            return f"Solver ended incomplete: reason={reason}. No visible output was captured."
        return "Solver ended incomplete with no visible output."

    error = payload.get("error")
    if isinstance(error, dict):
        message = str(error.get("message", "")).strip()
        code = str(error.get("code", "")).strip()
        if message and code:
            return f"Solver ended with status={status}: {code}: {message}"
        if message:
            return f"Solver ended with status={status}: {message}"
    return f"Solver ended with status={status}."


def main(argv: list[str] | None = None) -> int:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    parser = build_parser()
    args = parser.parse_args(argv)
    handler: Callable[[argparse.Namespace], int] = args.handler
    return handler(args)


if __name__ == "__main__":
    raise SystemExit(main())
