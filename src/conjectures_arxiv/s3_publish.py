from __future__ import annotations

from datetime import datetime
from pathlib import Path

import boto3
from botocore.exceptions import ClientError


def _normalize_prefix(prefix: str) -> str:
    cleaned = prefix.strip("/")
    return f"{cleaned}/" if cleaned else ""


class S3Publisher:
    def __init__(self, bucket: str, prefix: str = "", client=None) -> None:
        self.bucket = bucket
        self.prefix = _normalize_prefix(prefix)
        self.client = client or boto3.client("s3")

    def ensure_bucket(self, region: str = "") -> None:
        try:
            self.client.head_bucket(Bucket=self.bucket)
            return
        except ClientError as exc:
            code = str(exc.response.get("Error", {}).get("Code", ""))
            if code not in {"404", "NoSuchBucket", "NotFound"}:
                raise

        kwargs: dict[str, object] = {"Bucket": self.bucket}
        if region and region != "us-east-1":
            kwargs["CreateBucketConfiguration"] = {"LocationConstraint": region}
        self.client.create_bucket(**kwargs)

    def upload_file(self, local_path: str | Path, key: str) -> str:
        path = Path(local_path)
        self.client.upload_file(str(path), self.bucket, key)
        return f"s3://{self.bucket}/{key}"

    def upload_artifacts(self, db_path: str | Path, exports_dir: str | Path) -> list[str]:
        db_path = Path(db_path)
        exports_dir = Path(exports_dir)

        timestamp = datetime.utcnow().strftime("%Y%m%dT%H%M%SZ")
        run_prefix = f"{self.prefix}runs/{timestamp}/"
        latest_prefix = f"{self.prefix}latest/"

        uploaded: list[str] = []

        run_db_key = f"{run_prefix}{db_path.name}"
        latest_db_key = f"{latest_prefix}{db_path.name}"
        uploaded.append(self.upload_file(db_path, run_db_key))
        uploaded.append(self.upload_file(db_path, latest_db_key))

        if exports_dir.exists():
            for child in sorted(exports_dir.rglob("*")):
                if not child.is_file():
                    continue
                relative = child.relative_to(exports_dir).as_posix()
                run_key = f"{run_prefix}{relative}"
                latest_key = f"{latest_prefix}{relative}"
                uploaded.append(self.upload_file(child, run_key))
                uploaded.append(self.upload_file(child, latest_key))

        return uploaded
