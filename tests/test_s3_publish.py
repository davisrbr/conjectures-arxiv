from __future__ import annotations

from botocore.exceptions import ClientError

from conjectures_arxiv.s3_publish import S3Publisher


class FakeS3Client:
    def __init__(self, head_bucket_error: Exception | None = None):
        self.head_bucket_error = head_bucket_error
        self.created: list[dict] = []
        self.uploads: list[tuple[str, str, str]] = []

    def head_bucket(self, Bucket: str):
        del Bucket
        if self.head_bucket_error is not None:
            raise self.head_bucket_error

    def create_bucket(self, **kwargs):
        self.created.append(kwargs)

    def upload_file(self, local_path: str, bucket: str, key: str):
        self.uploads.append((local_path, bucket, key))



def test_ensure_bucket_creates_when_missing_non_us_east_1() -> None:
    err = ClientError({"Error": {"Code": "404", "Message": "not found"}}, "HeadBucket")
    client = FakeS3Client(head_bucket_error=err)
    publisher = S3Publisher(bucket="my-bucket", prefix="dataset", client=client)

    publisher.ensure_bucket(region="us-west-2")

    assert client.created == [
        {
            "Bucket": "my-bucket",
            "CreateBucketConfiguration": {"LocationConstraint": "us-west-2"},
        }
    ]


def test_upload_artifacts_writes_run_and_latest(tmp_path) -> None:
    db_path = tmp_path / "conjectures.sqlite"
    db_path.write_text("db", encoding="utf-8")

    exports_dir = tmp_path / "exports"
    exports_dir.mkdir()
    (exports_dir / "conjectures.jsonl").write_text("{}\n", encoding="utf-8")

    client = FakeS3Client()
    publisher = S3Publisher(bucket="my-bucket", prefix="dataset", client=client)
    uploaded = publisher.upload_artifacts(db_path=db_path, exports_dir=exports_dir)

    assert len(uploaded) == 4
    keys = [item[2] for item in client.uploads]
    assert any(key.endswith("/conjectures.sqlite") and "/runs/" in key for key in keys)
    assert "dataset/latest/conjectures.sqlite" in keys
    assert any(key.endswith("/conjectures.jsonl") and "/runs/" in key for key in keys)
    assert "dataset/latest/conjectures.jsonl" in keys
