from conjectures_arxiv.hf_publish import HuggingFacePublisher


class FakeHfApi:
    def __init__(self) -> None:
        self.created: list[dict[str, object]] = []
        self.uploaded: list[dict[str, object]] = []

    def create_repo(self, **kwargs) -> None:  # noqa: ANN003
        self.created.append(kwargs)

    def upload_folder(self, **kwargs) -> None:  # noqa: ANN003
        self.uploaded.append(kwargs)


def test_upload_dataset_creates_repo_and_uploads_folder(tmp_path) -> None:
    (tmp_path / "README.md").write_text("# Dataset\n", encoding="utf-8")
    data_dir = tmp_path / "data"
    data_dir.mkdir()
    (data_dir / "conjectures.jsonl").write_text("{}\n", encoding="utf-8")

    api = FakeHfApi()
    publisher = HuggingFacePublisher(token="hf_test_token", api=api)
    url = publisher.upload_dataset(
        dataset_dir=tmp_path,
        repo_id="alice/conjectures-arxiv",
        private=True,
        revision="main",
        commit_message="Refresh dataset",
    )

    assert url == "https://huggingface.co/datasets/alice/conjectures-arxiv"
    assert api.created == [
        {
            "repo_id": "alice/conjectures-arxiv",
            "repo_type": "dataset",
            "private": True,
            "exist_ok": True,
        }
    ]
    assert api.uploaded == [
        {
            "repo_id": "alice/conjectures-arxiv",
            "repo_type": "dataset",
            "folder_path": str(tmp_path),
            "path_in_repo": "",
            "revision": "main",
            "commit_message": "Refresh dataset",
        }
    ]


def test_upload_dataset_requires_prepared_readme(tmp_path) -> None:
    api = FakeHfApi()
    publisher = HuggingFacePublisher(api=api)

    try:
        publisher.upload_dataset(dataset_dir=tmp_path, repo_id="alice/conjectures-arxiv")
    except FileNotFoundError as exc:
        assert "README.md" in str(exc)
    else:
        raise AssertionError("Expected FileNotFoundError when README.md is missing")
