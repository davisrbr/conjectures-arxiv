from __future__ import annotations

from datetime import UTC, datetime
import os
from pathlib import Path
from typing import Any


def default_hf_commit_message() -> str:
    timestamp = datetime.now(UTC).strftime("%Y-%m-%d %H:%M:%S UTC")
    return f"Refresh conjectures dataset ({timestamp})"


class HuggingFacePublisher:
    def __init__(self, token: str | None = None, api: Any | None = None) -> None:
        self.token = token or os.getenv("HF_TOKEN") or os.getenv("HUGGINGFACE_HUB_TOKEN")
        self.api = api

    def upload_dataset(
        self,
        *,
        dataset_dir: str | Path,
        repo_id: str,
        private: bool = False,
        revision: str = "main",
        commit_message: str = "",
    ) -> str:
        dataset_path = Path(dataset_dir)
        if not dataset_path.exists():
            raise FileNotFoundError(f"Dataset directory does not exist: {dataset_path}")
        if not (dataset_path / "README.md").exists():
            raise FileNotFoundError(f"Dataset card is missing: {dataset_path / 'README.md'}")

        api = self.api or self._build_api()
        api.create_repo(repo_id=repo_id, repo_type="dataset", private=private, exist_ok=True)
        api.upload_folder(
            repo_id=repo_id,
            repo_type="dataset",
            folder_path=str(dataset_path),
            path_in_repo="",
            revision=revision,
            commit_message=commit_message or default_hf_commit_message(),
        )
        return f"https://huggingface.co/datasets/{repo_id}"

    def _build_api(self):  # noqa: ANN202
        try:
            from huggingface_hub import HfApi
        except ModuleNotFoundError as exc:
            raise RuntimeError(
                "huggingface_hub is required for Hugging Face uploads. "
                "Install it with `pip install -e '.[huggingface]'`."
            ) from exc
        return HfApi(token=self.token)
