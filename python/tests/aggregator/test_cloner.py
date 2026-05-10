"""Tests for the candidate repo cloner."""

from __future__ import annotations

import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

from lean_pool.aggregator.cloner import (
    _dedupe_by_key,
    _repo_url,
    _target_for_key,
    clone_all,
    clone_package,
)
from lean_pool.aggregator.reservoir import Package


def _package(
    *,
    full_name: str = "acme/demo",
    repo_url: str | None = "https://github.com/acme/demo",
) -> Package:
    """Build a minimal package dict shaped like a Reservoir entry."""
    owner, name = full_name.split("/")
    sources = [{"repoUrl": repo_url}] if repo_url else []
    return {  # type: ignore[typeddict-item]
        "name": name,
        "owner": owner,
        "fullName": full_name,
        "sources": sources,
    }


def test_repo_url_prefers_repo_url_then_git_url() -> None:
    """``repoUrl`` wins; ``gitUrl`` is the fallback when missing."""
    with_repo = _package(repo_url="https://github.com/acme/demo")
    only_git: Package = {  # type: ignore[typeddict-item]
        "fullName": "acme/demo",
        "sources": [{"gitUrl": "https://github.com/acme/demo.git"}],
    }
    no_sources: Package = {"fullName": "acme/demo"}  # type: ignore[typeddict-item]

    assert _repo_url(with_repo) == "https://github.com/acme/demo"
    assert _repo_url(only_git) == "https://github.com/acme/demo.git"
    assert _repo_url(no_sources) is None


def test_target_for_key_splits_owner_and_name(tmp_path: Path) -> None:
    """The canonical key maps to ``<clones_dir>/<owner>/<name>/``."""
    assert _target_for_key(tmp_path, "acme/demo") == tmp_path / "acme" / "demo"


def test_dedupe_by_key_keeps_first_occurrence() -> None:
    """Two URLs that differ only by case or ``.lean`` suffix collapse to one."""
    first = _package(full_name="Acme/Demo", repo_url="https://github.com/Acme/Demo")
    second = _package(
        full_name="acme/demo.lean", repo_url="https://github.com/acme/Demo.lean"
    )
    third = _package(full_name="other/repo", repo_url="https://github.com/other/repo")

    deduped = _dedupe_by_key([first, second, third])

    assert [p["fullName"] for p in deduped] == ["Acme/Demo", "other/repo"]


def test_clone_package_invokes_git_with_blobless_flags(tmp_path: Path) -> None:
    """``clone_package`` runs git with the expected shallow blobless args."""
    package = _package()

    with patch("lean_pool.aggregator.cloner.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0)
        result = clone_package(package, tmp_path)

    assert result == tmp_path / "acme" / "demo"
    args, kwargs = mock_run.call_args
    cmd = args[0]
    assert cmd[:2] == ["git", "clone"]
    assert "--depth=1" in cmd
    assert "--filter=blob:none" in cmd
    assert cmd[-2] == "https://github.com/acme/demo"
    assert cmd[-1].endswith("acme/demo")
    assert kwargs.get("check") is True


def test_clone_package_skips_when_target_exists(tmp_path: Path) -> None:
    """An existing clone directory short-circuits before ``git`` runs."""
    package = _package()
    existing = tmp_path / "acme" / "demo"
    existing.mkdir(parents=True)

    with patch("lean_pool.aggregator.cloner.subprocess.run") as mock_run:
        result = clone_package(package, tmp_path)

    assert result == existing
    mock_run.assert_not_called()


def test_clone_package_returns_none_without_url(tmp_path: Path) -> None:
    """Packages without a repo URL are skipped, not cloned."""
    package = _package(repo_url=None)

    with patch("lean_pool.aggregator.cloner.subprocess.run") as mock_run:
        result = clone_package(package, tmp_path)

    assert result is None
    mock_run.assert_not_called()


def test_clone_package_cleans_partial_dir_on_failure(tmp_path: Path) -> None:
    """A failed clone leaves no stray directory behind."""
    package = _package()

    def _fake_run(*args: object, **kwargs: object) -> None:
        # Simulate git creating the dest dir, then failing mid-clone.
        target = tmp_path / "acme" / "demo"
        target.mkdir(parents=True, exist_ok=True)
        raise subprocess.CalledProcessError(
            returncode=128,
            cmd=args[0],
            stderr="fatal: repository not found",
        )

    with patch("lean_pool.aggregator.cloner.subprocess.run", side_effect=_fake_run):
        result = clone_package(package, tmp_path)

    assert result is None
    assert not (tmp_path / "acme" / "demo").exists()


def test_clone_all_dedupes_and_counts(tmp_path: Path) -> None:
    """Run summary counts cloned, cached, and failed buckets correctly."""
    duplicate_a = _package(
        full_name="Acme/Demo", repo_url="https://github.com/Acme/Demo"
    )
    duplicate_b = _package(
        full_name="acme/demo", repo_url="https://github.com/acme/demo"
    )
    cached = _package(
        full_name="cached/repo", repo_url="https://github.com/cached/repo"
    )
    failing = _package(full_name="bad/repo", repo_url="https://github.com/bad/repo")
    no_url = _package(full_name="missing/url", repo_url=None)

    # Pre-create the cached entry so it shows up in already_present.
    (tmp_path / "cached" / "repo").mkdir(parents=True)

    def _fake_run(args: list[str], **_: object) -> MagicMock:
        url = args[-2]
        if "bad/repo" in url:
            raise subprocess.CalledProcessError(
                returncode=128, cmd=args, stderr="fatal: not found"
            )
        Path(args[-1]).mkdir(parents=True, exist_ok=True)
        return MagicMock(returncode=0)

    with patch("lean_pool.aggregator.cloner.subprocess.run", side_effect=_fake_run):
        cloned_now, already_present, failed = clone_all(
            [duplicate_a, duplicate_b, cached, failing, no_url],
            tmp_path,
            parallelism=2,
        )

    assert cloned_now == 1  # the deduped Acme/Demo pair clones once
    assert already_present == 1  # cached/repo
    assert failed == 2  # bad/repo + missing/url
