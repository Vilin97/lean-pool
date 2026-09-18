"""Validate exact-tree build reuse and safe fallback for unavailable artifacts."""

from __future__ import annotations

import io
import json
import subprocess
import tarfile
from pathlib import Path

import pytest

from lean_pool import ci_artifacts


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create a committed source tree with an ignored synthetic Lake build."""
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (tmp_path / name).write_text(name)
    (tmp_path / ".gitignore").write_text(".lake/\n*.tar.gz\n")
    (tmp_path / ".lake/build/lib/lean").mkdir(parents=True)
    (tmp_path / ".lake/build/lib/lean/LeanPool.olean").write_bytes(b"compiled")
    for command in (
        ["init", "-q"],
        ["add", "."],
        [
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "initial",
        ],
    ):
        subprocess.run(["git", *command], cwd=tmp_path, check=True)
    return tmp_path


def test_build_round_trip(repository: Path) -> None:
    """Matching output replaces the old build completely, including removed modules."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    output = repository / ".lake/build/lib/lean/LeanPool.olean"
    output.write_bytes(b"old")
    stale = output.with_name("Removed.olean")
    stale.touch()
    assert ci_artifacts.restore_build(repository, archive)
    assert output.read_bytes() == b"compiled"
    assert not stale.exists()


def test_mismatched_configuration_preserves_current_build(repository: Path) -> None:
    """An incompatible toolchain never replaces the fallback build."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    (repository / "lean-toolchain").write_text("other version")
    assert not ci_artifacts.restore_build(repository, archive)
    assert (
        repository / ".lake/build/lib/lean/LeanPool.olean"
    ).read_bytes() == b"compiled"


def test_mismatched_tree_preserves_current_build(repository: Path) -> None:
    """A different source tree cannot reuse a same-toolchain artifact."""
    archive = repository / "build.tar.gz"
    ci_artifacts.pack_build(repository, archive)
    (repository / "Added.lean").write_text("-- new source\n")
    subprocess.run(["git", "add", "Added.lean"], cwd=repository, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "commit",
            "-qm",
            "change",
        ],
        cwd=repository,
        check=True,
    )
    assert not ci_artifacts.restore_build(repository, archive)


def test_pack_rejects_dirty_checkout(repository: Path) -> None:
    """The producer cannot label modified build inputs with the committed tree."""
    (repository / "lakefile.toml").write_text("changed options")
    with pytest.raises(subprocess.CalledProcessError):
        ci_artifacts.pack_build(repository, repository / "build.tar.gz")


@pytest.mark.parametrize(
    ("name", "kind"),
    [
        ("../escape", tarfile.REGTYPE),
        ("/tmp/escape", tarfile.REGTYPE),
        (".lake/build/../../escape", tarfile.REGTYPE),
        ("LeanPool.lean", tarfile.REGTYPE),
        (".lake/build/link", tarfile.SYMTYPE),
        (".lake/build/link", tarfile.LNKTYPE),
    ],
)
def test_unexpected_archive_member_rejected(repository: Path, name: str, kind) -> None:
    """No archive path, symlink, or hardlink can escape the build directory."""
    destination = repository / "build.tar.gz"
    with tarfile.open(destination, "w:gz") as archive:
        payload = json.dumps(ci_artifacts.build_identity(repository)).encode()
        manifest = tarfile.TarInfo(ci_artifacts.MANIFEST_NAME)
        manifest.size = len(payload)
        archive.addfile(manifest, io.BytesIO(payload))
        member = tarfile.TarInfo(name)
        member.type = kind
        member.linkname = "../../../escape"
        archive.addfile(member)
    with pytest.raises(ValueError, match="Unexpected build archive member"):
        ci_artifacts.restore_build(repository, destination)
    assert (repository / ".lake/build/lib/lean/LeanPool.olean").exists()


def test_missing_run_falls_back(repository: Path, monkeypatch) -> None:
    """Docs-only changes and disabled CI retain the regular Lake build path."""
    monkeypatch.setattr(ci_artifacts, "matching_run", lambda *args: None)
    assert not ci_artifacts.reuse_build(repository, "owner/repo", "head", "push", 0)


def test_api_error_falls_back(repository: Path, monkeypatch) -> None:
    """Artifact API errors are an optimization miss rather than a docs failure."""

    def unavailable(*args):
        raise subprocess.CalledProcessError(1, "gh")

    monkeypatch.setattr(ci_artifacts, "matching_run", unavailable)
    assert not ci_artifacts.reuse_build(repository, "owner/repo", "head", "push", 0)


def test_matching_run_queries_exact_head_and_event(monkeypatch) -> None:
    """Concurrent PR/push runs cannot accidentally select another workflow's outputs."""
    endpoints = []

    def response(endpoint):
        endpoints.append(endpoint)
        return {"workflow_runs": [{"id": 1}, {"id": 5}]}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.matching_run("owner/repo", "abc123", "pull_request") == {
        "id": 5
    }
    assert "lean_action_ci.yml/runs?head_sha=abc123&event=pull_request&" in endpoints[0]


@pytest.mark.parametrize("status", ["completed", "in_progress"])
def test_wait_ends_on_completed_run_or_deadline(monkeypatch, status: str) -> None:
    """Missing artifacts cannot cause an unbounded wait."""

    def response(endpoint):
        return {"artifacts": []} if "/artifacts?" in endpoint else {"status": status}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.wait_for_artifact("owner/repo", {"id": 1}, 0) is None


def test_artifact_available_before_quality_finishes(monkeypatch) -> None:
    """Compilation output can be consumed while later checks are still running."""

    def response(endpoint):
        assert "/artifacts?" in endpoint
        return {"artifacts": [{"id": 8, "name": "lean-pool-build", "expired": False}]}

    monkeypatch.setattr(ci_artifacts, "github_json", response)
    assert ci_artifacts.wait_for_artifact("owner/repo", {"id": 1}, 0) == 8
