"""Tests for PR project metadata advisory comments."""

from __future__ import annotations

import base64
import json
import subprocess

import pytest

from lean_pool import pr_advisory
from lean_pool.pr_advisory import (
    ADVISORY_MARKER,
    AdvisoryRow,
    ProjectEntry,
    UpstreamMetadata,
    fetch_upstream_metadata,
    list_open_pr_numbers,
    main,
    post_sticky_comment,
    project_changes,
    render_comment,
    update_pr_advisory,
)


def _projects_yaml(*entries: str) -> str:
    """Build a minimal projects.yml document."""
    return "projects:\n" + "\n".join(entries)


def _project(
    slug: str,
    *,
    title: str = "Demo",
    license_name: str = "MIT",
    github_repo: str = "acme/demo",
) -> str:
    """Build one YAML project entry."""
    return (
        f"  - slug: {slug}\n"
        f"    title: {title}\n"
        "    source:\n"
        f"      github_repo: {github_repo}\n"
        f"    license: {license_name}\n"
    )


def test_project_changes_finds_added_and_changed_entries() -> None:
    """Project detection compares head projects.yml with the base version."""
    base = _projects_yaml(_project("old", license_name="MIT"))
    head = _projects_yaml(
        _project("new", license_name="Apache-2.0"),
        _project("old", license_name="Apache-2.0"),
    )

    changes = project_changes(base, head)

    assert [(change.kind, change.project.slug) for change in changes] == [
        ("added", "new"),
        ("changed", "old"),
    ]


def test_render_comment_includes_marker_and_metadata_table() -> None:
    """The advisory comment is sticky and includes the requested metadata."""
    body = render_comment(
        [
            AdvisoryRow(
                project=ProjectEntry(
                    slug="demo",
                    title="Demo",
                    license="MIT",
                    github_repo="acme/demo",
                ),
                change_kind="added",
                metadata=UpstreamMetadata(
                    license="Apache-2.0",
                    last_commit_date="2026-06-20",
                    lean_version="v4.30.0",
                    url="https://github.com/acme/demo",
                ),
            )
        ]
    )

    assert body.startswith(ADVISORY_MARKER)
    assert "| `demo` | added | [acme/demo](https://github.com/acme/demo) |" in body
    assert "`Apache-2.0`" in body
    assert "`2026-06-20`" in body
    assert "`v4.30.0`" in body


def test_render_comment_handles_pr_without_project_changes() -> None:
    """Non-content PRs still get a clear advisory comment."""
    body = render_comment([])

    assert body.startswith(ADVISORY_MARKER)
    assert "No added or changed `LeanPool/projects.yml`" in body


def test_list_open_pr_numbers_does_not_filter_drafts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The open PR listing asks GitHub for every open PR."""
    calls: list[tuple[str, ...]] = []

    def fake_run_gh(*args: str, stdin: str | None = None) -> str:
        calls.append(args)
        return "2\n3\n"

    monkeypatch.setattr(pr_advisory, "run_gh", fake_run_gh)

    assert list_open_pr_numbers("acme/pool") == [2, 3]
    assert "state=open" in calls[0][1]
    assert "--paginate" in calls[0]


def test_fetch_upstream_metadata_reads_license_commit_and_toolchain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Upstream metadata is fetched from the source repository."""
    toolchain = base64.b64encode(b"leanprover/lean4:v4.30.0\n").decode()

    responses = {
        "repos/acme/demo": {
            "default_branch": "main",
            "html_url": "https://github.com/acme/demo",
            "license": {"spdx_id": "Apache-2.0"},
        },
        "repos/acme/demo/commits/main": {
            "commit": {"committer": {"date": "2026-06-20T12:00:00Z"}}
        },
        "repos/acme/demo/contents/lean-toolchain?ref=main": {
            "encoding": "base64",
            "content": toolchain,
        },
    }

    def fake_run_gh(*args: str, stdin: str | None = None) -> str:
        return json.dumps(responses[args[1]])

    monkeypatch.setattr(pr_advisory, "run_gh", fake_run_gh)

    metadata = fetch_upstream_metadata("acme/demo")

    assert metadata.license == "Apache-2.0"
    assert metadata.last_commit_date == "2026-06-20"
    assert metadata.lean_version == "v4.30.0"


def test_fetch_upstream_metadata_reports_unknown_missing_source_fields(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Missing source-repo metadata is reported as unknown."""

    def fake_run_gh(*args: str, stdin: str | None = None) -> str:
        endpoint = args[1]
        if endpoint == "repos/acme/demo":
            return json.dumps(
                {
                    "default_branch": "main",
                    "html_url": "https://github.com/acme/demo",
                    "license": None,
                }
            )
        raise subprocess.CalledProcessError(1, ["gh", *args])

    monkeypatch.setattr(pr_advisory, "run_gh", fake_run_gh)

    metadata = fetch_upstream_metadata("acme/demo")

    assert metadata.license == "unknown"
    assert metadata.last_commit_date == "unknown"
    assert metadata.lean_version == "unknown"


def test_post_sticky_comment_updates_existing_comment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A rerun updates the existing marker comment instead of posting a new one."""
    calls: list[tuple[tuple[str, ...], str | None]] = []
    existing = {"id": 99, "body": f"{ADVISORY_MARKER}\nold"}

    def fake_run_gh(*args: str, stdin: str | None = None) -> str:
        calls.append((args, stdin))
        if "comments?per_page=100" in args[1]:
            return json.dumps(existing) + "\n"
        return "{}"

    monkeypatch.setattr(pr_advisory, "run_gh", fake_run_gh)

    action = post_sticky_comment("acme/pool", 7, f"{ADVISORY_MARKER}\nnew")

    assert action == "updated"
    assert calls[1][0][:3] == ("api", "-X", "PATCH")
    assert json.loads(calls[1][1] or "{}")["body"].endswith("new")


def test_update_pr_advisory_skips_pr_without_project_changes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """PRs without project metadata changes do not need a sticky comment."""
    posted = False

    def fake_rows(
        repo_full_name: str,
        pr_number: int,
        *,
        metadata_cache: dict[str, UpstreamMetadata] | None = None,
    ) -> list[AdvisoryRow]:
        assert repo_full_name == "acme/pool"
        assert pr_number == 7
        return []

    def fake_post(*args: object, **kwargs: object) -> str:
        nonlocal posted
        posted = True
        return "created"

    monkeypatch.setattr(pr_advisory, "advisory_rows_for_pr", fake_rows)
    monkeypatch.setattr(pr_advisory, "post_sticky_comment", fake_post)

    action = update_pr_advisory("acme/pool", 7)

    assert action == "skipped"
    assert not posted


def test_main_treats_comment_post_failure_as_nonblocking(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """GitHub comment-write failures should not fail the advisory workflow."""

    def fake_update(
        repo_full_name: str,
        pr_number: int,
        *,
        metadata_cache: dict[str, UpstreamMetadata] | None = None,
        dry_run: bool = False,
    ) -> str:
        assert repo_full_name == "acme/pool"
        assert pr_number == 7
        assert not dry_run
        raise subprocess.CalledProcessError(
            1,
            ["gh", "api"],
            stderr="Resource not accessible by integration\n",
        )

    monkeypatch.setattr(pr_advisory, "update_pr_advisory", fake_update)

    assert main(["--repo", "acme/pool", "--pr-number", "7"]) == 0

    captured = capsys.readouterr()
    assert "PR #7: comment-failed" in captured.out
    assert "continuing because this workflow is non-blocking" in captured.err
    assert "Resource not accessible by integration" in captured.err
