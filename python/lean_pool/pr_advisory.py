"""Post project metadata advisory comments on open pull requests.

The advisory is intentionally deterministic and does not execute pull request
code. It reads ``LeanPool/projects.yml`` from the PR base and head commits via
the GitHub API, detects added or changed project entries, enriches those
entries with source-repository metadata, then creates or updates a sticky PR
conversation comment.

Environment variables:
    GH_TOKEN: Token used by the GitHub CLI in CI.
    GITHUB_REPOSITORY: Repository in ``owner/name`` form.
    PR_NUMBER: Optional single PR number.

Run:
    uv run python -m lean_pool.pr_advisory
    uv run python -m lean_pool.pr_advisory --pr-number 123
    uv run python -m lean_pool.pr_advisory --dry-run
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Any
from urllib.parse import quote

import yaml

ADVISORY_MARKER = "<!-- lean-pool-project-advisory -->"
PROJECTS_PATH = "LeanPool/projects.yml"
TOOLCHAIN_PATH = "lean-toolchain"
UNKNOWN = "unknown"

_TOOLCHAIN_PREFIX_RE = re.compile(r"^leanprover/lean4:", re.IGNORECASE)


@dataclass(frozen=True)
class ProjectEntry:
    """Project metadata read from ``LeanPool/projects.yml``."""

    slug: str
    title: str
    license: str
    github_repo: str | None


@dataclass(frozen=True)
class ProjectChange:
    """A project entry added or changed by a pull request."""

    kind: str
    project: ProjectEntry


@dataclass(frozen=True)
class PullRequestRef:
    """The base and head repositories and commits for a PR."""

    number: int
    base_repo: str
    base_sha: str
    head_repo: str
    head_sha: str


@dataclass(frozen=True)
class UpstreamMetadata:
    """Metadata fetched from a project's source repository."""

    license: str
    last_commit_date: str
    lean_version: str
    url: str | None = None


@dataclass(frozen=True)
class AdvisoryRow:
    """One Markdown table row in the advisory comment."""

    project: ProjectEntry
    change_kind: str
    metadata: UpstreamMetadata


def run_gh(*args: str, stdin: str | None = None) -> str:
    """Run ``gh`` and return stdout.

    Args:
        *args: Arguments passed after ``gh``.
        stdin: Optional text passed to stdin.

    Returns:
        The command's stdout.
    """
    command = ["gh", *args]
    result = subprocess.run(
        command,
        capture_output=True,
        text=True,
        input=stdin,
    )
    if result.returncode != 0:
        print(
            f"GitHub CLI command failed with exit code {result.returncode}: "
            f"{' '.join(command)}",
            file=sys.stderr,
        )
        if result.stdout:
            print(result.stdout, file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        raise subprocess.CalledProcessError(
            result.returncode,
            command,
            output=result.stdout,
            stderr=result.stderr,
        )
    return result.stdout


def resolve_repo_full_name() -> str:
    """Return the current GitHub repository as ``owner/name``."""
    if repo := os.environ.get("GITHUB_REPOSITORY"):
        return repo
    return run_gh("repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner")


def list_open_pr_numbers(repo_full_name: str) -> list[int]:
    """Return all open pull request numbers, including drafts."""
    raw = run_gh(
        "api",
        f"repos/{repo_full_name}/pulls?state=open&per_page=100",
        "--paginate",
        "--jq",
        ".[].number",
    )
    return [int(line) for line in raw.splitlines() if line.strip()]


def project_changes(
    base_projects_text: str, head_projects_text: str
) -> list[ProjectChange]:
    """Return project entries added or changed between base and head YAML."""
    base_projects = _load_projects(base_projects_text)
    head_projects = _load_projects(head_projects_text)
    changes: list[ProjectChange] = []
    for slug in sorted(head_projects):
        head_project = head_projects[slug]
        base_project = base_projects.get(slug)
        if base_project is None:
            changes.append(ProjectChange(kind="added", project=head_project))
        elif head_project != base_project:
            changes.append(ProjectChange(kind="changed", project=head_project))
    return changes


def fetch_upstream_metadata(
    github_repo: str | None,
) -> UpstreamMetadata:
    """Fetch license, latest commit date, and Lean toolchain from GitHub."""
    if not github_repo:
        return UpstreamMetadata(
            license=UNKNOWN,
            last_commit_date=UNKNOWN,
            lean_version=UNKNOWN,
        )

    try:
        repository = _gh_json(f"repos/{github_repo}")
    except subprocess.CalledProcessError:
        return UpstreamMetadata(
            license=UNKNOWN,
            last_commit_date=UNKNOWN,
            lean_version=UNKNOWN,
            url=f"https://github.com/{github_repo}",
        )

    default_branch = str(repository.get("default_branch") or "main")
    license_name = _github_license(repository) or UNKNOWN
    commit_date = _fetch_latest_commit_date(github_repo, default_branch)
    lean_version = _fetch_lean_version(github_repo, default_branch)
    return UpstreamMetadata(
        license=license_name,
        last_commit_date=commit_date,
        lean_version=lean_version,
        url=repository.get("html_url") or f"https://github.com/{github_repo}",
    )


def advisory_rows_for_pr(
    repo_full_name: str,
    pr_number: int,
    *,
    metadata_cache: dict[str, UpstreamMetadata] | None = None,
) -> list[AdvisoryRow]:
    """Build advisory rows for a pull request."""
    pr_ref = _fetch_pr_ref(repo_full_name, pr_number)
    base_projects = _fetch_file_text(pr_ref.base_repo, PROJECTS_PATH, pr_ref.base_sha)
    head_projects = _fetch_file_text(pr_ref.head_repo, PROJECTS_PATH, pr_ref.head_sha)
    if base_projects is None or head_projects is None:
        return []

    cache = metadata_cache if metadata_cache is not None else {}
    rows: list[AdvisoryRow] = []
    for change in project_changes(base_projects, head_projects):
        cache_key = change.project.github_repo or f"project:{change.project.slug}"
        metadata = cache.get(cache_key)
        if metadata is None:
            metadata = fetch_upstream_metadata(change.project.github_repo)
            cache[cache_key] = metadata
        rows.append(
            AdvisoryRow(
                project=change.project,
                change_kind=change.kind,
                metadata=metadata,
            )
        )
    return rows


def render_comment(rows: list[AdvisoryRow]) -> str:
    """Render the sticky advisory comment body."""
    lines = [
        ADVISORY_MARKER,
        "## Project metadata advisory",
        "",
        (
            "This advisory summarizes source-project metadata for project "
            "entries added or changed by this PR."
        ),
        "",
    ]

    if not rows:
        lines.extend(
            [
                "No added or changed `LeanPool/projects.yml` project entries were "
                "detected for this PR.",
                "",
            ]
        )
    else:
        lines.extend(
            [
                "| Project | Change | Source | License | Last commit | Lean |",
                "| --- | --- | --- | --- | --- | --- |",
            ]
        )
        for row in rows:
            project = _markdown_code(row.project.slug)
            source = _source_cell(row.project.github_repo, row.metadata.url)
            license_name = _markdown_code(row.metadata.license)
            last_commit = _markdown_code(row.metadata.last_commit_date)
            lean_version = _markdown_code(row.metadata.lean_version)
            lines.append(
                f"| {project} | {row.change_kind} | {source} | {license_name} "
                f"| {last_commit} | {lean_version} |"
            )
        lines.append("")

    lines.extend(
        [
            (
                "_License is read from GitHub SPDX metadata when available, "
                "and the last commit and Lean version are read from the source "
                "repository's default branch._"
            )
        ]
    )
    return "\n".join(lines)


def post_sticky_comment(
    repo_full_name: str,
    pr_number: int,
    body: str,
    *,
    dry_run: bool = False,
) -> str:
    """Create or update the advisory comment on one PR.

    Args:
        repo_full_name: Repository in ``owner/name`` form.
        pr_number: Pull request number.
        body: Full Markdown comment body.
        dry_run: Print intended action without writing to GitHub.

    Returns:
        ``created``, ``updated``, ``unchanged``, or ``dry-run``.
    """
    existing = _find_existing_comment(repo_full_name, pr_number)
    if dry_run:
        action = "update" if existing is not None else "create"
        print(f"[dry-run] Would {action} advisory comment on PR #{pr_number}")
        print(body)
        return "dry-run"

    if existing is not None:
        if existing.get("body") == body:
            return "unchanged"
        run_gh(
            "api",
            "-X",
            "PATCH",
            f"repos/{repo_full_name}/issues/comments/{existing['id']}",
            "--input",
            "-",
            stdin=json.dumps({"body": body}),
        )
        return "updated"

    run_gh(
        "api",
        "-X",
        "POST",
        f"repos/{repo_full_name}/issues/{pr_number}/comments",
        "--input",
        "-",
        stdin=json.dumps({"body": body}),
    )
    return "created"


def update_pr_advisory(
    repo_full_name: str,
    pr_number: int,
    *,
    metadata_cache: dict[str, UpstreamMetadata] | None = None,
    dry_run: bool = False,
) -> str:
    """Render and post the advisory for one PR."""
    rows = advisory_rows_for_pr(
        repo_full_name, pr_number, metadata_cache=metadata_cache
    )
    if not rows:
        if dry_run:
            print(
                "[dry-run] Would skip advisory comment on "
                f"PR #{pr_number}: no project metadata changes"
            )
        return "skipped"
    return post_sticky_comment(
        repo_full_name,
        pr_number,
        render_comment(rows),
        dry_run=dry_run,
    )


def main(argv: list[str] | None = None) -> int:
    """CLI entry point."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        default=None,
        help="Repository in owner/name form. Defaults to GITHUB_REPOSITORY.",
    )
    parser.add_argument(
        "--pr-number",
        type=int,
        action="append",
        help="PR number to update. May be passed more than once.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Render actions without creating or updating comments.",
    )
    args = parser.parse_args(argv)

    repo_full_name = (args.repo or resolve_repo_full_name()).strip()
    pr_numbers = _resolve_pr_numbers(repo_full_name, args.pr_number)
    if not pr_numbers:
        print("No open PRs found.")
        return 0

    metadata_cache: dict[str, UpstreamMetadata] = {}
    for pr_number in pr_numbers:
        try:
            action = update_pr_advisory(
                repo_full_name,
                pr_number,
                metadata_cache=metadata_cache,
                dry_run=args.dry_run,
            )
        except subprocess.CalledProcessError as error:
            print(
                f"PR #{pr_number}: advisory comment failed; "
                "continuing because this workflow is non-blocking.",
                file=sys.stderr,
            )
            if error.stderr:
                print(error.stderr, file=sys.stderr)
            action = "comment-failed"
        print(f"PR #{pr_number}: {action}")
    return 0


def _resolve_pr_numbers(
    repo_full_name: str, explicit_numbers: list[int] | None
) -> list[int]:
    if explicit_numbers:
        return explicit_numbers
    if env_pr := os.environ.get("PR_NUMBER"):
        return [int(env_pr)]
    return list_open_pr_numbers(repo_full_name)


def _load_projects(projects_text: str) -> dict[str, ProjectEntry]:
    data = yaml.safe_load(projects_text) or {}
    projects = data.get("projects") if isinstance(data, dict) else None
    if not isinstance(projects, list):
        return {}

    result: dict[str, ProjectEntry] = {}
    for item in projects:
        if not isinstance(item, dict):
            continue
        slug = item.get("slug")
        if not isinstance(slug, str) or not slug.strip():
            continue
        source = item.get("source")
        github_repo = None
        if isinstance(source, dict) and isinstance(source.get("github_repo"), str):
            github_repo = source["github_repo"].strip() or None
        result[slug] = ProjectEntry(
            slug=slug,
            title=str(item.get("title") or slug),
            license=str(item.get("license") or UNKNOWN),
            github_repo=github_repo,
        )
    return result


def _fetch_pr_ref(repo_full_name: str, pr_number: int) -> PullRequestRef:
    pr = _gh_json(f"repos/{repo_full_name}/pulls/{pr_number}")
    base = pr["base"]
    head = pr["head"]
    head_repo = head.get("repo") or {}
    if not head_repo.get("full_name"):
        raise RuntimeError(f"PR #{pr_number} has no accessible head repository")
    return PullRequestRef(
        number=pr_number,
        base_repo=base["repo"]["full_name"],
        base_sha=base["sha"],
        head_repo=head_repo["full_name"],
        head_sha=head["sha"],
    )


def _fetch_file_text(repo_full_name: str, path: str, ref: str) -> str | None:
    encoded_path = quote(path, safe="/")
    encoded_ref = quote(ref, safe="")
    endpoint = f"repos/{repo_full_name}/contents/{encoded_path}?ref={encoded_ref}"
    try:
        payload = _gh_json(endpoint)
    except subprocess.CalledProcessError:
        return None
    content = payload.get("content")
    if not isinstance(content, str):
        return None
    if payload.get("encoding") != "base64":
        return None
    return base64.b64decode(content).decode("utf-8")


def _gh_json(endpoint: str) -> Any:
    return json.loads(run_gh("api", endpoint))


def _github_license(repository: dict[str, Any]) -> str | None:
    license_block = repository.get("license")
    if not isinstance(license_block, dict):
        return None
    spdx_id = license_block.get("spdx_id")
    if not isinstance(spdx_id, str) or spdx_id in {"", "NOASSERTION"}:
        return None
    return spdx_id


def _fetch_latest_commit_date(github_repo: str, default_branch: str) -> str:
    try:
        commit = _gh_json(
            f"repos/{github_repo}/commits/{quote(default_branch, safe='')}"
        )
    except subprocess.CalledProcessError:
        return UNKNOWN
    date = commit.get("commit", {}).get("committer", {}).get("date")
    if not isinstance(date, str) or not date:
        return UNKNOWN
    return date.split("T", 1)[0]


def _fetch_lean_version(github_repo: str, default_branch: str) -> str:
    text = _fetch_file_text(github_repo, TOOLCHAIN_PATH, default_branch)
    if text is None:
        return UNKNOWN
    stripped = _TOOLCHAIN_PREFIX_RE.sub("", text, count=1).strip()
    return stripped or UNKNOWN


def _find_existing_comment(
    repo_full_name: str, pr_number: int
) -> dict[str, Any] | None:
    raw = run_gh(
        "api",
        f"repos/{repo_full_name}/issues/{pr_number}/comments?per_page=100",
        "--paginate",
        "--jq",
        ".[]",
    )
    for line in raw.splitlines():
        if not line.strip():
            continue
        comment = json.loads(line)
        if str(comment.get("body") or "").startswith(ADVISORY_MARKER):
            return comment
    return None


def _source_cell(github_repo: str | None, url: str | None) -> str:
    if not github_repo:
        return UNKNOWN
    escaped = _escape_markdown_table(github_repo)
    if url:
        return f"[{escaped}]({url})"
    return escaped


def _markdown_code(value: str) -> str:
    return f"`{_escape_markdown_table(value)}`"


def _escape_markdown_table(value: str) -> str:
    return " ".join(value.split()).replace("|", r"\|") or UNKNOWN


if __name__ == "__main__":
    sys.exit(main())
