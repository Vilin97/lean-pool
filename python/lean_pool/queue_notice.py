"""Validate submitted attribution snapshots before regenerating a combined view."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
from pathlib import Path

import yaml

from lean_pool import notice, registry
from lean_pool.ci_artifacts import github_json


def git(root: Path, *arguments: str) -> str:
    """Read exact queue and constituent objects without changing the checkout."""
    return subprocess.check_output(["git", *arguments], cwd=root, text=True)


def validate_snapshot(root: Path, revision: str, expected_notice: str) -> None:
    """Reject hand-edited attribution against the submitting PR's own registry."""
    projects = registry.read_revision(root, revision)["projects"]
    extra = yaml.safe_load(git(root, "show", f"{revision}:NOTICE.extra.yml")) or {}
    if notice.unregistered_notes(projects, extra):
        raise ValueError("Attribution notes refer to unknown projects")
    if notice.render(projects, extra) != expected_notice:
        raise ValueError("Submitted NOTICE does not match its own project registry")


def write_test_view(root: Path) -> None:
    """Prepare generated attribution without following a checkout-controlled link."""
    with tempfile.NamedTemporaryFile(
        mode="w", dir=root, prefix=".notice-test-", delete=False
    ) as output:
        temporary = Path(output.name)
        try:
            output.write(notice.build(root))
        except BaseException:
            temporary.unlink()
            raise
    temporary.replace(root / "NOTICE")


def prepare_pull_request(root: Path, base: str, submitted_head: str) -> None:
    """Validate authored edits separately from stale inherited generated files."""
    ancestor = git(root, "merge-base", base, submitted_head).strip()
    changed = git(root, "diff", "--name-only", ancestor, submitted_head).splitlines()
    if "NOTICE" in changed:
        validate_snapshot(
            root, submitted_head, git(root, "show", f"{submitted_head}:NOTICE")
        )
    write_test_view(root)


def prepare(root: Path, repository: str, base: str, head: str) -> None:
    """Check each edited NOTICE, then include all queued projects in the test view."""
    commits = git(root, "rev-list", "--reverse", f"{base}..{head}").splitlines()
    for commit in commits:
        changed = git(root, "diff", "--name-only", f"{commit}^", commit).splitlines()
        if "NOTICE" not in changed:
            continue
        subject = git(root, "show", "-s", "--format=%s", commit).strip()
        match = re.search(r"\(#(\d+)\)$", subject)
        if match is None:
            raise ValueError("Cannot identify attribution PR in merge queue")
        pull = github_json(f"repos/{repository}/pulls/{match[1]}")
        if (
            pull["base"]["repo"]["full_name"] != repository
            or pull["base"]["ref"] != "main"
        ):
            raise ValueError("Attribution PR belongs to a different base repository")
        previous = pull["head"]["sha"]
        if not re.fullmatch("[0-9a-f]{40}", previous):
            raise ValueError("Invalid constituent head")
        subprocess.run(["git", "fetch", "origin", previous], cwd=root, check=True)
        submitted = git(root, "show", f"{commit}:NOTICE")
        if submitted != git(root, "show", f"{previous}:NOTICE"):
            raise ValueError("Queue attribution differs from the submitted PR")
        validate_snapshot(root, previous, submitted)
    # Content-only PRs already leave generated NOTICE temporarily stale. A
    # combined queue must retain that policy while validating every edited
    # snapshot above and testing the full generator on the combined registry.
    write_test_view(root)


def main() -> None:
    """Prepare attribution for the ordinary full Python suite on merge groups."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--pull-request", action="store_true")
    args = parser.parse_args()
    if args.pull_request:
        prepare_pull_request(Path.cwd(), args.base, args.head)
    else:
        prepare(Path.cwd(), os.environ["GITHUB_REPOSITORY"], args.base, args.head)


if __name__ == "__main__":
    main()
