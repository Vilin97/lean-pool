"""Version-detection, pin-rewriting, and build-log triage for Mathlib bumps.

Backs ``.github/workflows/mathlib-bump.yml``. The workflow keeps only
orchestration; every decision that benefits from being testable lives here:

* ``detect``  -- is there a newer Mathlib release than the one pinned?
* ``pin``     -- rewrite the four version pins to a target release.
* ``report``  -- turn a ``lake build`` log into a per-project breakage map,
  which becomes the repair fan-out's job matrix.

Pool projects never import each other, so a bump decomposes into one
independent repair per broken project. ``report`` is what makes that
decomposition explicit.

Usage::

    python -m lean_pool.bump detect --repo .. [--allow-prerelease]
    python -m lean_pool.bump pin --repo .. --version v4.33.0-rc1
    python -m lean_pool.bump report --repo .. --log build.log
"""

from __future__ import annotations

import argparse
import json
import logging
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

logger = logging.getLogger(__name__)

MATHLIB_REMOTE = "https://github.com/leanprover-community/mathlib4"

# Release tags shared by Lean, Mathlib, and doc-gen4: v4.33.0, v4.33.0-rc1.
VERSION_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?$")
# Diagnostics are `error: <path>:<line>:<col>: <message>`; lake may prefix the
# path with `./`. Progress lines instead name the module: `Building LeanPool.X`.
DIAGNOSTIC_RE = re.compile(r"^(?:.*?\s)?(error|warning):\s*(.*)$")
PATH_PROJECT_RE = re.compile(r"LeanPool/(\w+)")
MODULE_PROJECT_RE = re.compile(r"LeanPool\.(\w+)")
BUILDING_RE = re.compile(r"Building\s+(LeanPool\.\S+)")

# How many diagnostic lines to carry into the repair prompt per project.
MAX_EXCERPT_LINES = 40


def version_key(tag: str) -> tuple[int, int, int, int, int]:
    """Sort key for a release tag; a final release outranks its candidates."""
    match = VERSION_RE.match(tag)
    if match is None:
        raise ValueError(f"not a release tag: {tag}")
    major, minor, patch, candidate = match.groups()
    # `is_final` = 1 sorts v4.33.0 above v4.33.0-rc9.
    is_final = 0 if candidate else 1
    return (int(major), int(minor), int(patch), is_final, int(candidate or 0))


def is_prerelease(tag: str) -> bool:
    """Whether ``tag`` names a release candidate rather than a final release."""
    match = VERSION_RE.match(tag)
    return bool(match and match.group(4))


def current_version(root: Path) -> str:
    """Read the Mathlib release currently pinned in ``lakefile.toml``."""
    text = (root / "lakefile.toml").read_text(encoding="utf-8")
    # The manifest lists several packages; only Mathlib's rev is a release tag.
    for match in re.finditer(r'rev\s*=\s*"([^"]+)"', text):
        if VERSION_RE.match(match.group(1)):
            return match.group(1)
    raise SystemExit("no Mathlib release tag found in lakefile.toml")


def remote_tags(remote: str = MATHLIB_REMOTE) -> list[str]:
    """List release tags published by the Mathlib repository."""
    result = subprocess.run(
        ["git", "ls-remote", "--tags", "--refs", remote],
        capture_output=True,
        text=True,
        check=True,
    )
    tags = []
    for line in result.stdout.splitlines():
        _, _, ref = line.partition("refs/tags/")
        if ref and VERSION_RE.match(ref.strip()):
            tags.append(ref.strip())
    return tags


def newer_versions(
    current: str, tags: list[str], *, allow_prerelease: bool
) -> list[str]:
    """Return tags strictly newer than ``current``, oldest first."""
    threshold = version_key(current)
    candidates = [
        tag
        for tag in tags
        if version_key(tag) > threshold and (allow_prerelease or not is_prerelease(tag))
    ]
    return sorted(set(candidates), key=version_key)


def pin_files(root: Path, version: str) -> list[Path]:
    """Rewrite the toolchain and dependency pins to ``version``.

    Returns the files that changed. ``lake update`` still has to regenerate
    the manifests afterwards; this only moves the declared pins.
    """
    if not VERSION_RE.match(version):
        raise SystemExit(f"not a release tag: {version}")
    changed: list[Path] = []
    edits: list[tuple[Path, re.Pattern[str], str]] = [
        (
            root / "lean-toolchain",
            re.compile(r"^leanprover/lean4:.*$", re.M),
            f"leanprover/lean4:{version}",
        ),
        (
            root / "docbuild" / "lean-toolchain",
            re.compile(r"^leanprover/lean4:.*$", re.M),
            f"leanprover/lean4:{version}",
        ),
        # Only the release-tag rev is rewritten; branch pins (main, master)
        # in the same file are left alone.
        (
            root / "lakefile.toml",
            re.compile(r'rev\s*=\s*"v[\d.]+(?:-rc\d+)?"'),
            f'rev = "{version}"',
        ),
        (
            root / "docbuild" / "lakefile.toml",
            re.compile(r'rev\s*=\s*"v[\d.]+(?:-rc\d+)?"'),
            f'rev = "{version}"',
        ),
    ]
    for path, pattern, replacement in edits:
        if not path.is_file():
            raise SystemExit(f"missing pin file: {path}")
        before = path.read_text(encoding="utf-8")
        after = pattern.sub(replacement, before)
        if after != before:
            path.write_text(after, encoding="utf-8")
            changed.append(path)
    return changed


@dataclass
class ProjectDiagnostics:
    """Errors and warnings attributed to a single pool project."""

    project: str
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    def as_dict(self) -> dict[str, object]:
        """Serialise for the workflow's job matrix and report artifact."""
        return {
            "project": self.project,
            "errors": self.errors[:MAX_EXCERPT_LINES],
            "warnings": self.warnings[:MAX_EXCERPT_LINES],
            "error_count": len(self.errors),
            "warning_count": len(self.warnings),
        }


def _attribute(text: str, fallback: str | None) -> str | None:
    """Find which project a diagnostic line belongs to."""
    match = PATH_PROJECT_RE.search(text) or MODULE_PROJECT_RE.search(text)
    return match.group(1) if match else fallback


def parse_build_log(log: str) -> dict[str, ProjectDiagnostics]:
    """Bucket a ``lake build`` log's diagnostics by pool project.

    Diagnostics name their file, so most lines attribute themselves. A
    message that does not (a bare continuation line, or an error lake prints
    against a module rather than a file) is attributed to the module of the
    most recent ``Building`` line.
    """
    buckets: dict[str, ProjectDiagnostics] = {}
    current: str | None = None
    active: tuple[str, str] | None = None  # (project, severity) for continuations

    for line in log.splitlines():
        building = BUILDING_RE.search(line)
        if building:
            module = MODULE_PROJECT_RE.search(building.group(1))
            current = module.group(1) if module else None

        diagnostic = DIAGNOSTIC_RE.match(line)
        if diagnostic:
            severity, message = diagnostic.groups()
            project = _attribute(message, current)
            if project is None:
                active = None
                continue
            bucket = buckets.setdefault(project, ProjectDiagnostics(project))
            target = bucket.errors if severity == "error" else bucket.warnings
            target.append(line.rstrip())
            active = (project, severity)
            continue

        # Indented continuation of the previous diagnostic (goal state, etc.).
        if active and line.startswith(" ") and line.strip():
            project, severity = active
            bucket = buckets[project]
            target = bucket.errors if severity == "error" else bucket.warnings
            if len(target) < MAX_EXCERPT_LINES:
                target.append(line.rstrip())
        elif not line.strip():
            active = None

    return buckets


def build_report(log: str) -> dict[str, object]:
    """Summarise a build log into the report the workflow consumes."""
    buckets = parse_build_log(log)
    broken = sorted((b for b in buckets.values() if b.errors), key=lambda b: b.project)
    warned = sorted(
        (b for b in buckets.values() if b.warnings and not b.errors),
        key=lambda b: b.project,
    )
    return {
        "broken": [b.as_dict() for b in broken],
        "warned": [b.as_dict() for b in warned],
        "broken_projects": [b.project for b in broken],
        "warned_projects": [b.project for b in warned],
        "clean": not broken and not warned,
    }


def _command_detect(args: argparse.Namespace) -> int:
    """Print the next Mathlib release to bump to, if any."""
    root = args.repo.resolve()
    current = current_version(root)
    tags = remote_tags(args.remote)
    newer = newer_versions(current, tags, allow_prerelease=args.allow_prerelease)
    target = newer[-1] if newer else ""
    payload = {
        "current": current,
        "target": target,
        "available": newer,
        "found": bool(target),
    }
    print(json.dumps(payload))
    return 0


def _command_pin(args: argparse.Namespace) -> int:
    """Rewrite the version pins and report which files moved."""
    changed = pin_files(args.repo.resolve(), args.version)
    for path in changed:
        logger.info("pinned %s", path)
    if not changed:
        logger.info("pins already at %s", args.version)
    return 0


def _command_report(args: argparse.Namespace) -> int:
    """Turn a build log into the per-project breakage report."""
    log = args.log.read_text(encoding="utf-8", errors="replace")
    report = build_report(log)
    output = json.dumps(report, indent=2)
    if args.output:
        args.output.write_text(output + "\n", encoding="utf-8")
    print(output)
    return 0


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subparsers = parser.add_subparsers(dest="command", required=True)

    # `--repo` sits on each subcommand rather than the parent so it can be
    # passed after the subcommand, which is how it reads in a workflow step.
    detect = subparsers.add_parser("detect", help="find a newer Mathlib release")
    detect.add_argument("--repo", type=Path, default=Path("."), help="repository root")
    detect.add_argument("--remote", default=MATHLIB_REMOTE)
    detect.add_argument(
        "--allow-prerelease",
        action="store_true",
        help="also consider -rc tags (default: final releases only)",
    )
    detect.set_defaults(func=_command_detect)

    pin = subparsers.add_parser("pin", help="rewrite the version pins")
    pin.add_argument("--repo", type=Path, default=Path("."), help="repository root")
    pin.add_argument("--version", required=True)
    pin.set_defaults(func=_command_pin)

    report = subparsers.add_parser("report", help="triage a build log by project")
    report.add_argument("--log", type=Path, required=True)
    report.add_argument("--output", type=Path)
    report.set_defaults(func=_command_report)

    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Dispatch a subcommand; return a process exit code."""
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    args = _parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    sys.exit(main())
