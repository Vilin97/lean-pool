"""Compute headline repository statistics and write them into the README.

The main ``README.md`` carries a short, machine-maintained line reporting
how many projects live in the pool and how many lines of Lean they total.
This module derives both numbers from the single sources of truth
(``LeanPool/projects.yml`` for the project count, the ``LeanPool/`` tree
for the line count) and rewrites the block delimited by two HTML comment
markers:

    <!-- BEGIN STATS -->
    ...generated line goes here...
    <!-- END STATS -->

Run ``python -m lean_pool.stats --repo .`` to rewrite the block, or pass
``--check`` to fail without writing when the block is stale (used by CI to
decide whether a refresh commit is needed).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import yaml

BEGIN_MARKER = "<!-- BEGIN STATS -->"
END_MARKER = "<!-- END STATS -->"

_MARKER_BLOCK = re.compile(
    re.escape(BEGIN_MARKER) + r".*?" + re.escape(END_MARKER),
    re.DOTALL,
)

# Directories whose ``.lean`` files are build artefacts or vendored
# dependencies rather than pooled project source. ``LeanPool/`` should
# never contain these, but excluding them keeps the count honest if a
# stray build tree ever lands under it.
_LOC_EXCLUDE_DIR_NAMES = frozenset({".lake", ".git", "lake-packages", "build"})


@dataclass(frozen=True)
class Stats:
    """Headline counts shown in the README."""

    projects: int
    lines_of_lean: int


def count_projects(projects_yml_path: Path) -> int:
    """Return the number of projects registered in ``projects.yml``.

    Args:
        projects_yml_path: Path to ``LeanPool/projects.yml``.

    Returns:
        The length of the top-level ``projects`` list, or ``0`` if the
        file is missing, malformed, or has no ``projects`` key.
    """
    if not projects_yml_path.is_file():
        return 0
    data = yaml.safe_load(projects_yml_path.read_text()) or {}
    if not isinstance(data, dict):
        return 0
    projects = data.get("projects") or []
    if not isinstance(projects, list):
        return 0
    return len(projects)


def count_lean_loc(pool_dir: Path) -> int:
    """Sum lines across every ``.lean`` file under the pool tree.

    Walks ``pool_dir`` recursively and totals lines across all files
    matching ``*.lean``, skipping build/dependency directories. Line
    counting uses raw newline semantics so it matches ``wc -l``.

    Args:
        pool_dir: Path to the ``LeanPool/`` directory.

    Returns:
        The total line count, or ``0`` if the directory is missing.
    """
    if not pool_dir.is_dir():
        return 0
    total = 0
    for path in pool_dir.rglob("*.lean"):
        if any(part in _LOC_EXCLUDE_DIR_NAMES for part in path.parts):
            continue
        try:
            with path.open("rb") as handle:
                total += sum(1 for _ in handle)
        except OSError:
            continue
    return total


def collect_stats(root: Path) -> Stats:
    """Gather all README statistics for the checkout at ``root``."""
    return Stats(
        projects=count_projects(root / "LeanPool" / "projects.yml"),
        lines_of_lean=count_lean_loc(root / "LeanPool"),
    )


def render_stats(stats: Stats) -> str:
    """Render the stats block body (without the surrounding markers)."""
    return (
        f"**{stats.projects}** formalization projects · "
        f"**{stats.lines_of_lean:,}** lines of Lean"
    )


def apply_stats(readme_text: str, stats: Stats) -> str:
    """Return ``readme_text`` with the stats block replaced.

    Raises:
        ValueError: If the BEGIN/END markers are not present.
    """
    if not _MARKER_BLOCK.search(readme_text):
        raise ValueError(
            f"Could not find stats markers in README. "
            f"Expected '{BEGIN_MARKER}' ... '{END_MARKER}'."
        )
    replacement = f"{BEGIN_MARKER}\n{render_stats(stats)}\n{END_MARKER}"
    return _MARKER_BLOCK.sub(replacement, readme_text, count=1)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Repository root. Defaults to the checkout containing this package.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit non-zero if the README stats block is stale; do not write.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the stats CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    readme_path = root / "README.md"
    original = readme_path.read_text()
    stats = collect_stats(root)
    updated = apply_stats(original, stats)

    if args.check:
        if updated != original:
            print(
                "README stats are out of date. Run "
                "`uv run python -m lean_pool.stats --repo .` and commit.",
                file=sys.stderr,
            )
            return 1
        print("README stats are up to date.")
        return 0

    if updated != original:
        readme_path.write_text(updated)
        print(f"Updated README stats: {render_stats(stats)}")
    else:
        print("README stats already up to date.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
