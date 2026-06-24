"""Tests for README statistics generation."""

from __future__ import annotations

from pathlib import Path

import pytest

from lean_pool.stats import (
    Stats,
    apply_stats,
    collect_stats,
    count_lean_loc,
    count_projects,
    main,
    render_stats,
)

PROJECTS_YML = """projects:
  - slug: alpha
    title: Alpha
  - slug: beta
    title: Beta
"""


def _write_pool(root: Path) -> None:
    """Create a minimal LeanPool tree with two projects and known LOC."""
    pool = root / "LeanPool"
    pool.mkdir()
    (pool / "projects.yml").write_text(PROJECTS_YML)
    (pool / "Alpha.lean").write_text("line1\nline2\nline3\n")
    nested = pool / "Beta"
    nested.mkdir()
    (nested / "Core.lean").write_text("only-one-line\n")


def test_count_projects(tmp_path: Path) -> None:
    """The project count is the length of the projects list."""
    _write_pool(tmp_path)
    assert count_projects(tmp_path / "LeanPool" / "projects.yml") == 2


def test_count_projects_missing_file(tmp_path: Path) -> None:
    """A missing registry yields zero rather than raising."""
    assert count_projects(tmp_path / "nope.yml") == 0


def test_count_lean_loc(tmp_path: Path) -> None:
    """Lines are summed recursively across every .lean file."""
    _write_pool(tmp_path)
    assert count_lean_loc(tmp_path / "LeanPool") == 4


def test_count_lean_loc_skips_build_dirs(tmp_path: Path) -> None:
    """Build/dependency directories are excluded from the count."""
    _write_pool(tmp_path)
    artefact = tmp_path / "LeanPool" / ".lake" / "Dep.lean"
    artefact.parent.mkdir()
    artefact.write_text("a\nb\nc\nd\ne\n")
    assert count_lean_loc(tmp_path / "LeanPool") == 4


def test_collect_stats(tmp_path: Path) -> None:
    """Both headline numbers are gathered from the checkout."""
    _write_pool(tmp_path)
    assert collect_stats(tmp_path) == Stats(projects=2, lines_of_lean=4)


def test_apply_stats_replaces_block() -> None:
    """Only the marked block is rewritten; surrounding text is kept."""
    readme = "intro\n<!-- BEGIN STATS -->\nold\n<!-- END STATS -->\noutro\n"
    updated = apply_stats(readme, Stats(projects=2, lines_of_lean=4))
    assert render_stats(Stats(projects=2, lines_of_lean=4)) in updated
    assert "old" not in updated
    assert updated.startswith("intro\n")
    assert updated.endswith("outro\n")


def test_apply_stats_requires_markers() -> None:
    """A README without the markers is a hard error."""
    with pytest.raises(ValueError, match="stats markers"):
        apply_stats("no markers here", Stats(projects=1, lines_of_lean=1))


def test_main_writes_and_is_idempotent(tmp_path: Path) -> None:
    """Writing fills the block, and re-running changes nothing."""
    _write_pool(tmp_path)
    readme = tmp_path / "README.md"
    readme.write_text("<!-- BEGIN STATS -->\n\n<!-- END STATS -->\n")

    assert main(["--repo", str(tmp_path)]) == 0
    assert "**2** formalization projects" in readme.read_text()
    # A second write is a no-op, and --check now passes.
    assert main(["--repo", str(tmp_path)]) == 0
    assert main(["--repo", str(tmp_path), "--check"]) == 0


def test_main_check_fails_when_stale(tmp_path: Path) -> None:
    """`--check` exits non-zero when the block is out of date."""
    _write_pool(tmp_path)
    readme = tmp_path / "README.md"
    readme.write_text("<!-- BEGIN STATS -->\nstale\n<!-- END STATS -->\n")
    assert main(["--repo", str(tmp_path), "--check"]) == 1
