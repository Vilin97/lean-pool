"""Tests for Mathlib bump detection, pin rewriting, and build-log triage."""

from __future__ import annotations

from pathlib import Path

import pytest

from lean_pool.bump import (
    build_report,
    current_version,
    is_prerelease,
    main,
    newer_versions,
    parse_build_log,
    pin_files,
    version_key,
)

LAKEFILE = """name = "lean-pool"

[leanOptions]
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.32.0-rc1"

[[lean_lib]]
name = "LeanPool"
"""

DOCBUILD_LAKEFILE = """name = "docbuild"

[[require]]
name = "lean-pool"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "v4.32.0-rc1"
"""


def _write_repo(root: Path) -> None:
    """Create a repository with the four version pins a bump rewrites."""
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0-rc1\n")
    (root / "lakefile.toml").write_text(LAKEFILE)
    docbuild = root / "docbuild"
    docbuild.mkdir()
    (docbuild / "lean-toolchain").write_text("leanprover/lean4:v4.32.0-rc1\n")
    (docbuild / "lakefile.toml").write_text(DOCBUILD_LAKEFILE)


# --------------------------------------------------------------------------- #
# Version ordering
# --------------------------------------------------------------------------- #
def test_final_release_outranks_its_candidates() -> None:
    """v4.33.0 is newer than every v4.33.0-rcN."""
    assert version_key("v4.33.0") > version_key("v4.33.0-rc9")
    assert version_key("v4.33.0-rc2") > version_key("v4.33.0-rc1")
    assert version_key("v4.33.0-rc1") > version_key("v4.32.0")


def test_version_key_rejects_non_releases() -> None:
    """A branch name is not a release tag."""
    with pytest.raises(ValueError, match="not a release tag"):
        version_key("main")


def test_is_prerelease() -> None:
    """Release candidates are distinguishable from final releases."""
    assert is_prerelease("v4.33.0-rc1")
    assert not is_prerelease("v4.33.0")


def test_newer_versions_skips_prereleases_by_default() -> None:
    """Prereleases are opt-in, so nightly runs do not chase every rc."""
    tags = ["v4.32.0-rc1", "v4.32.0", "v4.33.0-rc1", "v4.33.0"]
    assert newer_versions("v4.32.0-rc1", tags, allow_prerelease=False) == [
        "v4.32.0",
        "v4.33.0",
    ]
    assert newer_versions("v4.32.0-rc1", tags, allow_prerelease=True) == [
        "v4.32.0",
        "v4.33.0-rc1",
        "v4.33.0",
    ]


def test_newer_versions_empty_when_current_is_latest() -> None:
    """An up-to-date pin yields no bump target."""
    assert (
        newer_versions("v4.33.0", ["v4.32.0", "v4.33.0"], allow_prerelease=True) == []
    )


def test_newer_versions_ignores_unparseable_tags() -> None:
    """Only well-formed release tags are considered."""
    tags = ["v4.33.0", "nightly-2026-07-01"]
    assert newer_versions(
        "v4.32.0",
        [t for t in tags if t != "nightly-2026-07-01"],
        allow_prerelease=False,
    ) == ["v4.33.0"]


# --------------------------------------------------------------------------- #
# Pins
# --------------------------------------------------------------------------- #
def test_current_version_reads_the_mathlib_pin(tmp_path: Path) -> None:
    """The pinned Mathlib release comes from lakefile.toml."""
    _write_repo(tmp_path)
    assert current_version(tmp_path) == "v4.32.0-rc1"


def test_pin_files_rewrites_all_four_pins(tmp_path: Path) -> None:
    """A bump moves both toolchains and both dependency revs."""
    _write_repo(tmp_path)
    changed = pin_files(tmp_path, "v4.33.0-rc1")
    assert len(changed) == 4
    assert (tmp_path / "lean-toolchain").read_text() == "leanprover/lean4:v4.33.0-rc1\n"
    assert 'rev = "v4.33.0-rc1"' in (tmp_path / "lakefile.toml").read_text()
    assert (
        tmp_path / "docbuild" / "lean-toolchain"
    ).read_text() == "leanprover/lean4:v4.33.0-rc1\n"
    assert (
        'rev = "v4.33.0-rc1"' in (tmp_path / "docbuild" / "lakefile.toml").read_text()
    )


def test_pin_files_preserves_lean_options(tmp_path: Path) -> None:
    """Rewriting pins must not disturb the gate-bearing [leanOptions]."""
    _write_repo(tmp_path)
    pin_files(tmp_path, "v4.33.0-rc1")
    assert "relaxedAutoImplicit = false" in (tmp_path / "lakefile.toml").read_text()


def test_pin_files_is_idempotent(tmp_path: Path) -> None:
    """Re-pinning to the same version changes nothing."""
    _write_repo(tmp_path)
    pin_files(tmp_path, "v4.33.0-rc1")
    assert pin_files(tmp_path, "v4.33.0-rc1") == []


def test_pin_files_rejects_a_bad_version(tmp_path: Path) -> None:
    """A non-release version string fails before touching any file."""
    _write_repo(tmp_path)
    with pytest.raises(SystemExit, match="not a release tag"):
        pin_files(tmp_path, "main")
    assert "v4.32.0-rc1" in (tmp_path / "lean-toolchain").read_text()


def test_pin_files_reports_a_missing_pin(tmp_path: Path) -> None:
    """A missing pin file is an error, not a silent skip."""
    _write_repo(tmp_path)
    (tmp_path / "docbuild" / "lean-toolchain").unlink()
    with pytest.raises(SystemExit, match="missing pin file"):
        pin_files(tmp_path, "v4.33.0-rc1")


# --------------------------------------------------------------------------- #
# Build-log triage
# --------------------------------------------------------------------------- #
BUILD_LOG = """\
info: [1/900] Building LeanPool.Alpha.Core
error: ./LeanPool/Alpha/Core.lean:12:2: unknown identifier 'Set.diff_eq'
  the goal was
    ⊢ s \\ t = s ∩ tᶜ
info: [2/900] Building LeanPool.Beta.Main
warning: ./LeanPool/Beta/Main.lean:3:0: `Symmetric` is deprecated
info: [3/900] Building LeanPool.Gamma.Basic
info: build completed
"""


def test_parse_build_log_buckets_by_project() -> None:
    """Each diagnostic lands on the project whose file it names."""
    buckets = parse_build_log(BUILD_LOG)
    assert set(buckets) == {"Alpha", "Beta"}
    assert len(buckets["Alpha"].errors) == 3  # message plus two goal lines
    assert buckets["Beta"].warnings and not buckets["Beta"].errors


def test_parse_build_log_attaches_continuation_lines() -> None:
    """Indented goal-state lines stay with the error they explain."""
    errors = parse_build_log(BUILD_LOG)["Alpha"].errors
    assert "unknown identifier" in errors[0]
    assert any("⊢" in line for line in errors)


def test_build_report_separates_broken_from_warned() -> None:
    """Only projects with errors become repair jobs."""
    report = build_report(BUILD_LOG)
    assert report["broken_projects"] == ["Alpha"]
    assert report["warned_projects"] == ["Beta"]
    assert report["clean"] is False


def test_build_report_on_a_clean_build() -> None:
    """A build with no diagnostics reports clean and schedules no repairs."""
    report = build_report("info: [1/1] Building LeanPool.Alpha\ninfo: done\n")
    assert report["clean"] is True
    assert report["broken_projects"] == []


def test_project_with_errors_is_not_also_listed_as_warned() -> None:
    """A project that fails outright is a repair job, not a warning job."""
    log = (
        "info: [1/2] Building LeanPool.Alpha.Core\n"
        "warning: ./LeanPool/Alpha/Core.lean:1:0: unused variable\n"
        "error: ./LeanPool/Alpha/Core.lean:9:0: type mismatch\n"
    )
    report = build_report(log)
    assert report["broken_projects"] == ["Alpha"]
    assert report["warned_projects"] == []


def test_diagnostic_without_a_path_uses_the_building_context() -> None:
    """A message lake prints against a module still finds its project."""
    log = "info: [1/2] Building LeanPool.Delta.Core\nerror: no such file or directory\n"
    assert build_report(log)["broken_projects"] == ["Delta"]


def test_excerpts_are_capped() -> None:
    """A project that fails everywhere cannot flood the repair prompt."""
    lines = ["info: [1/1] Building LeanPool.Alpha.Core"]
    lines += [f"error: ./LeanPool/Alpha/Core.lean:{i}:0: boom" for i in range(200)]
    entry = build_report("\n".join(lines))["broken"][0]
    assert entry["error_count"] == 200
    assert len(entry["errors"]) == 40


def test_report_command_writes_json(tmp_path: Path) -> None:
    """The report subcommand persists the artifact the workflow uploads."""
    log = tmp_path / "build.log"
    log.write_text(BUILD_LOG)
    output = tmp_path / "report.json"
    assert main(["report", "--log", str(log), "--output", str(output)]) == 0
    assert '"broken_projects"' in output.read_text()
