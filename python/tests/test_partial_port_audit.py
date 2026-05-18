"""Tests for deterministic partial-port auditing."""

from lean_pool.partial_port_audit import (
    LeanFile,
    LeanStats,
    count_lean_loc,
    evaluate_stats,
    normalize_stem,
)


def test_count_lean_loc_ignores_comments_and_blank_lines() -> None:
    """Comment-only and blank lines do not inflate LOC counts."""
    text = """
-- a line comment

/- a block
comment -/
def x := 1
theorem y : x = 1 := rfl
"""
    assert count_lean_loc(text) == 2


def test_normalize_stem_matches_renamed_camel_case_file() -> None:
    """Snake-case upstream files can match CamelCase imported files."""
    assert normalize_stem("Lean4/directed_van_kampen.lean") == normalize_stem(
        "LeanPool/DirectedTopologyLean4/DirectedVanKampen.lean"
    )


def test_evaluate_stats_flags_large_loc_gap() -> None:
    """A small imported slice of a larger upstream project is suspicious."""
    imported = LeanStats((LeanFile("LeanPool/Fineqs/Main.lean", 90, "main"),))
    upstream = LeanStats((LeanFile("fineqs/Main.lean", 570, "main"),))
    finding = evaluate_stats("LeanPool.Fineqs", "owner/fineqs", imported, upstream)
    assert finding is not None
    assert finding.imported_loc == 90
    assert finding.upstream_loc == 570


def test_evaluate_stats_flags_missing_large_file() -> None:
    """A headline-sized upstream file missing from the import is suspicious."""
    imported = LeanStats(
        (
            LeanFile("LeanPool/DirectedTopologyLean4/Dipath.lean", 500, "dipath"),
            LeanFile(
                "LeanPool/DirectedTopologyLean4/Dihomotopy.lean",
                500,
                "dihomotopy",
            ),
        )
    )
    upstream = LeanStats(
        (
            LeanFile("Lean4/dipath.lean", 500, "dipath"),
            LeanFile("Lean4/dihomotopy.lean", 500, "dihomotopy"),
            LeanFile("Lean4/directed_van_kampen.lean", 1000, "directedvankampen"),
        )
    )
    finding = evaluate_stats(
        "LeanPool.DirectedTopologyLean4", "owner/directed", imported, upstream
    )
    assert finding is not None
    assert finding.missing_files == ("Lean4/directed_van_kampen.lean",)


def test_evaluate_stats_lists_largest_missing_files_for_ratio_gap() -> None:
    """Suspicious partial imports report useful filenames even for small files."""
    imported = LeanStats((LeanFile("LeanPool/Foo/Main.lean", 100, "main"),))
    upstream = LeanStats(
        (
            LeanFile("Foo/Main.lean", 100, "main"),
            LeanFile("Foo/SkippedA.lean", 80, "skippeda"),
            LeanFile("Foo/SkippedB.lean", 60, "skippedb"),
            LeanFile("Foo/SkippedC.lean", 40, "skippedc"),
        )
    )
    finding = evaluate_stats("LeanPool.Foo", "owner/foo", imported, upstream)
    assert finding is not None
    assert finding.missing_files == (
        "Foo/SkippedA.lean",
        "Foo/SkippedB.lean",
        "Foo/SkippedC.lean",
    )


def test_evaluate_stats_accepts_close_import() -> None:
    """A near-complete import passes the tolerance check."""
    imported = LeanStats((LeanFile("LeanPool/Foo/Main.lean", 920, "main"),))
    upstream = LeanStats((LeanFile("Foo/Main.lean", 1000, "main"),))
    assert evaluate_stats("LeanPool.Foo", "owner/foo", imported, upstream) is None
