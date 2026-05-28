"""Tests for deterministic partial-port auditing."""

from pathlib import Path

from lean_pool.partial_port_audit import (
    LeanFile,
    LeanStats,
    count_lean_loc,
    evaluate_stats,
    has_forbidden_upstream_construct,
    imported_modules,
    module_name,
    normalize_relative_path,
    normalize_stem,
    stats_from_worktree,
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


def test_forbidden_upstream_construct_ignores_comments() -> None:
    """Forbidden words in comments do not make an upstream file unimportable."""
    text = """
-- axiom oldName : True
/- sorry -/
def x := 1
"""
    assert not has_forbidden_upstream_construct(text)


def test_stats_from_worktree_skips_unimportable_upstream_files(tmp_path) -> None:
    """Upstream files with sorries or unchecked declarations do not count."""
    (tmp_path / "Good.lean").write_text("def x := 1\n", encoding="utf-8")
    (tmp_path / "Axiom.lean").write_text(
        "axiom missingProof : True\n", encoding="utf-8"
    )
    (tmp_path / "Sorry.lean").write_text(
        "theorem t : True := by sorry\n", encoding="utf-8"
    )

    stats = stats_from_worktree(tmp_path)

    assert [file.path for file in stats.files] == ["Good.lean"]


def test_stats_from_worktree_skips_dependents_of_unimportable_files(
    tmp_path,
) -> None:
    """Files that import unimportable upstream modules do not count."""
    (tmp_path / "Bad.lean").write_text(
        "theorem missing : True := by sorry\n", encoding="utf-8"
    )
    (tmp_path / "UsesBad.lean").write_text("import Bad\ndef y := 1\n", encoding="utf-8")
    (tmp_path / "UsesUsesBad.lean").write_text(
        "import UsesBad\ndef z := 1\n", encoding="utf-8"
    )
    (tmp_path / "Good.lean").write_text("def x := 1\n", encoding="utf-8")

    stats = stats_from_worktree(tmp_path)

    assert [file.path for file in stats.files] == ["Good.lean"]


def test_imported_modules_ignores_comments() -> None:
    """Commented-out imports do not affect dependency analysis."""
    text = """
-- import Commented
/- import Blocked -/
import Real.One Real.Two
"""
    assert imported_modules(text) == ("Real.One", "Real.Two")


def test_module_name_uses_repository_relative_path() -> None:
    """Repository-relative paths map to dotted Lean module names."""
    assert module_name(Path("Foo/Bar.lean")) == "Foo.Bar"


def test_normalize_stem_matches_renamed_camel_case_file() -> None:
    """Snake-case upstream files can match CamelCase imported files."""
    assert normalize_stem("Lean4/directed_van_kampen.lean") == normalize_stem(
        "LeanPool/DirectedTopologyLean4/DirectedVanKampen.lean"
    )


def test_normalize_relative_path_drops_project_prefix() -> None:
    """Upstream and LeanPool project roots are ignored for same-file checks."""
    assert normalize_relative_path(
        "Monlib/LinearAlgebra/QuantumSet/Basic.lean"
    ) == normalize_relative_path("LeanPool/Monlib4/LinearAlgebra/QuantumSet/Basic.lean")


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


def test_evaluate_stats_flags_truncated_matched_file() -> None:
    """A same-path file with too little LOC is still suspicious."""
    imported = LeanStats(
        (
            LeanFile(
                "LeanPool/Monlib4/LinearAlgebra/QuantumSet/Basic.lean",
                120,
                "basic",
            ),
            LeanFile("LeanPool/Monlib4/Other.lean", 900, "other"),
        )
    )
    upstream = LeanStats(
        (
            LeanFile("Monlib/LinearAlgebra/QuantumSet/Basic.lean", 1000, "basic"),
            LeanFile("Monlib/Other.lean", 900, "other"),
        )
    )

    finding = evaluate_stats("LeanPool.Monlib4", "owner/monlib4", imported, upstream)

    assert finding is not None
    assert finding.truncated_files == (
        "Monlib/LinearAlgebra/QuantumSet/Basic.lean (120/1000 LOC)",
    )


def test_evaluate_stats_accepts_close_import() -> None:
    """A near-complete import passes the tolerance check."""
    imported = LeanStats((LeanFile("LeanPool/Foo/Main.lean", 920, "main"),))
    upstream = LeanStats((LeanFile("Foo/Main.lean", 1000, "main"),))
    assert evaluate_stats("LeanPool.Foo", "owner/foo", imported, upstream) is None
