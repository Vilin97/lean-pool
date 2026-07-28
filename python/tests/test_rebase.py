"""Tests for deterministic import-PR conflict resolution."""

from __future__ import annotations

from pathlib import Path

from lean_pool.rebase import (
    main,
    merge_registry,
    render_index,
    resolvable,
    split_cards,
)

BASE = """projects:
  - slug: alpha
    title: Alpha
    entry_module: LeanPool.Alpha
  - slug: beta
    title: Beta
    entry_module: LeanPool.Beta
"""

# main advanced: an import PR for `gamma` merged ahead of ours.
OURS = """projects:
  - slug: alpha
    title: Alpha
    entry_module: LeanPool.Alpha
  - slug: beta
    title: Beta
    entry_module: LeanPool.Beta
  - slug: gamma
    title: Gamma
    entry_module: LeanPool.Gamma
"""

# our PR, branched from BASE, adding `delta`.
THEIRS = """projects:
  - slug: alpha
    title: Alpha
    entry_module: LeanPool.Alpha
  - slug: beta
    title: Beta
    entry_module: LeanPool.Beta
  - slug: delta
    title: Delta
    entry_module: LeanPool.Delta
"""


# --------------------------------------------------------------------------- #
# Index regeneration
# --------------------------------------------------------------------------- #
def test_render_index_is_sorted_imports(tmp_path: Path) -> None:
    """The index lists every Lean file in the tree, sorted."""
    pool = tmp_path / "LeanPool"
    (pool / "Beta").mkdir(parents=True)
    (pool / "Alpha.lean").write_text("")
    (pool / "Beta" / "Core.lean").write_text("")
    (pool / "Beta.lean").write_text("")
    assert render_index(tmp_path) == (
        "import LeanPool.Alpha\nimport LeanPool.Beta\nimport LeanPool.Beta.Core\n"
    )


def test_render_index_ignores_non_lean_files(tmp_path: Path) -> None:
    """projects.yml sits inside LeanPool/ and is not a module."""
    pool = tmp_path / "LeanPool"
    pool.mkdir(parents=True)
    (pool / "Alpha.lean").write_text("")
    (pool / "projects.yml").write_text("projects: []\n")
    assert render_index(tmp_path) == "import LeanPool.Alpha\n"


def test_render_index_reproduces_the_committed_index() -> None:
    """The real index regenerates byte-for-byte, so no Lean build is needed."""
    root = Path(__file__).resolve().parents[2]
    assert render_index(root) == (root / "LeanPool.lean").read_text(encoding="utf-8")


# --------------------------------------------------------------------------- #
# Registry merging
# --------------------------------------------------------------------------- #
def test_split_cards_round_trips() -> None:
    """Header plus every card block reproduces the file exactly."""
    header, cards = split_cards(OURS)
    assert [slug for slug, _ in cards] == ["alpha", "beta", "gamma"]
    assert header + "".join(block for _, block in cards) == OURS


def test_merge_keeps_both_additions() -> None:
    """The merged registry has the card main added and the card we added."""
    merged = merge_registry(BASE, OURS, THEIRS)
    slugs = [slug for slug, _ in split_cards(merged)[1]]
    assert slugs == ["alpha", "beta", "gamma", "delta"]


def test_merge_preserves_existing_cards_verbatim() -> None:
    """Untouched cards are copied as text, never re-serialised."""
    merged = merge_registry(BASE, OURS, THEIRS)
    assert merged.startswith(OURS)
    assert "  - slug: delta\n    title: Delta\n" in merged


def test_merge_is_a_noop_when_the_branch_added_nothing() -> None:
    """A branch that only edits existing cards yields the base unchanged."""
    assert merge_registry(BASE, OURS, BASE) == OURS


def test_merge_does_not_duplicate_an_already_merged_card() -> None:
    """If our card reached the base first, it is not appended twice."""
    merged = merge_registry(BASE, THEIRS, THEIRS)
    assert [slug for slug, _ in split_cards(merged)[1]] == ["alpha", "beta", "delta"]


def test_merge_separates_appended_cards(tmp_path: Path) -> None:
    """A base missing its trailing newline still yields valid YAML."""
    merged = merge_registry(BASE, OURS.rstrip("\n"), THEIRS)
    assert "entry_module: LeanPool.Gamma\n  - slug: delta" in merged


def test_merge_result_parses_as_yaml() -> None:
    """The text-level merge must still produce loadable YAML."""
    import yaml

    data = yaml.safe_load(merge_registry(BASE, OURS, THEIRS))
    assert [card["slug"] for card in data["projects"]] == [
        "alpha",
        "beta",
        "gamma",
        "delta",
    ]


# --------------------------------------------------------------------------- #
# Scope
# --------------------------------------------------------------------------- #
def test_resolvable_only_covers_the_two_mechanical_files() -> None:
    """A conflict in real Lean content is not ours to resolve."""
    assert resolvable(["LeanPool.lean"])
    assert resolvable(["LeanPool.lean", "LeanPool/projects.yml"])
    assert not resolvable(["LeanPool/Alpha/Core.lean"])
    assert not resolvable(["LeanPool.lean", "LeanPool/Alpha/Core.lean"])
    assert not resolvable([])


def test_resolvable_command_exit_codes(tmp_path: Path) -> None:
    """The workflow branches on this command's exit code."""
    good = tmp_path / "good.txt"
    good.write_text("LeanPool.lean\nLeanPool/projects.yml\n")
    assert main(["resolvable", "--conflicts", str(good)]) == 0

    bad = tmp_path / "bad.txt"
    bad.write_text("LeanPool.lean\nLeanPool/Alpha/Core.lean\n")
    assert main(["resolvable", "--conflicts", str(bad)]) == 1


def test_registry_command_writes_the_merge(tmp_path: Path) -> None:
    """The registry subcommand writes the merged file into the repo."""
    (tmp_path / "LeanPool").mkdir()
    (tmp_path / "LeanPool" / "projects.yml").write_text(OURS)
    for name, text in (("base", BASE), ("ours", OURS), ("theirs", THEIRS)):
        (tmp_path / name).write_text(text)
    assert (
        main(
            [
                "registry",
                "--repo",
                str(tmp_path),
                "--base",
                str(tmp_path / "base"),
                "--ours",
                str(tmp_path / "ours"),
                "--theirs",
                str(tmp_path / "theirs"),
            ]
        )
        == 0
    )
    merged = (tmp_path / "LeanPool" / "projects.yml").read_text()
    assert "delta" in merged and "gamma" in merged
