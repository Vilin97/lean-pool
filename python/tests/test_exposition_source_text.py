"""Tests for statement slicing and kind refinement from Lean source text."""

from __future__ import annotations

from lean_pool.exposition.source_text import (
    SourceFile,
    module_skeleton,
    statement_slice,
)

THEOREM_BLOCK = """\
/-- Doc for foo. -/
@[simp]
private theorem foo (n : Nat) :
    n + 0 = n := by
  simp
"""


def _slice(
    text: str,
    declaration_range: list[int],
    selection: list[int],
    fallback: str = "theorem",
) -> tuple[str, str]:
    """Run statement_slice over freshly parsed source text (kind, statement)."""
    kind, statement, _ = _slice_full(text, declaration_range, selection, fallback)
    return kind, statement


def _slice_full(
    text: str,
    declaration_range: list[int],
    selection: list[int],
    fallback: str = "theorem",
) -> tuple[str, str, tuple[int, int] | None]:
    """Run statement_slice over freshly parsed source text (full result)."""
    source = SourceFile.from_text(text)
    return statement_slice(source, declaration_range, selection, fallback)


def test_theorem_with_assignment_boundary() -> None:
    """Doc comment, attribute, and modifier are skipped; body is cut at :=."""
    kind, statement, statement_end = _slice_full(THEOREM_BLOCK, [1, 0, 5, 6], [3, 16])
    assert kind == "theorem"
    assert statement == "theorem foo (n : Nat) :\n    n + 0 = n"
    # The boundary sits at the `:=` on line 4, column 14 (0-based codepoints).
    assert statement_end == (4, 14)


def test_module_skeleton_imports() -> None:
    """module_skeleton splits external and pool-internal imports."""
    text = (
        "import Mathlib.Order.Basic\n"
        "import LeanPool.Other.Module\n"
        "\n"
        "/-! Module doc: skipped. -/\n"
        "\n"
        "namespace Demo\n"
        "def x : Nat := 1\n"
        "end Demo\n"
    )
    skeleton = module_skeleton(SourceFile.from_text(text))
    assert skeleton.external_imports == ["Mathlib.Order.Basic"]
    assert skeleton.local_imports == ["LeanPool.Other.Module"]


def test_lemma_keyword_refines_theorem_kind() -> None:
    """A source `lemma` refines the extractor's coarse `theorem` kind."""
    text = "lemma bar : True := trivial\n"
    kind, statement = _slice(text, [1, 0, 1, 27], [1, 6], fallback="theorem")
    assert kind == "lemma"
    assert statement == "lemma bar : True"


def test_def_with_where_boundary() -> None:
    """A structure-instance body introduced by `where` ends the statement."""
    text = "def origin : Point where\n  x := 1\n  y := 2\n"
    kind, statement = _slice(text, [1, 0, 3, 8], [1, 4], fallback="def")
    assert kind == "def"
    assert statement == "def origin : Point"


def test_inductive_arms_boundary() -> None:
    """Constructor arms (no `=>`) still end an inductive's statement."""
    text = "inductive Color\n  | red\n  | green\n"
    kind, statement = _slice(text, [1, 0, 3, 9], [1, 10], fallback="inductive")
    assert kind == "inductive"
    assert statement == "inductive Color"


def test_class_inductive_reports_class() -> None:
    """`class inductive` reports kind `class` and keeps the full header."""
    text = "class inductive Weird (α : Type) : Type\n  | intro : Weird α\n"
    kind, statement = _slice(text, [1, 0, 2, 19], [1, 16], fallback="class")
    assert kind == "class"
    assert statement == "class inductive Weird (α : Type) : Type"


def test_generated_decl_with_midline_range_gets_empty_statement() -> None:
    """Attribute-generated decls (range at a mid-line token) blank the statement."""
    text = "@[to_additive]\ntheorem prod_thing : True := trivial\n"
    kind, statement = _slice(text, [1, 2, 1, 13], [1, 2], fallback="theorem")
    assert kind == "theorem"
    assert statement == ""


def test_deriving_generated_instance_gets_empty_statement() -> None:
    """`deriving`-generated instances point mid-line and blank the statement."""
    text = "structure Point where\n  x : Nat\n  deriving DecidableEq\n"
    kind, statement = _slice(text, [3, 11, 3, 22], [3, 11], fallback="instance")
    assert kind == "instance"
    assert statement == ""


def test_unknown_keyword_at_line_start_keeps_raw_slice() -> None:
    """A column-0 non-declaration command (e.g. notation) keeps its source text."""
    text = 'notation "⟦" x "⟧" => quot x\n'
    kind, statement = _slice(text, [1, 0, 1, 28], [1, 0], fallback="def")
    assert kind == "def"
    assert statement.startswith("notation")


def test_statement_capped_at_1200_characters() -> None:
    """Over-long statements are cut to 1200 characters ending in an ellipsis."""
    long_type = " → ".join(["Nat"] * 400)
    text = f"def long : {long_type} := fun value => value\n"
    kind, statement = _slice(text, [1, 0, 1, len(text) - 1], [1, 4], fallback="def")
    assert kind == "def"
    assert 1150 <= len(statement) <= 1200
    assert statement.endswith("…")
    assert statement.startswith("def long : Nat")
