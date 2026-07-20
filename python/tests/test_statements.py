"""Tests for the statement-change parser used by the proof profile.

``scripts/proof-profile/statements.py`` is fetched and run standalone in CI,
so it lives outside the ``lean_pool`` package; add its directory to the path
before importing it.
"""

from __future__ import annotations

import pathlib
import sys

SCRIPTS = pathlib.Path(__file__).resolve().parents[2] / "scripts" / "proof-profile"
sys.path.insert(0, str(SCRIPTS))

import statements  # noqa: E402

BASE = """
namespace Foo

theorem add_comm' (a b : Nat) : a + b = b + a := by
  have h : a + b = b + a := Nat.add_comm a b
  exact h

def double (n : Nat) : Nat := n + n

lemma embedded : (⟨1, by simp⟩ : {n : Nat // n = 1}).1 = 1 := by rfl

end Foo
"""


def test_pure_golf_changes_no_statement() -> None:
    """Golfing proofs and definition bodies is not a statement change."""
    head = """
namespace Foo

theorem add_comm' (a b : Nat) : a + b = b + a := by
  simp_all [Nat.add_comm]

def double (n : Nat) : Nat := 2 * n

lemma embedded : (⟨1, by omega⟩ : {n : Nat // n = 1}).1 = 1 := by rfl

end Foo
"""
    diff = statements.compare_statements(BASE, head)
    assert diff.statement_changed == []
    assert diff.binder_renamed == []
    assert diff.added == []
    assert diff.removed == []
    assert diff.head_decl_count == 3


def test_real_type_change_is_flagged() -> None:
    """Changing a declaration's type counts as a statement change."""
    head = BASE.replace(
        "def double (n : Nat) : Nat := n + n",
        "def double (n : Int) : Int := n + n",
    )
    diff = statements.compare_statements(BASE, head)
    assert diff.statement_changed == ["Foo.double"]
    assert diff.binder_renamed == []


def test_underscore_binder_rename_is_not_a_statement_change() -> None:
    """Marking a hypothesis unused (`h` -> `_h`) preserves the proposition."""
    base = """
theorem t (a b : Nat) (h : 0 < b) : a + 0 = a := by
  rw [Nat.add_zero]
"""
    head = """
theorem t (a b : Nat) (_h : 0 < b) : a + 0 = a := by
  simp
"""
    diff = statements.compare_statements(base, head)
    assert diff.statement_changed == []
    assert diff.binder_renamed == ["t"]


def test_added_and_removed_declarations() -> None:
    """Declarations gained or lost are reported separately."""
    head = """
namespace Foo

theorem add_comm' (a b : Nat) : a + b = b + a := by simp_all

def double (n : Nat) : Nat := n + n

theorem brand_new : True := trivial

end Foo
"""
    diff = statements.compare_statements(BASE, head)
    assert diff.statement_changed == []
    assert diff.added == ["Foo.brand_new"]
    assert diff.removed == ["Foo.embedded"]


def test_leading_absolute_value_bar_is_not_an_arm() -> None:
    """A line-leading `|x| ≤ …` in the type must not truncate the signature.

    Regression: `|…|` at line start was misread as an equation-compiler arm
    when the proof contained a `=>`, so golfing the proof (adding a `fun … =>`)
    produced a spurious statement change even though the type was identical.
    """
    base = """
lemma bound (f : Nat → Real) (h : 0 < 1) :
    ∃ C : Real, ∀ n,
      |Real.log (f n)| ≤ C := by
  intro n
  exact something n
"""
    head = """
lemma bound (f : Nat → Real) (h : 0 < 1) :
    ∃ C : Real, ∀ n,
      |Real.log (f n)| ≤ C :=
  fun n => something n
"""
    diff = statements.compare_statements(base, head)
    assert diff.statement_changed == []
    assert diff.binder_renamed == []


def test_identical_source_is_noop() -> None:
    """Comparing a file against itself reports nothing."""
    diff = statements.compare_statements(BASE, BASE)
    assert diff.statement_changed == []
    assert diff.added == []
    assert diff.removed == []
