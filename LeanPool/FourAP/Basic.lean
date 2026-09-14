/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
# The language of the paper

This file fixes the conventions used to formalize the paper
“A 4AP-free permutation of the positive integers”.  The construction takes place
in `ℕ`, which in Lean includes zero.  The final theorem shifts the values by one.

An arithmetic progression is expressed using the two equations
`a + c = 2 * b` and `b + d = 2 * c`.  For natural-number entries these equations,
together with `a ≠ b`, are equivalent to having a nonzero **integer** common
difference.  Thus decreasing progressions are included throughout.
-/

namespace FourAP

/-- Four consecutive terms of a nonconstant arithmetic progression, as in the
paper's main theorem. The equations avoid truncated subtraction in `ℕ`. -/
def IsAP4 (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a + c = 2 * b ∧ b + d = 2 * c

/-- The equation-based representation used in this formalization is equivalent
to the paper's progression `a, a+r, a+2r, a+3r`, with a nonzero **integer**
common difference. In particular, decreasing progressions are included. -/
theorem isAP4_iff_integer_progression {a b c d : ℕ} :
    IsAP4 a b c d ↔ ∃ r : ℤ, r ≠ 0 ∧
      (b : ℤ) = (a : ℤ) + r ∧
      (c : ℤ) = (a : ℤ) + 2 * r ∧
      (d : ℤ) = (a : ℤ) + 3 * r := by
  constructor
  · rintro ⟨hne, h₁, h₂⟩
    refine ⟨(b : ℤ) - (a : ℤ), ?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨r, hr, hb, hc, hd⟩
    exact ⟨by omega, by omega, by omega⟩

/-- The paper's definition of a 4AP-free order, applied to a strict relation.
The relation need not be bundled as a linear order for this predicate. -/
def APFree (R : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, IsAP4 a b c d → R a b → R b c → R c d → False

/-- The completion `𝒞(P)` from the paragraph preceding Lemma 1, with an arbitrary
background relation `R`.  `List.idxOf` is the length of the list for a missing
entry, so the first disjunct orders the prefix and puts it before the tail. -/
def Completion (R : ℕ → ℕ → Prop) (P : List ℕ) (a b : ℕ) : Prop :=
  P.idxOf a < P.idxOf b ∨ (a ∉ P ∧ b ∉ P ∧ R a b)

/-- A safe word in the sense of the paper: a word without repetitions whose
completion is 4AP-free. The background order is made explicit here. -/
def Safe (R : ℕ → ℕ → Prop) (P : List ℕ) : Prop :=
  P.Nodup ∧ APFree (Completion R P)

end FourAP
