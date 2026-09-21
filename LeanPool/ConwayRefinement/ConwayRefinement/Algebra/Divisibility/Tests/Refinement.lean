/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.NormNum

/-!
# Tests for four-factor refinement

The natural numbers provide nonzero and zero examples of the public refinement interface.
-/

public section

namespace Tests

/-- The natural numbers give a four-factor refinement model with `0 ≠ 1` and nonunit elements. -/
theorem nat_hasFourFactorRefinement : HasFourFactorRefinement ℕ :=
  hasFourFactorRefinement_of_decompositionMonoid

theorem nat_hasFourFactorRefinement_iff_decompositionMonoid :
    HasFourFactorRefinement ℕ ↔ DecompositionMonoid ℕ :=
  hasFourFactorRefinement_iff_decompositionMonoid

/-- The equality `6 * 35 = 10 * 21` has the refinement `(2, 3, 5, 7)`. -/
theorem nat_six_thirty_five_ten_twenty_one_refinement :
    ∃ e f g h : ℕ, 6 = e * f ∧ 35 = g * h ∧ 10 = e * g ∧ 21 = f * h :=
  ⟨2, 3, 5, 7, by norm_num⟩

theorem nat_zero_left_refinement (b d : ℕ) :
    ∃ e f g h : ℕ, 0 = e * f ∧ b = g * h ∧ 0 = e * g ∧ d = f * h :=
  nat_hasFourFactorRefinement.refine (by simp)

theorem nat_zero_right_refinement (b c : ℕ) :
    ∃ e f g h : ℕ, 0 = e * f ∧ b = g * h ∧ c = e * g ∧ 0 = f * h :=
  nat_hasFourFactorRefinement.refine (by simp)

end Tests
