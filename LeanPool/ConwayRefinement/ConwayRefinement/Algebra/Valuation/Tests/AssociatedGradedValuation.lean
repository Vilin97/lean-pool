/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.OfValuation
public import Mathlib.Algebra.Order.Ring.Rat

import Mathlib.Algebra.Ring.Prod

/-!
# API checks for leading-grade valuations

A two-grade direct sum over `ℤ` verifies that leading grade uses the largest nonzero grade and
that ordinary addition of grades governs products. The asymmetric grades ensure that the client
is not merely checking the grade-zero ring inherited from the coefficient ring.

The first-projection valuation on `ℚ × ℚ`, read as a multiplicative max-additive degree, is
nonseparated, while its associated-graded valuation is separated. Its nonzero kernel element has
zero initial form, and a representative outside the kernel retains its degree under the
initial-form map. These certificates exercise the distinction between the original kernel and the
zero element of the associated graded ring.
-/

public noncomputable section

open MaxAddDegree
open scoped DirectSum

namespace Tests

abbrev LeadingGradeFixture := DirectSum ℕ (fun _ ↦ ℤ)

def leadingGradeLow : LeadingGradeFixture :=
  DirectSum.of (fun _ : ℕ ↦ ℤ) 1 2

def leadingGradeHigh : LeadingGradeFixture :=
  DirectSum.of (fun _ : ℕ ↦ ℤ) 3 5

/-- The sum of components in grades one and three has leading grade three. -/
theorem leadingGrade_sum_fixture :
    DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) (leadingGradeLow + leadingGradeHigh) = 3 := by
  have hlow : DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeLow = 1 := by
    rw [leadingGradeLow]
    exact DirectSum.leadingGrade_of _ (by norm_num)
  have hhigh : DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeHigh = 3 := by
    rw [leadingGradeHigh]
    exact DirectSum.leadingGrade_of _ (by norm_num)
  apply le_antisymm
  · calc
      DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) (leadingGradeLow + leadingGradeHigh) ≤
          max (DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeLow)
            (DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeHigh) :=
        DirectSum.leadingGrade_add_le_max _ _ _
      _ = 3 := by
        rw [hlow, hhigh]
        norm_num
  · apply DirectSum.grade_le_leadingGrade
    norm_num [leadingGradeLow, leadingGradeHigh, DirectSum.of_apply]

/-- The product of the grade-one and grade-three components has leading grade four. -/
theorem leadingGrade_mul_fixture :
    DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) (leadingGradeLow * leadingGradeHigh) = 4 := by
  have hlow : DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeLow = 1 := by
    rw [leadingGradeLow]
    exact DirectSum.leadingGrade_of _ (by norm_num)
  have hhigh : DirectSum.leadingGrade (fun _ : ℕ ↦ ℤ) leadingGradeHigh = 3 := by
    rw [leadingGradeHigh]
    exact DirectSum.leadingGrade_of _ (by norm_num)
  rw [DirectSum.leadingGrade_mul (fun _ : ℕ ↦ ℤ)
    (fun a b ha hb ↦ mul_ne_zero ha hb)]
  rw [hlow, hhigh]
  norm_num

def associatedFirstProjectionValuation : MaxAddDegree (ℚ × ℚ) ℕ :=
  MaxAddDegree.ofValuation
    ((1 : Valuation ℚ (WithZero (Multiplicative ℕ))).comap (RingHom.fst ℚ ℚ))

instance : associatedFirstProjectionValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

theorem associatedFirstProjectionValuation_not_isSeparated :
    ¬associatedFirstProjectionValuation.IsSeparated := by
  rw [MaxAddDegree.isSeparated_iff]
  push Not
  exact ⟨(0, 1), by simp [MaxAddDegree.ofValuation_apply,
    associatedFirstProjectionValuation, Valuation.one_apply_def]⟩

/-- The associated-graded valuation is separated even when the original valuation is not. -/
theorem associatedFirstProjectionValuation_associated_isSeparated :
    associatedFirstProjectionValuation.associatedGradedValuation.IsSeparated :=
  associatedFirstProjectionValuation.associatedGradedValuation_isSeparated

/-- A nonzero element of the original kernel has bottom-valued initial form. -/
theorem associatedFirstProjectionValuation_support_initialForm :
    associatedFirstProjectionValuation.associatedGradedValuation
      (associatedFirstProjectionValuation.initialForm (0, 1)) = ⊥ := by
  rw [MaxAddDegree.associatedGradedValuation_initialForm]
  simp [MaxAddDegree.ofValuation_apply, associatedFirstProjectionValuation,
    Valuation.one_apply_def]

/-- A representative outside the kernel retains its finite degree under the initial-form map. -/
theorem associatedFirstProjectionValuation_nonzero_initialForm :
    associatedFirstProjectionValuation.associatedGradedValuation
      (associatedFirstProjectionValuation.initialForm (1, 1)) = 0 := by
  rw [MaxAddDegree.associatedGradedValuation_initialForm]
  simp [MaxAddDegree.ofValuation_apply, associatedFirstProjectionValuation,
    Valuation.one_apply_def]

end Tests
