/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Target

/-!
# Rational and degree-two places

The `4 × 4` Hankel rank-two classification is intentionally concrete.  It is
a closed calculation on 128 coefficient vectors and 16 cubic minors, not a
search over circuits.  Subsequent proofs consume the named rational, tangent,
and degree-two-place families rather than raw bit patterns.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Determinant of a `3 × 3` matrix in characteristic two. -/
@[expose] def detThree (M : Matrix (Fin 3) (Fin 3) F₂) : F₂ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 2 * M 2 1 +
  M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
  M 0 2 * M 1 0 * M 2 1 + M 0 2 * M 1 1 * M 2 0

/-- A cubic minor obtained by deleting one row and one column. -/
@[expose] def hankelMinorThree (c : TargetCoeff) (dropRow dropCol : Fin 4) : F₂ :=
  detThree fun i j =>
    hankelMatrix c (dropRow.succAbove i) (dropCol.succAbove j)

/-- Algebraic rank-at-most-two condition: all `3 × 3` minors vanish. -/
@[expose] def HankelRankLETwo (c : TargetCoeff) : Prop :=
  ∀ dropRow dropCol : Fin 4, hankelMinorThree c dropRow dropCol = 0

instance (c : TargetCoeff) : Decidable (HankelRankLETwo c) := by
  unfold HankelRankLETwo
  infer_instance

/-- The sixteen coefficient words in the manuscript's rank-at-most-two
table, including zero. -/
@[expose] def rankTwoWord : Fin 16 → TargetCoeff :=
  ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0],
    ![0, 1, 1, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 0, 1, 0, 1],
    ![1, 0, 1, 1, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 1, 0, 1],
    ![1, 1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1, 1]]

/-- Complete binary rank-two Hankel classification. -/
theorem rankTwo_target_classification (c : TargetCoeff) :
    HankelRankLETwo c ↔ ∃ i : Fin 16, c = rankTwoWord i := by
  revert c
  decide +kernel

/-- Direct algebraic description of the rational-place span. -/
@[expose] def IsRationalCoeff (c : TargetCoeff) : Prop :=
  ∃ α β γ : F₂,
    c = α • rZeroCoeff + β • rOneCoeff + γ • rInfinityCoeff

instance (c : TargetCoeff) : Decidable (IsRationalCoeff c) :=
  Fintype.decidableExistsFintype

/-- Six tangent words followed by the three nonzero degree-two-place words. -/
@[expose]
def outsideRankTwoWord : Fin 9 → TargetCoeff :=
  ![![0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0],
    ![1, 0, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 0, 1, 1, 0],
    ![1, 1, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 0, 1, 1]]

/-- Every nonzero rank-at-most-two target outside the rational-place span is
one of the six rational tangents or one of the three degree-two-place forms. -/
theorem outside_rankTwo_classification (c : TargetCoeff) :
    HankelRankLETwo c ∧ c ≠ 0 ∧ ¬ IsRationalCoeff c ↔
      ∃ i : Fin 9, c = outsideRankTwoWord i := by
  revert c
  decide +kernel

/-- The two-dimensional closed degree-two place. -/
def degreeTwoPlaceBasis : Fin 2 → TargetCoeff :=
  ![![0, 1, 1, 0, 1, 1, 0], ![1, 1, 0, 1, 1, 0, 1]]

/-- The target coefficient space of the irreducible quadratic place. -/
def degreeTwoCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range degreeTwoPlaceBasis)

/-- The first Hasse-jet direction at each rational place, with its translate
by the place itself. -/
@[expose]
def tangentWord : Fin 6 → TargetCoeff :=
  ![outsideRankTwoWord 0, outsideRankTwoWord 1,
    outsideRankTwoWord 2, outsideRankTwoWord 3,
    outsideRankTwoWord 4, outsideRankTwoWord 5]

theorem degreeTwoPlace_linearIndependent :
    LinearIndependent F₂ degreeTwoPlaceBasis := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have hcoord := congrFun h (if i = 0 then 2 else 0)
  fin_cases i <;>
    simp only [degreeTwoPlaceBasis, Fin.zero_eta, Fin.isValue, ↓reduceIte, Finset.sum_apply,
      Pi.smul_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one, smul_eq_mul,
      Fin.sum_univ_succ, Matrix.cons_val_zero, mul_one, Finset.univ_unique,
      Fin.default_eq_zero, Matrix.cons_val_succ, mul_zero, Finset.sum_const_zero, add_zero,
      Pi.zero_apply, Fin.mk_one, one_ne_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
      zero_add] at hcoord ⊢
  · exact hcoord
  · exact hcoord

theorem degreeTwoCoeffSpace_finrank :
    Module.finrank F₂ degreeTwoCoeffSpace = 2 := by
  exact finrank_span_eq_card degreeTwoPlace_linearIndependent

theorem rationalCoeffSpace_eq :
    rationalCoeffSpace =
      Submodule.span F₂ (Set.range ![rZeroCoeff, rOneCoeff, rInfinityCoeff]) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro c (rfl | rfl | rfl)
    · apply Submodule.subset_span
      exact ⟨0, by simp⟩
    · apply Submodule.subset_span
      exact ⟨1, by simp⟩
    · apply Submodule.subset_span
      exact ⟨2, by simp⟩
  · apply Submodule.span_le.mpr
    rintro c ⟨i, rfl⟩
    fin_cases i <;> apply Submodule.subset_span
    all_goals simp

end

end N4
end UnrestrictedBooleanMul
