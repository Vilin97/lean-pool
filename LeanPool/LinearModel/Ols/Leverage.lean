/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic
import LeanPool.LinearModel.Ols.QuadForm
import LeanPool.LinearModel.Ols.ProjectionCLT

/-!
# The hat matrix and leverage

This file develops the projection geometry of a fixed design matrix `X`: the hat matrix
`H = X(XᵀX)⁻¹Xᵀ`, its diagonal leverage values `hᵢᵢ`, and the complement projector `I − H`.

Several minor results are derived, which are split into two sections: those concerning properties of
the hat matrix and complement projector, and those specifically relating to leverage.
-/

namespace LeanPool.LinearModel

noncomputable section

open Matrix Finset BigOperators

variable {n p : ℕ}


section Definitions

/-- The hat (projection) matrix: `H = X (XᵀX)⁻¹ Xᵀ`. -/
def hatMatrix (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  X * (Xᵀ * X)⁻¹ * Xᵀ

/-- The leverage of observation `i`, defined to be `Hᵢᵢ`. -/
def leverage (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) : ℝ :=
  hatMatrix X i i

/-- The complement projector: `P := I − H`. -/
def complementProj (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - hatMatrix X

end Definitions


section MatrixProperties

/-- The hat matrix is symmetric: `Hᵀ = H`. -/
lemma hatMatrix_symmetric (X : Matrix (Fin n) (Fin p) ℝ) :
    (hatMatrix X)ᵀ = hatMatrix X := by
  unfold hatMatrix
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
  Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- The hat matrix is idempotent: `H² = H`. -/
lemma hatMatrix_idempotent (X : Matrix (Fin n) (Fin p) ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    hatMatrix X * hatMatrix X = hatMatrix X := by
  unfold hatMatrix
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, ← Matrix.mul_assoc Xᵀ,
    Matrix.mul_nonsing_inv _ hX_inv, Matrix.one_mul]

/-- `HX = X`: the hat matrix fixes `X`. -/
lemma hatMatrix_mul_X (X : Matrix (Fin n) (Fin p) ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    hatMatrix X * X = X := by
  unfold hatMatrix
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX_inv, Matrix.mul_one]

/-- The complement projector is symmetric: `(I − H)ᵀ = I − H`. -/
lemma complementProj_symmetric (X : Matrix (Fin n) (Fin p) ℝ) :
    (complementProj X)ᵀ = complementProj X := by
  unfold complementProj
  rw [Matrix.transpose_sub, Matrix.transpose_one, hatMatrix_symmetric]

/-- The complement projector is idempotent: `(I − H)² = I − H`. -/
lemma complementProj_idempotent (X : Matrix (Fin n) (Fin p) ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    complementProj X * complementProj X = complementProj X := by
  unfold complementProj
  simp [Matrix.sub_mul, Matrix.mul_sub, hatMatrix_idempotent X hX_inv]

/-- Contraction inequality for `I − H`: `‖(I−H)v‖² ≤ ‖v‖²`. -/
lemma complementProj_mulVec_normSq_le (X : Matrix (Fin n) (Fin p) ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) :
    ∀ v, normSq ((complementProj X) *ᵥ v) ≤ normSq v := fun v =>
  proj_mulVec_normSq_le (complementProj X) (complementProj_symmetric X)
    (complementProj_idempotent X hX_inv) v

end MatrixProperties


section LeverageProperties

/-- The `i`th leverage is equal to the squared norm of the `i`th row of `H`: `Hᵢᵢ = ‖Hᵢ‖²`. -/
lemma leverage_eq_hatMatrix_normSq (X : Matrix (Fin n) (Fin p) ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) (i : Fin n) :
    leverage X i = normSq (hatMatrix X i) :=
  proj_diag_eq_row_normSq (hatMatrix X) (hatMatrix_symmetric X)
    (hatMatrix_idempotent X hX_inv) i

/-- The `i`th leverage is equal to `‖Xᵢ‖²_{(XᵀX)⁻¹}`. -/
lemma leverage_eq_normSq' (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) :
    leverage X i = normSq' (Xᵀ * X)⁻¹ (X i) := by
  simp only [leverage, hatMatrix, normSq', toBilin'_apply', Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Leverage values are non-negative.  No invertibility is needed: when `XᵀX` is
singular its `Matrix.inv` is `0`, so every leverage vanishes. -/
theorem leverage_nonneg (X : Matrix (Fin n) (Fin p) ℝ) :
    ∀ i, 0 ≤ leverage X i := by
  intro i
  by_cases hX_inv : IsUnit (Xᵀ * X).det
  · exact proj_diag_nonneg (hatMatrix X) (hatMatrix_symmetric X)
      (hatMatrix_idempotent X hX_inv) i
  · simp [leverage, hatMatrix, Matrix.nonsing_inv_apply_not_isUnit _ hX_inv]

/-- Leverage values are at most `1`. -/
theorem leverage_le_one (X : Matrix (Fin n) (Fin p) ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    ∀ i, leverage X i ≤ 1 := fun i =>
  proj_diag_le_one (hatMatrix X) (hatMatrix_symmetric X)
    (hatMatrix_idempotent X hX_inv) i

/-- The maximal leverage of a design. -/
def maxLev (X : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  ⨆ i : Fin n, leverage X i

/-- Each individual leverage value is bounded by the maximal leverage. -/
lemma leverage_le_maxLev (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) :
    leverage X i ≤ maxLev X :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- The maximal leverage is non-negative. -/
lemma maxLev_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ maxLev X :=
  Real.iSup_nonneg (leverage_nonneg X)

/-- Cauchy–Schwarz/projection bound on the OLS weights `w = X(XᵀX)⁻¹a`:
`wᵢ² ≤ hᵢᵢ · ∑ⱼ wⱼ²`. -/
lemma olsWeights_sq_le_leverage (X : Matrix (Fin n) (Fin p) ℝ)
    (a : Fin p → ℝ) (hX_inv : IsUnit (Xᵀ * X).det) (i : Fin n) :
    olsWeights X a i ^ 2 ≤ leverage X i * normSq (olsWeights X a) := by
  set w : Fin n → ℝ := olsWeights X a with hw_def
  -- `w` lies in the column space, so `Hw = w`.
  have hHw : (hatMatrix X) *ᵥ w = w := by
    have h1 : w = X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ a) := rfl
    rw [h1, Matrix.mulVec_mulVec, hatMatrix_mul_X X hX_inv]
  -- hence `wᵢ = ∑ⱼ Hᵢⱼ wⱼ`, and Cauchy–Schwarz applies.
  have hwi : w i = ∑ j, hatMatrix X i j * w j := by
    have h := congrFun hHw i
    simpa [Matrix.mulVec, dotProduct] using h.symm
  calc w i ^ 2 = (∑ j, hatMatrix X i j * w j) ^ 2 := by rw [hwi]
    _ ≤ normSq (hatMatrix X i) * normSq w := by
        rw [normSq_eq_sum_sq, normSq_eq_sum_sq]
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun j => hatMatrix X i j) w
    _ = leverage X i * normSq w := by rw [← leverage_eq_hatMatrix_normSq X hX_inv i]


end LeverageProperties

end
end LinearModel
end LeanPool
