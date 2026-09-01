/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import LeanPool.LinearModel.Ols.QuadForm

/-!
# Optimality of the Ordinary Least Squares estimator

This file establishes the fact that for an `n × p` matrix `X` and `y ∈ ℝⁿ` the OLS estimator
`β̂ = (XᵀX)⁻¹Xᵀy` is the unique vector satisfying `‖y - Xβ̂‖² ≤ ‖y - Xβ‖²` for all `β ∈ ℝⁿ`.

The main results are the following (both assume that `XᵀX` is invertible):
· `olsEstimator_optimal` - for every `β`, `‖y - Xβ̂‖² ≤ ‖y - Xβ‖²`.
· `olsEstimator_unique` - `‖y - Xβ‖² = ``‖y - Xβ̂‖²` iff `β = β̂`
-/

namespace LeanPool.LinearModel

noncomputable section

open Matrix Finset BigOperators

variable {n p : ℕ}


section Definitions

/-- The residual vector `y - Xβ`. -/
def olsResidual (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : Fin n → ℝ := y - X *ᵥ β

/-- The OLS estimator `β̂ = (XᵀX)⁻¹Xᵀy`, defined when `XᵀX` is invertible. -/
def olsEstimator (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) : Fin p → ℝ := (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

end Definitions


section IntermediateResults

/-- If `XᵀX` is invertible, then `XᵀX(XᵀX)⁻¹ = I`, so `XᵀX β̂ = Xᵀy`. -/
lemma normal_equations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X) *ᵥ (olsEstimator X y) = Xᵀ *ᵥ y := by
  unfold olsEstimator
  rw [mulVec_mulVec]
  rw [mul_nonsing_inv _ hX_inv]
  simp

/-- `(y - Xβ̂)` is orthogonal to the column space of `X`, i.e. `Xᵀ(y - Xβ̂) = 0`. -/
lemma olsResidual_orthogonal_to_columns (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    Xᵀ *ᵥ (y - X *ᵥ (olsEstimator X y)) = 0 := by
  simp only [Matrix.mulVec_sub]
  rw [mulVec_mulVec]
  rw [normal_equations X y hX_inv]
  simp [sub_self]

/-- `‖y - Xβ‖² = ‖y - Xβ̂‖² + ‖X(β̂ - β)‖²`. -/
lemma olsResidual_normSq (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    normSq (y - X *ᵥ β) = normSq (y - X *ᵥ (olsEstimator X y))
       + normSq (X *ᵥ (olsEstimator X y - β)) := by
  have h : normSq (y - X *ᵥ β) = normSq (y - X *ᵥ (olsEstimator X y))
      + normSq (X *ᵥ (olsEstimator X y - β))
      + 2 * (y - X *ᵥ (olsEstimator X y)) ⬝ᵥ (X *ᵥ (olsEstimator X y - β)) := by
    rw [show y - X *ᵥ β = (y - X *ᵥ (olsEstimator X y)) +
      (X *ᵥ (olsEstimator X y - β)) by simp [Matrix.mulVec_sub]]
    simp only [normSq, dotProduct_add, dotProduct_comm _ _]; ring
  rw [h]
  have h_cross : (y - X *ᵥ (olsEstimator X y)) ⬝ᵥ (X *ᵥ (olsEstimator X y - β)) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, olsResidual_orthogonal_to_columns X y hX_inv]; simp
  rw [h_cross]
  ring

end IntermediateResults


section MainResults

/-- Optimality of the OLS estimator: if `XᵀX` is invertible then
for every `β`, `‖y - Xβ̂‖² ≤ ‖y - Xβ‖²`. -/
theorem olsEstimator_optimal (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (hX_inv : IsUnit (Xᵀ * X).det) :
    ∀ β : (Fin p → ℝ), normSq (y - X *ᵥ (olsEstimator X y)) ≤ normSq (y - X *ᵥ β) := by
  intro β
  rw [olsResidual_normSq X y β hX_inv]
  linarith [normSq_nonneg (X *ᵥ (olsEstimator X y - β)) ]

/-- Uniqueness of the OLS estimator: if `XᵀX` is invertible then `‖y - Xβ‖² = `
`‖y - Xβ̂‖²` iff `β = β̂`. -/
theorem olsEstimator_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) (hX_inv : IsUnit (Xᵀ * X).det) :
    normSq (y - X *ᵥ β) = normSq (y - X *ᵥ (olsEstimator X y)) ↔
    β = olsEstimator X y := by
  have hX_inj : Function.Injective (X *ᵥ ·) := by
    intro u v huv
    have hXtX : (Xᵀ * X) *ᵥ u = (Xᵀ * X) *ᵥ v := by
      simp only [← Matrix.mulVec_mulVec, huv]
    have : (Xᵀ * X)⁻¹ *ᵥ ((Xᵀ * X) *ᵥ u) = (Xᵀ * X)⁻¹ *ᵥ ((Xᵀ * X) *ᵥ v) := by rw [hXtX]
    simpa only [mulVec_mulVec, nonsing_inv_mul _ hX_inv, one_mulVec] using this
  constructor
  · intro h_eq
    rw [olsResidual_normSq X y β hX_inv] at h_eq
    have h_zero : normSq (X *ᵥ (olsEstimator X y - β)) = 0 := by
      linarith
    have h_mulvec_zero : X *ᵥ (olsEstimator X y - β) = 0 := by
      exact dotProduct_self_eq_zero.mp h_zero
    have h_diff_zero : olsEstimator X y - β = 0 :=
      hX_inj (h_mulvec_zero.trans (mulVec_zero X).symm)
    exact (sub_eq_zero.mp h_diff_zero).symm
  · intro h; rw [h]


end MainResults

end
end LinearModel
end LeanPool
