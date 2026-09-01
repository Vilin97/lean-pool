/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Matrix.Basic
import LeanPool.LinearModel.Ols.QuadForm

/-!
# Weighted Gram matrices

This file develops the weighted Gram matrices `weightedGram X w = Xᵀ·diag(w)·X` for an `n × p`
matrix `X`.  Results for arbitrary weighted Gram matrices are presented first, before a few results
for the specialised sample gram matrix (when `w i = 1 / n` for all `n`) in an additional section at
the end. -/

namespace LeanPool.LinearModel

noncomputable section

open Matrix Finset BigOperators

variable {n p : ℕ}


section WeightedGram

/-! ## The weighted Gram matrix and its weight calculus -/

/-- The weighted Gram matrix `Xᵀ·diag(w)·X`. -/
def weightedGram (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Xᵀ * diagonal w * X

/-- Entrywise form of the weighted Gram matrix: `(weightedGram X w)_{ij} = ∑k wₖ xₖᵢ xₖⱼ`. -/
lemma weightedGram_apply (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (i j : Fin p) :
    weightedGram X w i j = ∑ k, w k * (X k i * X k j) := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  ring

/-- The weighted Gram matrix as a weighted sum of the rank-one terms `xᵢxᵢᵀ`:
`weightedGram X w = ∑ᵢ wᵢ xᵢxᵢᵀ`. -/
lemma weightedGram_eq_sum (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) :
    weightedGram X w = ∑ i, w i • vecMulVec (X i) (X i) := by
  ext k ℓ
  rw [weightedGram_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]

/-- The weighted Gram matrix is symmetric. -/
lemma weightedGram_transpose (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) :
    (weightedGram X w)ᵀ = weightedGram X w := by
  unfold weightedGram
  simp [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Weight-linearity of the weighted Gram matrix under addition. -/
lemma weightedGram_add (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ) :
    weightedGram X (w + w') = weightedGram X w + weightedGram X w' := by
  have hdiag : diagonal (w + w') = diagonal w + diagonal w' := by simp
  unfold weightedGram
  rw [hdiag, Matrix.mul_add, Matrix.add_mul]

/-- Weight-linearity of the weighted Gram matrix under subtraction. -/
lemma weightedGram_sub (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ) :
    weightedGram X (w - w') = weightedGram X w - weightedGram X w' := by
  have hdiag : diagonal (w - w') = diagonal w - diagonal w' := by simp
  unfold weightedGram
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul]

/-- Weight-linearity of the weighted Gram matrix under scaling. -/
lemma weightedGram_smul (X : Matrix (Fin n) (Fin p) ℝ) (c : ℝ) (w : Fin n → ℝ) :
    weightedGram X (c • w) = c • weightedGram X w := by
  have hdiag : diagonal (c • w) = c • diagonal w := by simp
  unfold weightedGram
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]

/-- Unit weights give the Gram matrix: `weightedGram X 1 = XᵀX`. -/
lemma weightedGram_one (X : Matrix (Fin n) (Fin p) ℝ) :
    weightedGram X (fun _ => 1) = Xᵀ * X := by
  unfold weightedGram
  rw [Matrix.diagonal_one, Matrix.mul_one]

/-- `‖v‖²_(weightedGram X w) = Σᵢ wᵢ (xᵢ·v)²`. -/
lemma weightedGram_normSq'_eq (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ)
    (v : Fin p → ℝ) :
    normSq' (weightedGram X w) v = ∑ i, w i * (X i ⬝ᵥ v) ^ 2 := by
  simp only [normSq', toBilin'_apply', weightedGram]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [dotProduct, mulVec]
  ring

/-- If `0 ≤ w` then `weightedGram X w` is psd. -/
lemma weightedGram_psd_of_pos (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ)
    (hw_pos : ∀ i, 0 ≤ w i) : IsPsd (weightedGram X w) := by
  unfold IsPsd
  intro v
  rw [weightedGram_normSq'_eq]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw_pos i) (sq_nonneg _)

/-- If `w ≤ w'` then `weightedGram X (w' - w)` is psd. -/
lemma weightedGram_mono (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ)
    (hw_le : ∀ i, w i ≤ w' i) :
    IsPsd (weightedGram X (w' - w)) := by
  have h : ∀ i, 0 ≤ (w' - w) i := fun i => by simpa using sub_nonneg.mpr (hw_le i)
  exact weightedGram_psd_of_pos X (w' - w) h

/-- If `w ≤ R * w'` then `weightedGram X (R • w' - w)` is psd. -/
lemma weightedGram_mono_smul (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ)
    (R : ℝ) (hw_le : ∀ i, w i ≤ R * w' i) :
    IsPsd (weightedGram X (R • w' - w)) := by
  have h : ∀ i, 0 ≤ (R • w' - w) i := fun i => by simpa using sub_nonneg.mpr (hw_le i)
  exact weightedGram_psd_of_pos X (R • w' - w) h

/-- If `r * w ≤ w'` then then `weightedGram X (w' - c • w)` is psd. -/
lemma weightedGram_smul_mono (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ)
    (r : ℝ) (hw_le : ∀ i, r * w i ≤ w' i) :
    IsPsd (weightedGram X (w' - r • w)) := by
  have h : ∀ i, 0 ≤ (w' - r • w) i := fun i => by simpa using sub_nonneg.mpr (hw_le i)
  exact weightedGram_psd_of_pos X (w' - r • w) h

/-- If `0 ≤ w ≤ R * w'` and `weightedGram X w'` has spectral upper bound `C`, then
`|weightedGram X w i j| ≤ R * C` for all `i, j`. -/
lemma weightedGram_abs_entry_le (X : Matrix (Fin n) (Fin p) ℝ) (w w' : Fin n → ℝ)
    (C R : ℝ) (hW_nn : 0 ≤ R) (hw_nn : ∀ i, 0 ≤ w i) (hw_le : ∀ i, w i ≤ R * w' i)
    (hwGX_ub : isSpectralUb (weightedGram X w') C) :
    ∀ i j, |weightedGram X w i j| ≤ C * R := by
  intro i j
  refine entry_ub_of_spectral_ub _ (weightedGram_transpose X w)
    (weightedGram_psd_of_pos X w hw_nn) (C * R) (fun v => ?_) i j
  have h := weightedGram_mono_smul X w w' R hw_le v
  rw [weightedGram_sub, weightedGram_smul] at h
  simp only [normSq', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  calc normSq' (weightedGram X w) v
      ≤ R * normSq' (weightedGram X w') v := sub_nonneg.mp h
    _ ≤ R * (C * normSq v) := mul_le_mul_of_nonneg_left (hwGX_ub v) hW_nn
    _ = C * R * normSq v := by ring

end WeightedGram


section SampleGram

/-! ## The sample Gram matrix as a weighted Gram instance

Everything `sampleGram`-specific is here; the weighted-Gram theory above is
standalone. `Sₙ = weightedGram X (fun _ => 1/n)`. -/

/-- The sample Gram (second-moment) matrix: `Sₙ := (1/n) XᵀX`, the weighted Gram
matrix at the constant weights `1/n`. -/
def sampleGram (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (1 / (n : ℝ)) • (Xᵀ * X)

/-- The sample Gram matrix is the `1/n`-weight weighted Gram matrix. -/
lemma sampleGram_eq_weightedGram (X : Matrix (Fin n) (Fin p) ℝ) :
    sampleGram X = weightedGram X (fun _ => 1 / (n : ℝ)) := by
  rw [show (fun _ : Fin n => 1 / (n : ℝ)) = (1 / (n : ℝ)) • (fun _ : Fin n => (1 : ℝ))
      from funext fun _ => by simp, weightedGram_smul, weightedGram_one]
  rfl

/-- `Sₙ` is symmetric. -/
lemma sampleGram_transpose (X : Matrix (Fin n) (Fin p) ℝ) :
    (sampleGram X)ᵀ = sampleGram X := by
  rw [sampleGram_eq_weightedGram]
  exact weightedGram_transpose _ _

/-- `(sampleGram X)⁻¹` is symmetric. -/
lemma sampleGram_inv_transpose (X : Matrix (Fin n) (Fin p) ℝ) :
    ((sampleGram X)⁻¹)ᵀ = (sampleGram X)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, sampleGram_transpose]

/-- `‖v‖²_{Sₙ} = (1/n) Σᵢ (xᵢ·v)²`. -/
lemma sampleGram_normSq'_eq (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    normSq' (sampleGram X) v = (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * v j) ^ 2 := by
  rw [sampleGram_eq_weightedGram, weightedGram_normSq'_eq, ← Finset.mul_sum]
  simp [dotProduct]

/-- The sample Gram is psd. -/
lemma sampleGram_is_psd (X : Matrix (Fin n) (Fin p) ℝ) :
    IsPsd (sampleGram X) := by
  rw [sampleGram_eq_weightedGram]
  exact weightedGram_psd_of_pos _ _ (fun i => by positivity)

/-- The sample-Gram quadratic form scales the `XᵀX` form by `1/n`. -/
lemma sampleGram_normSq'_of_gram (X : Matrix (Fin n) (Fin p) ℝ) :
    ∀ v, normSq' (sampleGram X) v = (1 / (n : ℝ)) * normSq' (Xᵀ * X) v := by
  rw [sampleGram]; simp [normSq']

/-- `Sₙ` is invertible when `n > 0` and `XᵀX` is. -/
lemma isUnit_sampleGram (X : Matrix (Fin n) (Fin p) ℝ) (hn : 0 < n)
    (hX_inv : IsUnit (Xᵀ * X).det) : IsUnit (sampleGram X).det := by
  rw [sampleGram, Matrix.det_smul]
  refine isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by positivity)) ?_)
  exact isUnit_iff_ne_zero.mp hX_inv

/-- If `C` is a spectral upper bound for `Sₙ` then `‖Sₙ v‖² ≤ C²·‖v‖²` for all `v`. -/
lemma sampleGram_mulVec_normSq_le (X : Matrix (Fin n) (Fin p) ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hS_ub : isSpectralUb (sampleGram X) C) :
    ∀ v, normSq ((sampleGram X) *ᵥ v) ≤ C ^ 2 * normSq v :=
  mulVec_normSq_le_spectral_ub_sq_normSq (sampleGram X) (sampleGram_transpose X)
    (sampleGram_is_psd X) C hC hS_ub

/-- If `c` and `C` are spectral lower and upper bounds for `Sₙ` then
`c·‖v‖² ≤ C²‖v‖²_{Sₙ⁻¹}` for all `v`. -/
theorem sampleGram_invQuad_lower_bound (X : Matrix (Fin n) (Fin p) ℝ)
    (hn : 0 < n) (hX_inv : IsUnit (Xᵀ * X).det)
    (c C : ℝ) (hc_pos : 0 < c) (hC_pos : 0 < C)
    (hS_lb : isSpectralLb (sampleGram X) c)
    (hS_ub : isSpectralUb (sampleGram X) C) :
    ∀ v, c * normSq v ≤ C ^ 2 * normSq' (sampleGram X)⁻¹ v :=
  spectral_lb_normSq_le_spectral_ub_sq_inv_normSq (sampleGram X)
    (isUnit_sampleGram X hn hX_inv) (sampleGram_transpose X) (sampleGram_is_psd X)
    c C hc_pos hC_pos hS_lb hS_ub


end SampleGram

end
end LinearModel
end LeanPool
