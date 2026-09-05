/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Ols.TTest

/-!
# HC2 recovers the Welch t-test in the two-sample problem

The two-sample problem as a regression: with the cell-means design
`X : Matrix (Fin (m + k)) (Fin 2) ℝ` whose first `m` rows are `(1, 0)` and last
`k` rows are `(0, 1)`, OLS estimates the two group means, and the contrast
`a = (1, −1)` estimates their difference.  This file shows that the
HC2-studentised contrast is precisely the Welch two-sample t-statistic.

The main result of the file is:

· `hc2_studentized_twoSample_eq_welch` — the HC2-studentised contrast is
the Welch two-sample t-statistic: `aᵀβ̂ / √(D̂/n) = (ybar₁ − ybar₂) / √(s₁²/m + s₂²/k)`.
-/

open Matrix Finset BigOperators

namespace LeanPool.LinearModel

noncomputable section

section Definitions

variable {m k : ℕ}

/-- The two-sample (cell-means) design: the first `m` rows are `(1, 0)`, the
last `k` rows are `(0, 1)`. -/
def twoSampleDesign (m k : ℕ) : Matrix (Fin (m + k)) (Fin 2) ℝ :=
  Matrix.of fun i =>
    Fin.addCases (motive := fun _ => Fin 2 → ℝ) (fun _ => ![1, 0]) (fun _ => ![0, 1]) i

/-- The first-group subvector of a data vector. -/
def fstSample (v : Fin (m + k) → ℝ) : Fin m → ℝ := fun i => v (Fin.castAdd k i)

/-- The second-group subvector of a data vector. -/
def sndSample (v : Fin (m + k) → ℝ) : Fin k → ℝ := fun j => v (Fin.natAdd m j)

/-- The sample mean. -/
def sampleMean {n : ℕ} (w : Fin n → ℝ) : ℝ := (∑ i, w i) / (n : ℝ)

/-- The Bessel-corrected (unbiased) sample variance. -/
def sampleVar {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ i, (w i - sampleMean w) ^ 2) / ((n : ℝ) - 1)

/-- Welch's squared standard error `s₁²/m + s₂²/k`. -/
def welchSE2 (v : Fin (m + k) → ℝ) : ℝ :=
  sampleVar (fstSample v) / (m : ℝ) + sampleVar (sndSample v) / (k : ℝ)

/-- The Welch two-sample t-statistic `(ybar₁ − ybar₂) / √(s₁²/m + s₂²/k)`. -/
def welchStatistic (v : Fin (m + k) → ℝ) : ℝ :=
  (sampleMean (fstSample v) - sampleMean (sndSample v)) / Real.sqrt (welchSE2 v)

@[simp] lemma twoSampleDesign_castAdd (i : Fin m) :
    twoSampleDesign m k (Fin.castAdd k i) = ![1, 0] := by
  change Fin.addCases (motive := fun _ => Fin 2 → ℝ)
    (fun _ => ![1, 0]) (fun _ => ![0, 1]) (Fin.castAdd k i) = ![1, 0]
  exact Fin.addCases_left i

@[simp] lemma twoSampleDesign_natAdd (j : Fin k) :
    twoSampleDesign m k (Fin.natAdd m j) = ![0, 1] := by
  change Fin.addCases (motive := fun _ => Fin 2 → ℝ)
    (fun _ => ![1, 0]) (fun _ => ![0, 1]) (Fin.natAdd m j) = ![0, 1]
  exact Fin.addCases_right j

/-- Sums of squared centred values are `(n − 1)` times the sample variance. -/
lemma sum_sq_dev_eq {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) :
    ∑ i, (w i - sampleMean w) ^ 2 = ((n : ℝ) - 1) * sampleVar w := by
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [sampleVar, mul_div_cancel₀ _ hn1]

end Definitions


section DesignAlgebra

variable {m k : ℕ}

/-- The Gram matrix of the two-sample design is `diag(m, k)`. -/
lemma twoSampleDesign_gram (m k : ℕ) :
    (twoSampleDesign m k)ᵀ * twoSampleDesign m k = diagonal ![(m : ℝ), (k : ℝ)] := by
  ext g h
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fin.sum_univ_add]
  simp only [twoSampleDesign_castAdd, twoSampleDesign_natAdd]
  fin_cases g <;> fin_cases h <;>
    simp [Matrix.diagonal]

/-- The Gram matrix is invertible when both groups are non-empty. -/
lemma twoSampleDesign_isUnit_det (hm : m ≠ 0) (hk : k ≠ 0) :
    IsUnit ((twoSampleDesign m k)ᵀ * twoSampleDesign m k).det := by
  rw [twoSampleDesign_gram, Matrix.det_diagonal, isUnit_iff_ne_zero]
  simp [Fin.prod_univ_two, hm, hk]

/-- The inverse Gram matrix is `diag(1/m, 1/k)`. -/
lemma twoSampleDesign_gram_inv (hm : m ≠ 0) (hk : k ≠ 0) :
    ((twoSampleDesign m k)ᵀ * twoSampleDesign m k)⁻¹
      = diagonal ![((m : ℝ))⁻¹, ((k : ℝ))⁻¹] := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [twoSampleDesign_gram]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext g
  fin_cases g <;>
    simp [mul_inv_cancel₀ hm', mul_inv_cancel₀ hk']

/-- `Xᵀv` collects the two group sums. -/
lemma twoSampleDesign_transpose_mulVec (v : Fin (m + k) → ℝ) :
    (twoSampleDesign m k)ᵀ *ᵥ v = ![∑ i, fstSample v i, ∑ j, sndSample v j] := by
  funext g
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Fin.sum_univ_add]
  simp only [twoSampleDesign_castAdd, twoSampleDesign_natAdd]
  fin_cases g <;> simp [fstSample, sndSample]

/-- The OLS estimator is the pair of group means. -/
lemma olsEstimator_twoSample (hm : m ≠ 0) (hk : k ≠ 0) (v : Fin (m + k) → ℝ) :
    olsEstimator (twoSampleDesign m k) v
      = ![sampleMean (fstSample v), sampleMean (sndSample v)] := by
  unfold olsEstimator
  rw [twoSampleDesign_gram_inv hm hk, twoSampleDesign_transpose_mulVec]
  funext g
  rw [Matrix.mulVec_diagonal]
  fin_cases g <;> simp [sampleMean, inv_mul_eq_div]

/-- Fitted values in the first group are the first coordinate of `β`. -/
lemma twoSampleDesign_mulVec_castAdd (β : Fin 2 → ℝ) (i : Fin m) :
    (twoSampleDesign m k *ᵥ β) (Fin.castAdd k i) = β 0 := by
  simp only [Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_two]

/-- Fitted values in the second group are the second coordinate of `β`. -/
lemma twoSampleDesign_mulVec_natAdd (β : Fin 2 → ℝ) (j : Fin k) :
    (twoSampleDesign m k *ᵥ β) (Fin.natAdd m j) = β 1 := by
  simp only [Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_two]

/-- OLS residuals in the first group are the centred first-group values. -/
lemma sampleResidual_twoSample_castAdd (hm : m ≠ 0) (hk : k ≠ 0)
    (v : Fin (m + k) → ℝ) (i : Fin m) :
    sampleResidual (twoSampleDesign m k) v (Fin.castAdd k i)
      = fstSample v i - sampleMean (fstSample v) := by
  unfold sampleResidual olsResidual
  rw [olsEstimator_twoSample hm hk]
  simp [twoSampleDesign_mulVec_castAdd, fstSample]

/-- OLS residuals in the second group are the centred second-group values. -/
lemma sampleResidual_twoSample_natAdd (hm : m ≠ 0) (hk : k ≠ 0)
    (v : Fin (m + k) → ℝ) (j : Fin k) :
    sampleResidual (twoSampleDesign m k) v (Fin.natAdd m j)
      = sndSample v j - sampleMean (sndSample v) := by
  unfold sampleResidual olsResidual
  rw [olsEstimator_twoSample hm hk]
  simp [twoSampleDesign_mulVec_natAdd, sndSample]

/-- Every first-group observation has leverage `1/m`. -/
lemma leverage_twoSample_castAdd (hm : m ≠ 0) (hk : k ≠ 0) (i : Fin m) :
    leverage (twoSampleDesign m k) (Fin.castAdd k i) = (m : ℝ)⁻¹ := by
  rw [leverage_eq_normSq', twoSampleDesign_gram_inv hm hk]
  simp [normSq', toBilin'_apply', Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_two]

/-- Every second-group observation has leverage `1/k`. -/
lemma leverage_twoSample_natAdd (hm : m ≠ 0) (hk : k ≠ 0) (j : Fin k) :
    leverage (twoSampleDesign m k) (Fin.natAdd m j) = (k : ℝ)⁻¹ := by
  rw [leverage_eq_normSq', twoSampleDesign_gram_inv hm hk]
  simp [normSq', toBilin'_apply', Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_two]

end DesignAlgebra


section Hc2Welch

variable {m k : ℕ}

/-- The HC2 residual-weighted Gram matrix of the two-sample regression:
`diag(m·s₁², k·s₂²)/(m + k)` in the unbiased sample variances. -/
lemma hc2Gram_twoSample (hm : 2 ≤ m) (hk : 2 ≤ k) (v : Fin (m + k) → ℝ) :
    hcGram (twoSampleDesign m k) (hc2Correction (twoSampleDesign m k)) v
      = diagonal ![(m : ℝ) * sampleVar (fstSample v) / ((m : ℝ) + k),
          (k : ℝ) * sampleVar (sndSample v) / ((m : ℝ) + k)] := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have hm' : (m : ℝ) ≠ 0 := by linarith
  have hk' : (k : ℝ) ≠ 0 := by linarith
  have hmk : ((m + k : ℕ) : ℝ) = (m : ℝ) + k := by push_cast; ring
  have hmk0 : (m : ℝ) + k ≠ 0 := by positivity
  have hinvm : 1 - (m : ℝ)⁻¹ = ((m : ℝ) - 1) / m := by field_simp
  have hinvk : 1 - (k : ℝ)⁻¹ = ((k : ℝ) - 1) / k := by field_simp
  ext g h
  simp only [hcGram]
  rw [weightedGram_apply, Fin.sum_univ_add]
  simp only [hc2Correction, leverage_twoSample_castAdd hm0 hk0,
    leverage_twoSample_natAdd hm0 hk0, sampleResidual_twoSample_castAdd hm0 hk0 v,
    sampleResidual_twoSample_natAdd hm0 hk0 v, twoSampleDesign_castAdd,
    twoSampleDesign_natAdd, hmk]
  fin_cases g <;> fin_cases h
  · -- entry (0,0): the first-group sum survives
    simp only [Fin.zero_eta, Matrix.cons_val_zero, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.diagonal_apply_eq]
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_sq_dev_eq hm, hinvm, inv_div]
    field_simp
  · -- entry (0,1): every term vanishes
    simp [Matrix.diagonal_apply_ne]
  · -- entry (1,0): every term vanishes
    simp [Matrix.diagonal_apply_ne]
  · -- entry (1,1): the second-group sum survives
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      mul_one, mul_zero, Finset.sum_const_zero, zero_add,
      Matrix.diagonal_apply_eq]
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_sq_dev_eq hk, hinvk, inv_div]
    field_simp

/-- The inverse sample Gram matrix is `diag((m+k)/m, (m+k)/k)`. -/
lemma sampleGram_twoSample_inv (hm : m ≠ 0) (hk : k ≠ 0) :
    (sampleGram (twoSampleDesign m k))⁻¹
      = diagonal ![((m : ℝ) + k) / m, ((m : ℝ) + k) / k] := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hmk : ((m + k : ℕ) : ℝ) = (m : ℝ) + k := by push_cast; ring
  have hmk0 : (m : ℝ) + k ≠ 0 := by positivity
  have hS : sampleGram (twoSampleDesign m k)
      = diagonal ![(m : ℝ) / ((m : ℝ) + k), (k : ℝ) / ((m : ℝ) + k)] := by
    rw [sampleGram, twoSampleDesign_gram]
    ext g h
    fin_cases g <;> fin_cases h <;>
      simp [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, hmk,
        div_eq_inv_mul]
  rw [hS]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext g
  fin_cases g <;>
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one]
      field_simp

/-- The HC2 sandwich at the contrast `(1, −1)` is Welch's squared standard
error, scaled by `n = m + k`: `aᵀ Sₙ⁻¹ M̂ Sₙ⁻¹ a = (m + k)(s₁²/m + s₂²/k)`. -/
theorem hc2_scalarSandwich_twoSample (hm : 2 ≤ m) (hk : 2 ≤ k)
    (v : Fin (m + k) → ℝ) :
    scalarSandwich (sampleGram (twoSampleDesign m k))
        (hcGram (twoSampleDesign m k) (hc2Correction (twoSampleDesign m k)) v)
        ![1, -1]
      = ((m : ℝ) + k) * welchSE2 v := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hmk0 : (m : ℝ) + k ≠ 0 := by positivity
  simp only [scalarSandwich]
  rw [sampleGram_twoSample_inv hm0 hk0, hc2Gram_twoSample hm hk,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [normSq', toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, welchSE2]
  field_simp

/-- The contrast `(1, −1)` selects the difference of group means. -/
lemma dotProduct_olsEstimator_twoSample (hm : m ≠ 0) (hk : k ≠ 0)
    (v : Fin (m + k) → ℝ) :
    ![1, -1] ⬝ᵥ olsEstimator (twoSampleDesign m k) v
      = sampleMean (fstSample v) - sampleMean (sndSample v) := by
  rw [olsEstimator_twoSample hm hk]
  simp [dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- HC2 gives the Welch t-test: in the two-sample regression, the
HC2-studentised contrast — the plug-in t-statistic `aᵀβ̂ / sHat` with
`sHat² = aᵀ Sₙ⁻¹ M̂ Sₙ⁻¹ a / n` and `a = (1, −1)` — is exactly the Welch
two-sample statistic `(ybar₁ − ybar₂)/√(s₁²/m + s₂²/k)`. -/
theorem hc2_studentized_twoSample_eq_welch (hm : 2 ≤ m) (hk : 2 ≤ k)
    (v : Fin (m + k) → ℝ) :
    (![1, -1] ⬝ᵥ olsEstimator (twoSampleDesign m k) v)
      / Real.sqrt (scalarSandwich (sampleGram (twoSampleDesign m k))
          (hcGram (twoSampleDesign m k) (hc2Correction (twoSampleDesign m k))
            v) ![1, -1] / ((m : ℝ) + k))
      = welchStatistic v := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hmk0 : (m : ℝ) + k ≠ 0 := by positivity
  rw [dotProduct_olsEstimator_twoSample hm0 hk0,
    hc2_scalarSandwich_twoSample hm hk, mul_div_cancel_left₀ _ hmk0]
  rfl

end Hc2Welch


end

end LinearModel
end LeanPool
