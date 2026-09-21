/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectPStopping
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNativePositiveSuffixResolved
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyLowFullOddReduction

/-!
# Unconditional sparse bound for the high full-odd quadratic suffixes

The direct quadratic one-node theorem gives the positive-half suffix bound
with a factor three for the shifted grids. Reflection restores the full odd
kernel with a further factor two. All constants are independent of the lower
and upper high-scale cutoffs.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson.KrauseLaceyHighFullSuffixResolved

open KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyNativePositiveSuffixResolved
open KrauseLaceyQuadraticDirectPStopping
open KrauseLaceyCompactPairingStabilization KrauseLaceySharpSmoothAdapter
open KrauseLaceyFullDyadicReflection KrauseLaceyLowFullOddReduction


noncomputable section

/-- Six times the checked one-node constant: three shifted grids and the two
spatial halves of the full odd kernel. -/
def highFullSuffixSparseConstant : ℝ := 6 * directQuadraticOneNodeConstant

theorem highFullSuffixSparseConstant_nonneg :
    0 ≤ highFullSuffixSparseConstant :=
  mul_nonneg (by norm_num) directQuadraticOneNodeConstant_nonneg

/-- The high positive suffix estimate has no remaining analytic premise. -/
theorem hasNativeUnitHighPositiveSuffixSparseBound_directQuadratic :
    HasNativeUnitHighPositiveSuffixSparseBound
      (3 * directQuadraticOneNodeConstant) :=
  hasNativeUnitHighPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart
    hasOneNodePStoppingGoodPartPairingBound_directQuadratic

/-- Unconditional sparse domination of every finite unit-phase full-odd
suffix maximum whose initial dyadic scale is at least one. -/
theorem hasSparseOnePBound_highFullDyadicSuffixMax
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (finiteFullDyadicSuffixMaxOperator 1 j N) := by
  have hpositive :=
    hasNativeUnitHighPositiveSuffixSparseBound_directQuadratic.2 p hp hp2 j hj N
  have hC : 0 ≤ 3 * directQuadraticOneNodeConstant * holderConjugate p :=
    mul_nonneg (mul_nonneg (by norm_num) directQuadraticOneNodeConstant_nonneg)
      (holderConjugate_spec hp).symm.pos.le
  have hfull := hasSparseOnePBound_fullDyadicSuffixMax 1 j N hC hpositive
  convert hfull using 1 <;> unfold highFullSuffixSparseConstant <;> ring

/-- The sparse norm has the same uniform high-scale bound. -/
theorem sparseOnePNorm_highFullDyadicSuffixMax_le
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    sparseOnePNorm p (finiteFullDyadicSuffixMaxOperator 1 j N) ≤
      highFullSuffixSparseConstant * holderConjugate p :=
  sparseOnePNorm_le_of_bound
    (mul_nonneg highFullSuffixSparseConstant_nonneg (holderConjugate_spec hp).symm.pos.le)
    (hasSparseOnePBound_highFullDyadicSuffixMax hp hp2 j hj N)

@[simp] theorem absoluteValue_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) :
    absoluteValueOperator (finiteFullDyadicSuffixMaxOperator lam j N) =
      finiteFullDyadicSuffixMaxOperator lam j N := by
  funext f x
  simp [absoluteValueOperator, finiteFullDyadicSuffixMaxOperator]

/-- Compact-support stabilization passes the uniform high-suffix estimate
to every moving lower cutoff, with no further constant loss. -/
theorem hasSparseOnePBound_highDyadicSmoothHighPassMax
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (j : ℤ) (hj : 1 ≤ j) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (dyadicSmoothHighPassMaxOperator 1 j) :=
  hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_finiteSuffixMax 1 j
    (fun N ↦ hasSparseOnePBound_highFullDyadicSuffixMax hp hp2 j hj N)

/-- The countable high-pass maximum retains subadditivity in extended norm. -/
theorem dyadicSmoothHighPassMaxEnorm_add_le
    (lam : ℝ) (j : ℤ) (f g : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j (L0Infinity.add f g) x ≤
      dyadicSmoothHighPassMaxEnorm lam j f x +
        dyadicSmoothHighPassMaxEnorm lam j g x := by
  unfold dyadicSmoothHighPassMaxEnorm
  apply iSup_le
  intro m
  rw [smoothQuadraticHighPass_add lam (zpow_pos (by norm_num) _)]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup (fun n : ℕ ↦
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (n : ℤ) - 3)) f x‖ₑ) m)
    (le_iSup (fun n : ℕ ↦
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (n : ℤ) - 3)) g x‖ₑ) m))

/-- Scalar homogeneity passes exactly through the countable supremum. -/
theorem dyadicSmoothHighPassMaxEnorm_smul
    (lam : ℝ) (j : ℤ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j (L0Infinity.smul c f) x =
      ‖c‖ₑ * dyadicSmoothHighPassMaxEnorm lam j f x := by
  unfold dyadicSmoothHighPassMaxEnorm
  have hterm (m : ℕ) :
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3))
        (L0Infinity.smul c f) x‖ₑ =
      ‖c‖ₑ * ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3)) f x‖ₑ := by
    rw [smoothQuadraticHighPass_smul lam (zpow_pos (by norm_num) _) c f x, enorm_mul]
  simp_rw [hterm]
  exact (ENNReal.mul_iSup _ _).symm

/-- The genuine dyadic smooth high-pass maximum satisfies the sublinearity
interface of the finite-family sparse maximal theorem. -/
theorem isSublinear_dyadicSmoothHighPassMaxOperator (lam : ℝ) (j : ℤ) :
    IsSublinear (dyadicSmoothHighPassMaxOperator lam j) := by
  constructor
  · intro f g x
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    simp only [ofReal_norm, enorm_dyadicSmoothHighPassMaxOperator]
    exact dyadicSmoothHighPassMaxEnorm_add_le lam j f g x
  · intro c f x
    apply (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [ofReal_norm, enorm_dyadicSmoothHighPassMaxOperator]
    exact dyadicSmoothHighPassMaxEnorm_smul lam j c f x

/-- Full dyadic convolution is additive on the paper's test space. -/
theorem fullDyadicConvolution_add
    (lam : ℝ) (j : ℤ) (f g : L0Infinity) (x : ℝ) :
    fullDyadicConvolution lam j (L0Infinity.add f g) x =
      fullDyadicConvolution lam j f x + fullDyadicConvolution lam j g x := by
  have hi (h : L0Infinity) : Integrable (fun y ↦
      annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam (x - y) * h y) :=
    integrable_convolution_row_of_memLp
      (continuous_fullDyadicQuadraticKernel lam j)
      (hasCompactSupport_fullDyadicQuadraticKernel lam j) (memLp_two_L0Infinity h) x
  unfold fullDyadicConvolution
  rw [← integral_add (hi f) (hi g)]
  apply integral_congr_ae
  filter_upwards with y
  change _ * (f y + g y) = _
  ring

/-- Scalar multiplication commutes with a full dyadic convolution. -/
theorem fullDyadicConvolution_smul
    (lam : ℝ) (j : ℤ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    fullDyadicConvolution lam j (L0Infinity.smul c f) x =
      c * fullDyadicConvolution lam j f x := by
  unfold fullDyadicConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change _ * (c * f y) = _
  ring

theorem finiteFullDyadicSuffix_add
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f g : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m (L0Infinity.add f g) x =
      finiteFullDyadicSuffix lam j N m f x + finiteFullDyadicSuffix lam j N m g x := by
  simp only [finiteFullDyadicSuffix, finiteFullDyadicTail,
    fullDyadicConvolution_add, Finset.sum_add_distrib]

theorem finiteFullDyadicSuffix_smul
    (lam : ℝ) (j : ℤ) (N m : ℕ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m (L0Infinity.smul c f) x =
      c * finiteFullDyadicSuffix lam j N m f x := by
  simp only [finiteFullDyadicSuffix, finiteFullDyadicTail,
    fullDyadicConvolution_smul, Finset.mul_sum]

/-- Taking the finite maximum preserves subadditivity of full suffixes. -/
theorem finiteFullDyadicSuffixMaxNNNorm_add_le
    (lam : ℝ) (j : ℤ) (N : ℕ) (f g : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N (L0Infinity.add f g) x ≤
      finiteFullDyadicSuffixMaxNNNorm lam j N f x +
        finiteFullDyadicSuffixMaxNNNorm lam j N g x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  apply Finset.sup_le
  intro m hm
  rw [finiteFullDyadicSuffix_add]
  exact (nnnorm_add_le _ _).trans (add_le_add
    (Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicSuffix lam j N r f x‖₊) hm)
    (Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicSuffix lam j N r g x‖₊) hm))

/-- The finite full-suffix maximum is exactly homogeneous. -/
theorem finiteFullDyadicSuffixMaxNNNorm_smul
    (lam : ℝ) (j : ℤ) (N : ℕ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N (L0Infinity.smul c f) x =
      ‖c‖₊ * finiteFullDyadicSuffixMaxNNNorm lam j N f x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  simp_rw [finiteFullDyadicSuffix_smul, nnnorm_mul]
  exact (NNReal.mul_finset_sup ‖c‖₊ _ _).symm

theorem norm_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finiteFullDyadicSuffixMaxOperator lam j N f x‖ =
      (finiteFullDyadicSuffixMaxNNNorm lam j N f x : ℝ) := by
  simp [finiteFullDyadicSuffixMaxOperator]

/-- Sublinearity of the finite full-odd maximum needed for finite sparse
families; no restriction on scales or modulation is required. -/
theorem isSublinear_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) :
    IsSublinear (finiteFullDyadicSuffixMaxOperator lam j N) := by
  constructor
  · intro f g x
    simp only [norm_finiteFullDyadicSuffixMaxOperator]
    exact_mod_cast finiteFullDyadicSuffixMaxNNNorm_add_le lam j N f g x
  · intro c f x
    simp only [norm_finiteFullDyadicSuffixMaxOperator]
    rw [finiteFullDyadicSuffixMaxNNNorm_smul]
    rfl


end
end QuadraticCarleson.KrauseLaceyHighFullSuffixResolved
