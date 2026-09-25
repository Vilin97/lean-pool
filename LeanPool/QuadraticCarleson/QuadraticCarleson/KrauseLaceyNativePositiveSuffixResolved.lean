/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNativePositiveForestClosure
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPStoppingPositiveClosure
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveSuffixThreeShift
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyAnnularSparseTransfer

/-!
# Native positive suffixes from the one-node Krause--Lacey estimate

This module joins the two already checked halves of the native positive
argument. The concrete finite positive suffix maximum is pointwise bounded
by three localized shifted-forest maxima. The finite-forest stopping
recursion supplies one sparse form for each shift. For each pair of test
functions we choose the largest of those three forms, absorbing their sum
with the exact factor `3`; no union of overlapping shifted grids is used.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyNativePositiveSuffixResolved

open KrauseLaceyAnnularSparseTransfer
open KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyNativePositiveForestClosure
open KrauseLaceyNativePositiveSuffixClosure
open KrauseLaceyPStoppingPositiveClosure
open KrauseLaceyPositiveSuffixThreeShift
open KrauseLaceyStoppingRecursion KrauseLaceyThreeShiftGrid


noncomputable
section

/-- The one-node good-part estimate implies sparse domination of the actual
finite unit-phase positive dyadic suffix maximum. The factor `3` is exactly
the cost of the three shifted grids. -/
theorem hasSparseOnePBound_finitePositiveDyadicSuffixMaxOperator_of_oneNodeGoodPart
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2) (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    HasSparseOnePBound (3 * (A * holderConjugate p)) p
      (finitePositiveDyadicSuffixMaxOperator 1 j N) := by
  classical
  intro f g
  obtain ⟨E, hforest, hpoint⟩ :=
    exists_threeShiftForests_finitePositiveDyadicSuffixMax j N f
  let topScale : ℤ := j + (N : ℤ) - 1
  let branch : Fin 3 → Finset RealInterval := fun shift ↦
    finiteOneShiftMultiscaleFamily topScale (Finset.range N) E shift
  let roots : Fin 3 → Finset (ℕ × ℤ) := fun shift ↦
    finiteOneShiftMultiscaleAddresses (Finset.range N) E shift
  have hbranch (shift : Fin 3) :
      ∃ R : Finset RealInterval,
        IsSparse (1 / 4) (↑R : Set RealInterval) ∧
        (∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ) ≤
          ENNReal.ofReal (A * holderConjugate p) *
            sparseForm p f g (↑R : Set RealInterval) := by
    apply exists_recursive_sparse_bound_forest hlocal hp hp2
      (j + 2) topScale shift N (roots shift) (branch shift) f g
    · omega
    · simpa only [topScale, roots, branch] using hforest shift
  choose R hRsparse hRbound using hbranch
  obtain ⟨shift₀, _, hmax⟩ := Finset.univ.exists_max_image
    (fun shift : Fin 3 ↦ sparseForm p f g (↑(R shift) : Set RealInterval))
    Finset.univ_nonempty
  refine ⟨(↑(R shift₀) : Set RealInterval), hRsparse shift₀, ?_⟩
  let T := finitePositiveDyadicSuffixMaxOperator 1 j N
  by_cases hi : Integrable (fun x ↦ T f x * star (g x))
  · have hnorm : ‖operatorPairing T f g‖ ≤
        ∫ x, ‖T f x * star (g x)‖ := by
      unfold operatorPairing
      exact norm_integral_le_of_norm_le hi.norm
        (Filter.Eventually.of_forall fun x ↦ le_rfl)
    have hof : ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ∫⁻ x, ‖T f x * star (g x)‖ₑ := by
      exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq
        (ofReal_integral_norm_eq_lintegral_enorm hi)
    have hthree : (∫⁻ x, ‖T f x * star (g x)‖ₑ) ≤
        ∑ shift : Fin 3,
          ∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ := by
      calc
        (∫⁻ x, ‖T f x * star (g x)‖ₑ) =
            ∫⁻ x, ‖T f x‖ₑ * ‖g x‖ₑ := by
          congr 1
          funext x
          simp only [enorm_mul]
          rw [show ‖star (g x)‖ₑ = ‖g x‖ₑ by simp [← ofReal_norm]]
        _ ≤ ∫⁻ x, (∑ shift : Fin 3,
              localizedTailMaximal (j + 2)
                (finiteShiftGridScale topScale shift) (branch shift) f x) *
              ‖g x‖ₑ := by
          apply lintegral_mono
          intro x
          exact mul_le_mul' (by simpa only [T, topScale, branch] using hpoint x) le_rfl
        _ = _ := by
          simp_rw [Finset.sum_mul]
          apply lintegral_finsetSum
          intro shift hshift
          exact (measurable_localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift)
            f.measurable_toFun).mul g.measurable_toFun.enorm
    have hsum : (∑ shift : Fin 3,
          ∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ) ≤
        3 * (ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval)) := by
      calc
        _ ≤ ∑ shift : Fin 3, ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R shift₀) : Set RealInterval) := by
          apply Finset.sum_le_sum
          intro shift hshift
          exact (hRbound shift).trans
            (mul_le_mul' le_rfl (hmax shift (Finset.mem_univ shift)))
        _ = _ := by simp [nsmul_eq_mul]
    calc
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤
          ∫⁻ x, ‖T f x * star (g x)‖ₑ := hof
      _ ≤ 3 * (ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval)) := hthree.trans hsum
      _ = ENNReal.ofReal (3 * (A * holderConjugate p)) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
        ring
  · have hzero : operatorPairing T f g = 0 := by
      unfold operatorPairing
      exact integral_undef hi
    rw [hzero, norm_zero, ENNReal.ofReal_zero]
    exact bot_le

/-- Genuine `p`-monitor version of the three-shift suffix closure. The
testing function remains `g`, but every recursive stopping family is selected
using the local `p`-mass monitor. -/
theorem hasSparseOnePBound_finitePositiveDyadicSuffixMaxOperator_of_oneNodePStoppingGoodPart
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2) (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    HasSparseOnePBound (3 * (A * holderConjugate p)) p
      (finitePositiveDyadicSuffixMaxOperator 1 j N) := by
  classical
  intro f g
  obtain ⟨E, hforest, hpoint⟩ :=
    exists_threeShiftForests_finitePositiveDyadicSuffixMax j N f
  let topScale : ℤ := j + (N : ℤ) - 1
  let branch : Fin 3 → Finset RealInterval := fun shift ↦
    finiteOneShiftMultiscaleFamily topScale (Finset.range N) E shift
  let roots : Fin 3 → Finset (ℕ × ℤ) := fun shift ↦
    finiteOneShiftMultiscaleAddresses (Finset.range N) E shift
  have hbranch (shift : Fin 3) :
      ∃ R : Finset RealInterval,
        IsSparse (1 / 4) (↑R : Set RealInterval) ∧
        (∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ) ≤
          ENNReal.ofReal (A * holderConjugate p) *
            sparseForm p f g (↑R : Set RealInterval) := by
    apply exists_pStopping_recursive_sparse_bound_forest hlocal hp hp2.le
      (j + 2) topScale shift N (roots shift) (branch shift) f g
    · omega
    · simpa only [topScale, roots, branch] using hforest shift
  choose R hRsparse hRbound using hbranch
  obtain ⟨shift₀, _, hmax⟩ := Finset.univ.exists_max_image
    (fun shift : Fin 3 ↦ sparseForm p f g (↑(R shift) : Set RealInterval))
    Finset.univ_nonempty
  refine ⟨(↑(R shift₀) : Set RealInterval), hRsparse shift₀, ?_⟩
  let T := finitePositiveDyadicSuffixMaxOperator 1 j N
  by_cases hi : Integrable (fun x ↦ T f x * star (g x))
  · have hnorm : ‖operatorPairing T f g‖ ≤
        ∫ x, ‖T f x * star (g x)‖ := by
      unfold operatorPairing
      exact norm_integral_le_of_norm_le hi.norm
        (Filter.Eventually.of_forall fun x ↦ le_rfl)
    have hof : ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ∫⁻ x, ‖T f x * star (g x)‖ₑ := by
      exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq
        (ofReal_integral_norm_eq_lintegral_enorm hi)
    have hthree : (∫⁻ x, ‖T f x * star (g x)‖ₑ) ≤
        ∑ shift : Fin 3,
          ∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ := by
      calc
        (∫⁻ x, ‖T f x * star (g x)‖ₑ) =
            ∫⁻ x, ‖T f x‖ₑ * ‖g x‖ₑ := by
          congr 1
          funext x
          simp only [enorm_mul]
          rw [show ‖star (g x)‖ₑ = ‖g x‖ₑ by simp [← ofReal_norm]]
        _ ≤ ∫⁻ x, (∑ shift : Fin 3,
              localizedTailMaximal (j + 2)
                (finiteShiftGridScale topScale shift) (branch shift) f x) *
              ‖g x‖ₑ := by
          apply lintegral_mono
          intro x
          exact mul_le_mul' (by simpa only [T, topScale, branch] using hpoint x) le_rfl
        _ = _ := by
          simp_rw [Finset.sum_mul]
          apply lintegral_finsetSum
          intro shift hshift
          exact (measurable_localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift)
            f.measurable_toFun).mul g.measurable_toFun.enorm
    have hsum : (∑ shift : Fin 3,
          ∫⁻ x, localizedTailMaximal (j + 2)
            (finiteShiftGridScale topScale shift) (branch shift) f x * ‖g x‖ₑ) ≤
        3 * (ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval)) := by
      calc
        _ ≤ ∑ shift : Fin 3, ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R shift₀) : Set RealInterval) := by
          apply Finset.sum_le_sum
          intro shift hshift
          exact (hRbound shift).trans
            (mul_le_mul' le_rfl (hmax shift (Finset.mem_univ shift)))
        _ = _ := by simp [nsmul_eq_mul]
    calc
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤
          ∫⁻ x, ‖T f x * star (g x)‖ₑ := hof
      _ ≤ 3 * (ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval)) := hthree.trans hsum
      _ = ENNReal.ofReal (3 * (A * holderConjugate p)) *
          sparseForm p f g (↑(R shift₀) : Set RealInterval) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
        ring
  · have hzero : operatorPairing T f g = 0 := by
      unfold operatorPairing
      exact integral_undef hi
    rw [hzero, norm_zero, ENNReal.ofReal_zero]
    exact bot_le

/-- Sparse control of the unit positive suffixes in precisely the high range
where the quadratic one-node estimate applies. Low scales must be kept in
the full odd kernel and handled separately. -/
def HasNativeUnitHighPositiveSuffixSparseBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (p : ℝ), 1 < p → p < 2 → ∀ (j : ℤ), 1 ≤ j → ∀ (N : ℕ),
    HasSparseOnePBound (C * holderConjugate p) p
      (finitePositiveDyadicSuffixMaxOperator 1 j N)

/-- The direct high-scale one-node estimate closes every finite high positive
suffix, with the factor `3` from the shifted grids. -/
theorem hasNativeUnitHighPositiveSuffixSparseBound_of_oneNodeGoodPart
    {A : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A) :
    HasNativeUnitHighPositiveSuffixSparseBound (3 * A) := by
  refine ⟨mul_nonneg (by norm_num) hlocal.1, ?_⟩
  intro p hp hp2 j hj N
  have h :=
    hasSparseOnePBound_finitePositiveDyadicSuffixMaxOperator_of_oneNodeGoodPart
      hlocal hp hp2 j hj N
  convert h using 1; ring

/-- The genuine `p`-monitor one-node estimate closes all high positive
suffixes, with only the three-shift factor. -/
theorem hasNativeUnitHighPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart
    {A : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A) :
    HasNativeUnitHighPositiveSuffixSparseBound (3 * A) := by
  refine ⟨mul_nonneg (by norm_num) hlocal.1, ?_⟩
  intro p hp hp2 j hj N
  have h :=
    hasSparseOnePBound_finitePositiveDyadicSuffixMaxOperator_of_oneNodePStoppingGoodPart
      hlocal hp hp2 j hj N
  convert h using 1; ring

/-- The part of the downstream all-scale suffix interface not supplied by
the source's high-scale one-node argument. -/
def HasNativeUnitLowPositiveSuffixSparseBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (p : ℝ), 1 < p → p < 2 → ∀ (j : ℤ), j < 1 → ∀ (N : ℕ),
    HasSparseOnePBound (C * holderConjugate p) p
      (finitePositiveDyadicSuffixMaxOperator 1 j N)

/-- High- and low-starting suffix estimates combine into the existing
all-integer native suffix interface without changing its statement. -/
theorem hasNativeUnitPositiveSuffixSparseBound_of_high_and_low
    {C D : ℝ} (hhigh : HasNativeUnitHighPositiveSuffixSparseBound C)
    (hlow : HasNativeUnitLowPositiveSuffixSparseBound D) :
    HasNativeUnitPositiveSuffixSparseBound (C + D) := by
  refine ⟨add_nonneg hhigh.1 hlow.1, ?_⟩
  intro p hp hp2 j N
  have hp' : 0 < holderConjugate p := (holderConjugate_spec hp).symm.pos
  by_cases hj : 1 ≤ j
  · exact (hhigh.2 p hp hp2 j hj N).mono
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hlow.1) hp'.le)
  · exact (hlow.2 p hp hp2 j (by omega) N).mono
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hhigh.1) hp'.le)

/-- Complete all-scale suffix adapter from the genuine p-stopping one-node
estimate and the explicitly isolated low-starting suffix estimate. -/
theorem hasNativeUnitPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart_and_low
    {A D : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hlow : HasNativeUnitLowPositiveSuffixSparseBound D) :
    HasNativeUnitPositiveSuffixSparseBound (3 * A + D) :=
  hasNativeUnitPositiveSuffixSparseBound_of_high_and_low
    (hasNativeUnitHighPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart hlocal) hlow


end
end KrauseLaceyNativePositiveSuffixResolved
end QuadraticCarleson
