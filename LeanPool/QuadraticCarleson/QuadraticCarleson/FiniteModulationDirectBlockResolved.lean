/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteBlockHighReduction
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyHighSuffixDilationResolved
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticBlockConjugation
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseCommonErrorWeak

/-!
# Arbitrary finite nonzero modulation blocks

The exact block comparison and the proved high suffix sparse theorem imply a
uniform logarithm-squared weak bound for every finite set of nonzero real
modulations. Conjugation handles negative modulations with the same constant.
The common maximal-function error is paid once for the whole family.
-/

open Function MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace QuadraticCarleson.FiniteModulationDirectBlockResolved

open KrauseLaceyFiniteBlockHighReduction KrauseLaceyHighSuffixDilationResolved
open KrauseLaceySparseDilation KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyHighFullSuffixResolved SparseDilationRegularity
open QuadraticBlockConjugation FiniteSparseCommonErrorWeak
open ExtendedWeakL1Combinators KaltonPaperApplication


noncomputable section

private theorem conjugate_add (f g : L0Infinity) :
    L0Infinity.conjugate (L0Infinity.add f g) =
      L0Infinity.add (L0Infinity.conjugate f) (L0Infinity.conjugate g) := by
  cases f
  cases g
  simp [L0Infinity.conjugate, L0Infinity.add]

private theorem conjugate_smul (c : ℂ) (f : L0Infinity) :
    L0Infinity.conjugate (L0Infinity.smul c f) =
      L0Infinity.smul (conj c) (L0Infinity.conjugate f) := by
  cases f
  simp [L0Infinity.conjugate, L0Infinity.smul]

theorem isSublinear_conjugatedOperator {T : TestOperator} (hT : IsSublinear T) :
    IsSublinear (conjugatedOperator T) := by
  constructor
  · intro f g x
    simpa only [conjugatedOperator, Complex.norm_conj, conjugate_add] using
      hT.1 (L0Infinity.conjugate f) (L0Infinity.conjugate g) x
  · intro c f x
    simpa only [conjugatedOperator, Complex.norm_conj, conjugate_smul] using
      hT.2 (conj c) (L0Infinity.conjugate f) x

@[simp] theorem absoluteValue_conjugatedOperator (T : TestOperator) :
    absoluteValueOperator (conjugatedOperator T) =
      conjugatedOperator (absoluteValueOperator T) := by
  funext f x
  simp [absoluteValueOperator, conjugatedOperator]

theorem continuous_conjugatedOperator {T : TestOperator}
    (hT : ∀ f : L0Infinity, Continuous (T f)) (f : L0Infinity) :
    Continuous (conjugatedOperator T f) :=
  Complex.continuous_conj.comp (hT (L0Infinity.conjugate f))

/-- A single signed modulation uses one dilated high suffix operator. -/
def signedHighSuffixOperator (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) : TestOperator :=
  let T := dilatedOperator (Real.sqrt |lam|) (Real.sqrt_pos.mpr (abs_pos.mpr hlam))
    (finiteFullDyadicSuffixMaxOperator 1 1 (B + 1))
  if lam < 0 then conjugatedOperator T else T

theorem continuous_signedHighSuffixOperator
    (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (f : L0Infinity) :
    Continuous (signedHighSuffixOperator B lam hlam f) := by
  have hcont := continuous_dilatedOperator (Real.sqrt |lam|)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlam))
    (continuous_finiteFullDyadicSuffixMaxOperator 1 1 (B + 1))
  unfold signedHighSuffixOperator
  split
  · exact continuous_conjugatedOperator hcont f
  · exact hcont f

theorem isSublinear_signedHighSuffixOperator
    (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) :
    IsSublinear (signedHighSuffixOperator B lam hlam) := by
  have hsub := isSublinear_dilatedOperator (Real.sqrt |lam|)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlam))
    (isSublinear_finiteFullDyadicSuffixMaxOperator 1 1 (B + 1))
  unfold signedHighSuffixOperator
  split
  · exact isSublinear_conjugatedOperator hsub
  · exact hsub

theorem hasSparseOnePBound_signedHighSuffixOperator
    (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (absoluteValueOperator (signedHighSuffixOperator B lam hlam)) := by
  have hb := hasSparseOnePBound_dilatedHighSuffix B (Real.sqrt |lam|)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlam)) hp hp2
  unfold signedHighSuffixOperator
  split
  · rw [absoluteValue_conjugatedOperator]
    exact hasSparseOnePBound_conjugatedOperator hb
  · exact hb

/-- Signed normalization keeps exactly one family member per modulation. -/
def signedHighSuffixFamily {N : ℕ} (B : ℕ) (lam : Fin N → ℝ)
    (hlam : ∀ i, lam i ≠ 0) : Fin N → TestOperator :=
  fun i ↦ signedHighSuffixOperator B (lam i) (hlam i)

theorem finiteSparseMaximalHypothesis_signedHighSuffixFamily
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0) :
    FiniteSparseMaximalHypothesis (signedHighSuffixFamily B lam hlam)
      highFullSuffixSparseConstant := by
  refine ⟨highFullSuffixSparseConstant_nonneg, ?_, ?_, ?_⟩
  · intro i f
    exact (continuous_signedHighSuffixOperator B (lam i) (hlam i) f).locallyIntegrable
  · intro i
    exact isSublinear_signedHighSuffixOperator B (lam i) (hlam i)
  · intro p hp hp2 i
    have hb := hasSparseOnePBound_signedHighSuffixOperator B (lam i) (hlam i) hp hp2
    have hC : 0 ≤ highFullSuffixSparseConstant * holderConjugate p :=
      mul_nonneg highFullSuffixSparseConstant_nonneg (holderConjugate_spec hp).symm.pos.le
    exact ⟨⟨_, hC, hb⟩, sparseOnePNorm_le_of_bound hC hb⟩

theorem hasWeakOneOneBound_signedHighSuffixFamily
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0) :
    HasWeakOneOneBound
      (finiteSparseMaximalUniversalConstant * highFullSuffixSparseConstant *
        paperLog 1 N ^ 2)
      (finiteMax (signedHighSuffixFamily B lam hlam)) :=
  finiteSparseMaximal_hasWeakOneOneBound (signedHighSuffixFamily B lam hlam)
    highFullSuffixSparseConstant
    (finiteSparseMaximalHypothesis_signedHighSuffixFamily B lam hlam)

/-- The same common error bound applies to either sign of modulation. -/
theorem enorm_paperLowDyadicOperator_le_signedHighSuffix_add_maximal
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator lam hlam B f x‖ₑ ≤
      ‖signedHighSuffixOperator B lam hlam f x‖ₑ +
        48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  by_cases hneg : lam < 0
  · have heq := enorm_paperLowDyadicOperator_neg (-lam) (neg_ne_zero.mpr hlam) B f x
    simp only [neg_neg] at heq
    rw [heq]
    have hp := enorm_paperLowDyadicOperator_le_dilatedHighSuffix_add_maximal
      (-lam) (neg_pos.mpr hneg) B (L0Infinity.conjugate f) x
    simpa only [signedHighSuffixOperator, ite_eq_left hneg, abs_of_neg hneg,
      conjugatedOperator, ← ofReal_norm, L0Infinity.conjugate_apply, Complex.norm_conj] using hp
  · have hpos : 0 < lam := (lt_or_gt_of_ne hlam).resolve_left hneg
    simpa only [signedHighSuffixOperator, ite_eq_right hneg, abs_of_pos hpos] using
      enorm_paperLowDyadicOperator_le_dilatedHighSuffix_add_maximal lam hpos B f x

/-- The actual finite maximum in the paper's finite-modulation corollary. -/
def finitePaperBlockMaxEnorm {N : ℕ} (B : ℕ) (lam : Fin N → ℝ)
    (hlam : ∀ i, lam i ≠ 0) (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  Finset.univ.sup fun i ↦ ‖paperLowDyadicOperator (lam i) (hlam i) B f x‖ₑ

theorem finitePaperBlockMaxEnorm_le_signedHighSuffix_add_maximal
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0)
    (f : L0Infinity) (x : ℝ) :
    finitePaperBlockMaxEnorm B lam hlam f x ≤
      ENNReal.ofReal (finiteMax (signedHighSuffixFamily B lam hlam) f x) +
        48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold finitePaperBlockMaxEnorm
  apply Finset.sup_le
  intro i _hi
  apply (enorm_paperLowDyadicOperator_le_signedHighSuffix_add_maximal
    (lam i) (hlam i) B f x).trans
  apply add_le_add _ le_rfl
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (le_finiteMax (signedHighSuffixFamily B lam hlam) f x i)

/-- The universal coefficient is independent of the height and modulations. -/
def finiteBlockWeakConstant : ℝ :=
  2 * (finiteSparseMaximalUniversalConstant * highFullSuffixSparseConstant) + 384

theorem finiteBlockWeakConstant_nonneg : 0 ≤ finiteBlockWeakConstant := by
  unfold finiteBlockWeakConstant
  positivity [finiteSparseMaximalUniversalConstant_pos, highFullSuffixSparseConstant_nonneg]

/-- Corollary `c:finitemodulationsweak11` in distribution-function form, for
arbitrary signed nonzero real modulations, uniformly over every `B ≥ 0`.
The family need not be injective, and the empty family is included. -/
theorem finiteModulationBlock_weak_bound
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal α * volume
        {x | ENNReal.ofReal α < finitePaperBlockMaxEnorm B lam hlam f x} ≤
      ENNReal.ofReal (finiteBlockWeakConstant * paperLog 1 N ^ 2) *
        ∫⁻ x, ‖f x‖ₑ := by
  let C : ℝ := finiteSparseMaximalUniversalConstant * highFullSuffixSparseConstant *
    paperLog 1 N ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [finiteSparseMaximalUniversalConstant_pos, highFullSuffixSparseConstant_nonneg]
  have hw := hasExtendedWeakL1Bound_of_finiteMax_add_fortyEight_maximal
    (signedHighSuffixFamily B lam hlam) hC
    (hasWeakOneOneBound_signedHighSuffixFamily B lam hlam) f
    (finitePaperBlockMaxEnorm_le_signedHighSuffix_add_maximal B lam hlam f)
  have hL : 1 ≤ paperLog 1 (N : ℝ) :=
    PositiveEndpointOptimization.one_le_paperLog_one (by positivity)
  have hLsq : 1 ≤ paperLog 1 (N : ℝ) ^ 2 := by nlinarith
  have hconst : 2 * C + 384 ≤ finiteBlockWeakConstant * paperLog 1 N ^ 2 := by
    dsimp only [C, finiteBlockWeakConstant]
    nlinarith
  have hout := (ExtendedWeakL1Combinators.HasExtendedWeakL1Bound.mono_constant hw
    (mul_le_mul_of_nonneg_right hconst ENNReal.toReal_nonneg)).2 α hα
  rw [ENNReal.ofReal_mul (mul_nonneg finiteBlockWeakConstant_nonneg (sq_nonneg _)),
    ENNReal.ofReal_toReal f.integrable.hasFiniteIntegral.ne] at hout
  exact hout


end
end QuadraticCarleson.FiniteModulationDirectBlockResolved
