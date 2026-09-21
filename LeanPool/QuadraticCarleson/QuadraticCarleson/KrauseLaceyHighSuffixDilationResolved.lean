/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyHighFullSuffixResolved
import LeanPool.QuadraticCarleson.QuadraticCarleson.SparseDilationRegularity
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximalProof

/-!
# Uniform weak bounds for finite families of dilated high suffixes

Positive spatial dilation preserves the sparse constant of the finite full
quadratic suffix maximum. Combining that exact transfer with continuity and
sublinearity verifies every premise of the finite sparse maximal theorem.
-/

open Function MeasureTheory

namespace QuadraticCarleson.KrauseLaceyHighSuffixDilationResolved

open KrauseLaceyFullDyadicSparseTransfer KrauseLaceyHighFullSuffixResolved
open KrauseLaceySparseDilation SparseDilationRegularity


noncomputable section

/-- The normalized high full-odd suffix maximum transported to each positive
dilation in a finite family. The upper scale count remains explicit. -/
def dilatedHighSuffixFamily {N : ℕ} (B : ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) : Fin N → TestOperator :=
  fun i ↦ dilatedOperator (a i) (ha i)
    (finiteFullDyadicSuffixMaxOperator 1 1 (B + 1))

/-- Neither the positive dilation nor the number of scales changes the
verified high-scale sparse constant. -/
theorem hasSparseOnePBound_dilatedHighSuffix
    (B : ℕ) (a : ℝ) (ha : 0 < a) {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (absoluteValueOperator (dilatedOperator a ha
        (finiteFullDyadicSuffixMaxOperator 1 1 (B + 1)))) := by
  rw [absoluteValue_dilatedOperator, absoluteValue_finiteFullDyadicSuffixMaxOperator]
  exact hasSparseOnePBound_dilatedOperator a ha
    (hasSparseOnePBound_highFullDyadicSuffixMax hp hp2 1 le_rfl (B + 1))

/-- Every finite collection of positive dilations satisfies the complete
sparse-maximal hypothesis with one universal constant, including the empty
family. -/
theorem finiteSparseMaximalHypothesis_dilatedHighSuffixFamily
    {N : ℕ} (B : ℕ) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    FiniteSparseMaximalHypothesis (dilatedHighSuffixFamily B a ha)
      highFullSuffixSparseConstant := by
  refine ⟨highFullSuffixSparseConstant_nonneg, ?_, ?_, ?_⟩
  · intro i f
    exact locallyIntegrable_dilatedOperator_of_continuous (a i) (ha i)
      (continuous_finiteFullDyadicSuffixMaxOperator 1 1 (B + 1)) f
  · intro i
    exact isSublinear_dilatedOperator (a i) (ha i)
      (isSublinear_finiteFullDyadicSuffixMaxOperator 1 1 (B + 1))
  · intro p hp hp2 i
    have hb := hasSparseOnePBound_dilatedHighSuffix B (a i) (ha i) hp hp2
    have hC : 0 ≤ highFullSuffixSparseConstant * holderConjugate p :=
      mul_nonneg highFullSuffixSparseConstant_nonneg (holderConjugate_spec hp).symm.pos.le
    exact ⟨⟨_, hC, hb⟩, sparseOnePNorm_le_of_bound hC hb⟩

/-- The actual finite maximum of the dilated high suffix operators has the
paper's logarithmic-squared weak bound, uniformly in both cutoffs and all
positive dilation parameters. -/
theorem hasWeakOneOneBound_dilatedHighSuffixFamily
    {N : ℕ} (B : ℕ) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    HasWeakOneOneBound
      (finiteSparseMaximalUniversalConstant * highFullSuffixSparseConstant *
        paperLog 1 N ^ 2)
      (finiteMax (dilatedHighSuffixFamily B a ha)) :=
  finiteSparseMaximal_hasWeakOneOneBound (dilatedHighSuffixFamily B a ha)
    highFullSuffixSparseConstant
    (finiteSparseMaximalHypothesis_dilatedHighSuffixFamily B a ha)


end
end QuadraticCarleson.KrauseLaceyHighSuffixDilationResolved
