/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.ArbitraryIntegrability

/-! # Normalized Statements -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

/-- Pointwise form of the variance triangle after interpreting variance as the
Section 5.4 squared operator-norm fluctuation. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverageNormalized_add_two_error
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center Q a ≤
      2 * descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct center Q j a +
      2 * normalizedCoarseAverageErrorOperatorNormSq
        hP hStruct center Q j a := by
  let parentMatrix : FullBlockMat d :=
    Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct center (cubeSet Q) a
  let averageMatrix : FullBlockMat d :=
    descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a
  let errorMatrix : FullBlockMat d :=
    normalizedCoarseAverageErrorMatrix hP hStruct center Q j a
  let parentCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) parentMatrix
  let averageCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) averageMatrix
  let errorCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) errorMatrix
  have hparent : parentMatrix = averageMatrix + errorMatrix := by
    simp [parentMatrix, averageMatrix, errorMatrix, normalizedCoarseAverageErrorMatrix]
  have hclm : parentCLM = averageCLM + errorCLM := by
    simp [parentCLM, averageCLM, errorCLM, hparent]
  calc
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center Q a
        = ‖parentCLM‖ ^ (2 : ℕ) := by
          simp [Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
            Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq,
            parentMatrix, parentCLM]
    _ = ‖averageCLM + errorCLM‖ ^ (2 : ℕ) := by
          rw [hclm]
    _ ≤ 2 * ‖averageCLM‖ ^ (2 : ℕ) + 2 * ‖errorCLM‖ ^ (2 : ℕ) :=
          norm_add_sq_le_two_sq_add_two_sq averageCLM errorCLM
    _ =
        2 * descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct center Q j a +
        2 * normalizedCoarseAverageErrorOperatorNormSq
          hP hStruct center Q j a := by
          simp [descendantsAverageNormalizedFluctuationOperatorNormSq,
            normalizedCoarseAverageErrorOperatorNormSq, averageMatrix, averageCLM,
            errorMatrix, errorCLM]

/-- A version whose first term is the descendant average of the existing
Section 5.4 fluctuation observable. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverage_add_two_error
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center Q a ≤
      2 * descendantsAverage Q j
        (fun R =>
          Ch04.fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
            (cubeSet R) a) +
      2 * normalizedCoarseAverageErrorOperatorNormSq
        hP hStruct center Q j a := by
  have htriangle :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverageNormalized_add_two_error
      hP hStruct center Q j a
  have hjensen :=
    descendantsAverageNormalizedFluctuationOperatorNormSq_le_descendantsAverage
      hP hStruct center Q j a
  nlinarith

/-- Section 5.6 variance estimate with quadratic `J` error, retaining the
descendant-average fluctuation term.  This is the pointwise form of the
manuscript variance splitting before the Jensen relaxation to the average of
child variances. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverageNormalized_add_eight_JTraceAverageSq_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      2 * descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct (m : ℤ) Q j a +
      8 * normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a := by
  filter_upwards
    [normalizedCoarseAverageErrorOperatorNormSq_le_four_normalizedBlockJTraceAverageSq_ae
      hP hStruct hP4 m Q j] with a herror
  have htriangle :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverageNormalized_add_two_error
      hP hStruct (m : ℤ) Q j a
  nlinarith

/-- Integrated Section 5.6 variance estimate with quadratic `J` error, using
the Section 5.4 squared operator-norm fluctuation observable for the variance
terms.  The integrability needed to pass from the a.e. estimate to expectation
is supplied by `(P4)`. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_two_descendantsAverageNormalized_add_eight_JTraceAverageSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) :
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (n : ℤ)) a ∂P ≤
      2 *
        ∫ a,
          descendantsAverageNormalizedFluctuationOperatorNormSq
            hP hStruct (m : ℤ) (originCube d (n : ℤ)) (n - k) a ∂P +
      8 *
        ∫ a,
          normalizedBlockJTraceAverageSq hP hStruct (m : ℤ)
            (originCube d (n : ℤ)) (n - k) a ∂P := by
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  let F : RegCoeffField d → ℝ :=
    fun a =>
      descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct (m : ℤ) Q j a
  let J : RegCoeffField d → ℝ :=
    fun a => normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a
  have hFInt : Integrable F P := by
    simpa [F, Q, j] using
      integrable_descendantsAverageNormalizedFluctuationOperatorNormSq_from_P4_of_stationary
        hP hStruct hP4 m n k hk
  have hJInt : Integrable J P := by
    simpa [J, Q, j] using
      integrable_normalizedBlockJTraceAverageSq_from_P4_of_stationary
        hP hStruct hP4 m n k hk
  have hRhsInt : Integrable (fun a : RegCoeffField d => 2 * F a + 8 * J a) P :=
    (hFInt.const_mul (2 : ℝ)).add (hJInt.const_mul (8 : ℝ))
  have hpoint :
      (fun a : RegCoeffField d =>
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) Q a)
        ≤ᵐ[P]
      fun a : RegCoeffField d => 2 * F a + 8 * J a := by
    simpa [F, J, Q, j] using
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverageNormalized_add_eight_JTraceAverageSq_ae
        hP hStruct hP4 m Q j
  have hmono :
      ∫ a,
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (m : ℤ) Q a ∂P ≤
        ∫ a, 2 * F a + 8 * J a ∂P := by
    refine integral_mono_of_nonneg ?_ hRhsInt hpoint
    filter_upwards with a
    exact
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
        hP hStruct (m : ℤ) Q a
  calc
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (n : ℤ)) a ∂P
        = ∫ a,
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) Q a ∂P := by
          rfl
    _ ≤ ∫ a, 2 * F a + 8 * J a ∂P := hmono
    _ = ∫ a, 2 * F a ∂P + ∫ a, 8 * J a ∂P := by
          rw [integral_add (hFInt.const_mul (2 : ℝ)) (hJInt.const_mul (8 : ℝ))]
    _ = 2 * ∫ a, F a ∂P + 8 * ∫ a, J a ∂P := by
          rw [integral_const_mul, integral_const_mul]
    _ =
      2 *
        ∫ a,
          descendantsAverageNormalizedFluctuationOperatorNormSq
            hP hStruct (m : ℤ) (originCube d (n : ℤ)) (n - k) a ∂P +
      8 *
        ∫ a,
          normalizedBlockJTraceAverageSq hP hStruct (m : ℤ)
            (originCube d (n : ℤ)) (n - k) a ∂P := by
          rfl

/-- Section 5.6 variance estimate with quadratic `J` error, expressed through
the Section 5.4 squared operator-norm fluctuation observable.  This is the
a.s. pointwise inequality whose expectation gives the manuscript display
`e.var.a.star` for the scalar block normalization used in Section 5.4. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverage_add_eight_JTraceAverageSq_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      2 * descendantsAverage Q j
        (fun R =>
          Ch04.fullBlockNormalizedFluctuationOperatorNormSq hP hStruct (m : ℤ)
            (cubeSet R) a) +
      8 * normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a := by
  filter_upwards
    [normalizedCoarseAverageErrorOperatorNormSq_le_four_normalizedBlockJTraceAverageSq_ae
      hP hStruct hP4 m Q j] with a herror
  have htriangle :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_descendantsAverage_add_two_error
      hP hStruct (m : ℤ) Q j a
  nlinarith
end

end Section56
end Ch05
end Book
end Homogenization
