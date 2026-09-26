/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScaleAbsorption

/-! # Variance Bound Good Scale -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open scoped BigOperators

noncomputable section

/-!
# Variance bound at a good scale

This file exposes the LaTeX-facing Section 5.4 variance lemma.  The proof
assembles the refined finite-probe estimate, the deterministic budget
summation, and the logarithmic scale-separation absorption.
-/

/-- Final constant used in the good-scale variance bound. -/
noncomputable def varianceBoundGoodScaleConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  max 1
    (max (varianceScaleSeparationConst hP4)
      (3 * (refinedMatrixBudgetConst d * weightedRefinedBudgetConst hP4)))

/-- Parameter-only version of the Section 5.4 variance beta core. -/
noncomputable def section54VarianceBetaCoreParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  min (1 - params.sUpper - params.sLower)
    (min params.sUpper
      (min params.sLower
        (min (params.sUpper - (d : ℝ) / (params.xi : ℝ))
          (params.sLower - (d : ℝ) / (params.xi : ℝ)))))

/-- Parameter-only version of the Section 5.4 variance beta. -/
noncomputable def section54VarianceBetaParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  section54VarianceBetaCoreParams params / 2

/-- Parameter-only version of the variance scale-separation constant. -/
noncomputable def varianceScaleSeparationConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  8 * (section54VarianceBetaParams params * Real.log 3)⁻¹

/-- Parameter-only version of the `L^ξ` geometric decay exponent. -/
noncomputable def lpVarianceDecayParams (d : ℕ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (d : ℝ) - (d : ℝ) / (params.xi : ℝ)

/-- Parameter-only version of the linear weighted pair-budget constant. -/
noncomputable def pairLinearBudgetConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 params.xi *
        (geometricDiscount
          (lpVarianceDecayParams d params - section54VarianceBetaParams params) 1)⁻¹ +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 params.xi *
        (geometricDiscount (sqrtVarianceDecay d - section54VarianceBetaParams params) 1)⁻¹)

/-- Parameter-only version of the pointwise pair-budget constant. -/
noncomputable def pairPointwiseBudgetConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 params.xi +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 params.xi)

/-- Parameter-only version of the weighted refined budget constant. -/
noncomputable def weightedRefinedBudgetConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (geometricDiscount (section54VarianceBetaParams params) 1)⁻¹ +
    2 * pairLinearBudgetConstParams params +
      2 * pairPointwiseBudgetConstParams params * pairLinearBudgetConstParams params

/-- Parameter-only final constant for the good-scale variance bound. -/
noncomputable def varianceBoundGoodScaleConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  max 1
    (max (varianceScaleSeparationConstParams params)
      (3 * (refinedMatrixBudgetConst d * weightedRefinedBudgetConstParams params)))

@[simp]
theorem section54VarianceBetaCoreParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaCoreParams hP4.params =
      section54VarianceBetaCore hP4 := rfl

@[simp]
theorem section54VarianceBetaParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaParams hP4.params =
      section54VarianceBeta hP4 := rfl

@[simp]
theorem varianceScaleSeparationConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    varianceScaleSeparationConstParams hP4.params =
      varianceScaleSeparationConst hP4 := rfl

@[simp]
theorem lpVarianceDecayParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    lpVarianceDecayParams d hP4.params = lpVarianceDecay d hP4 := rfl

@[simp]
theorem pairLinearBudgetConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    pairLinearBudgetConstParams hP4.params =
      pairLinearBudgetConst hP4 := rfl

@[simp]
theorem pairPointwiseBudgetConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    pairPointwiseBudgetConstParams hP4.params =
      pairPointwiseBudgetConst hP4 := rfl

@[simp]
theorem weightedRefinedBudgetConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    weightedRefinedBudgetConstParams hP4.params =
      weightedRefinedBudgetConst hP4 := rfl

@[simp]
theorem varianceBoundGoodScaleConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    varianceBoundGoodScaleConstParams hP4.params =
      varianceBoundGoodScaleConst hP4 := rfl

private theorem refinedMatrixBudgetConst_nonneg (d : ℕ) :
    0 ≤ refinedMatrixBudgetConst d := by
  unfold refinedMatrixBudgetConst
  positivity

private theorem varianceBoundGoodScaleConstParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < varianceBoundGoodScaleConstParams params := by
  unfold varianceBoundGoodScaleConstParams
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

private theorem varianceBoundGoodScaleConst_ge_scaleSep
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    varianceScaleSeparationConst hP4 ≤ varianceBoundGoodScaleConst hP4 := by
  unfold varianceBoundGoodScaleConst
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem varianceBoundGoodScaleConst_ge_budget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    3 * (refinedMatrixBudgetConst d * weightedRefinedBudgetConst hP4) ≤
      varianceBoundGoodScaleConst hP4 := by
  unfold varianceBoundGoodScaleConst
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- Section 5.4, variance bound at a good scale. -/
theorem varianceBoundGoodScale_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta : ℝ}, 0 < delta → delta ≤ 1 / 2 →
      ∀ {m : ℕ},
        C * (params.xi : ℝ) *
            Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
              widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ) →
        hP.barSigmaAtScale hStruct 0 ≤
            (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ) →
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
            (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ →
        varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m ≤
          C * Real.sqrt delta := by
  refine ⟨varianceBoundGoodScaleConstParams params, ?_, ?_⟩
  · exact varianceBoundGoodScaleConstParams_pos params
  intro P hP hStruct hP4 hparams delta hdelta_pos hdelta_le_half m hsep
    hgood_upper hgood_lower
  subst params
  let C : ℝ := varianceBoundGoodScaleConst hP4
  let θ : ℝ := widetildeThetaAtScale P 0 hP4
  let D : ℝ := Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ))
  let M : ℝ := refinedMatrixBudgetConst d
  let B : ℝ := weightedRefinedBudgetConst hP4
  have hsep_law :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ) := by
    simpa [C] using hsep
  have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
  have hdelta_le_one : delta ≤ 1 := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using refinedMatrixBudgetConst_nonneg d
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using weightedRefinedBudgetConst_nonneg hP4
  have hMB_nonneg : 0 ≤ M * B := mul_nonneg hM_nonneg hB_nonneg
  have hsum_matrix :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          refinedMatrixVarianceScaleBound hP4 delta j) ≤
        M *
          (∑ j ∈ Finset.Icc 1 m,
            varianceWeight (section54VarianceBeta hP4) m j *
              refinedVarianceBasicBudget hP4 delta j) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          refinedMatrixVarianceScaleBound hP4 delta j) ≤
          ∑ j ∈ Finset.Icc 1 m,
            varianceWeight (section54VarianceBeta hP4) m j *
              (M * refinedVarianceBasicBudget hP4 delta j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [M] using
                refinedMatrixVarianceScaleBound_le_basicBudget
                  hP4 hdelta_nonneg hdelta_le_one j)
            (varianceWeight_nonneg (section54VarianceBeta hP4) m j)
      _ =
          M *
            (∑ j ∈ Finset.Icc 1 m,
              varianceWeight (section54VarianceBeta hP4) m j *
                refinedVarianceBasicBudget hP4 delta j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
  have hsum_budget :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          refinedVarianceBasicBudget hP4 delta j) ≤
        B * (delta + D * (θ + θ ^ (2 : ℕ))) := by
    simpa [B, D, θ] using
      sum_Icc_varianceWeight_mul_refinedVarianceBasicBudget_le
        hP4 hdelta_pos hdelta_le_half m
  have habsorb : D * (θ + θ ^ (2 : ℕ)) ≤ 2 * delta := by
    simpa [C, D, θ] using
      scaleSeparation_absorbs_widetildeThetaBudget
        hP4 (hC := varianceBoundGoodScaleConst_ge_scaleSep hP4)
        hdelta_pos hdelta_le_half hsep_law
  have hinside_sqrt :
      delta + D * (θ + θ ^ (2 : ℕ)) ≤ 3 * Real.sqrt delta := by
    have hδ_le_sqrt := le_sqrt_of_pos_of_le_half hdelta_pos hdelta_le_half
    nlinarith
  have hbudget_sqrt :
      M * (B * (delta + D * (θ + θ ^ (2 : ℕ)))) ≤
        (3 * (M * B)) * Real.sqrt delta := by
    calc
      M * (B * (delta + D * (θ + θ ^ (2 : ℕ)))) =
          (M * B) * (delta + D * (θ + θ ^ (2 : ℕ))) := by ring
      _ ≤ (M * B) * (3 * Real.sqrt delta) :=
          mul_le_mul_of_nonneg_left hinside_sqrt hMB_nonneg
      _ = (3 * (M * B)) * Real.sqrt delta := by ring
  have hC_budget :
      3 * (M * B) ≤ C := by
    simpa [C, M, B] using varianceBoundGoodScaleConst_ge_budget hP4
  calc
    varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m ≤
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight (section54VarianceBeta hP4) m j *
            refinedMatrixVarianceScaleBound hP4 delta j :=
      varianceGoodScaleFullBlockSumAtScale_le_weighted_refinedMatrixVarianceScaleBound
        hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower
    _ ≤ M *
        (∑ j ∈ Finset.Icc 1 m,
          varianceWeight (section54VarianceBeta hP4) m j *
            refinedVarianceBasicBudget hP4 delta j) := hsum_matrix
    _ ≤ M * (B * (delta + D * (θ + θ ^ (2 : ℕ)))) :=
      mul_le_mul_of_nonneg_left hsum_budget hM_nonneg
    _ ≤ (3 * (M * B)) * Real.sqrt delta := hbudget_sqrt
    _ ≤ C * Real.sqrt delta :=
      mul_le_mul_of_nonneg_right hC_budget hsqrt_nonneg
    _ = varianceBoundGoodScaleConstParams hP4.params * Real.sqrt delta := by
      simp [C]

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
