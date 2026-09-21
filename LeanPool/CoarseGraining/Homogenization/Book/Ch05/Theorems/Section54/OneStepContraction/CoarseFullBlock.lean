/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CoarseRHSPrep

/-! # Coarse Full Block -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Section 5.3-beta full-block fluctuation sums

The public variance lemma uses the Section 5.4 beta.  The Section 5.3
coarse-fluctuation RHS uses the slower quarter-beta, so the one-step proof
needs the same refined budget argument with that beta.
-/

open Section53.JUpperBoundCoarseFluctuations

private theorem section53CoarseFluctuationBeta_lt_dim_div_two
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBeta hP4 < (d : ℝ) / 2 := by
  have hbeta_le := section53CoarseFluctuationBeta_le_sUpper hP4
  have hupper_lt : hP4.sUpper < 1 := hP4.sUpper_lt_one
  have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  nlinarith

private theorem lpVarianceDecay_gap_pos_section53
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < VarianceBoundGoodScale.lpVarianceDecay d hP4 -
      section53CoarseFluctuationBeta hP4 := by
  have hbeta := section53CoarseFluctuationBeta_lt_dim_div_two hP4
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast hP4.two_le_xi
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdiv_le : (d : ℝ) / (hP4.xi : ℝ) ≤ (d : ℝ) / 2 := by
    exact div_le_div_of_nonneg_left hd_nonneg (by norm_num) hxi_two
  dsimp [VarianceBoundGoodScale.lpVarianceDecay]
  nlinarith

private theorem sqrtVarianceDecay_gap_pos_section53
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < VarianceBoundGoodScale.sqrtVarianceDecay d -
      section53CoarseFluctuationBeta hP4 := by
  simpa [VarianceBoundGoodScale.sqrtVarianceDecay] using
    section53CoarseFluctuationBeta_lt_dim_div_two hP4

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P 0 hP4 := by
  simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

/-- Linear constant for refined pair budgets summed with the Section 5.3
beta. -/
noncomputable def oneStepCoarsePairLinearBudgetConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        (geometricDiscount
          (VarianceBoundGoodScale.lpVarianceDecay d hP4 -
            section53CoarseFluctuationBeta hP4) 1)⁻¹ +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        (geometricDiscount
          (VarianceBoundGoodScale.sqrtVarianceDecay d -
            section53CoarseFluctuationBeta hP4) 1)⁻¹)

theorem oneStepCoarsePairLinearBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ oneStepCoarsePairLinearBudgetConst hP4 := by
  unfold oneStepCoarsePairLinearBudgetConst
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hdiscLp :
      0 ≤ (geometricDiscount
        (VarianceBoundGoodScale.lpVarianceDecay d hP4 -
          section53CoarseFluctuationBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos
        (by simpa using lpVarianceDecay_gap_pos_section53 hP4)).le
  have hdiscSqrt :
      0 ≤ (geometricDiscount
        (VarianceBoundGoodScale.sqrtVarianceDecay d -
          section53CoarseFluctuationBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos
        (by simpa using sqrtVarianceDecay_gap_pos_section53 hP4)).le
  positivity

theorem pairPointwiseBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ VarianceBoundGoodScale.pairPointwiseBudgetConst hP4 := by
  unfold VarianceBoundGoodScale.pairPointwiseBudgetConst
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  positivity

/-- Constant controlling the Section 5.3-beta refined scalar budget. -/
noncomputable def oneStepWeightedRefinedBudgetConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹ +
    2 * oneStepCoarsePairLinearBudgetConst hP4 +
      2 * VarianceBoundGoodScale.pairPointwiseBudgetConst hP4 *
        oneStepCoarsePairLinearBudgetConst hP4

/-- The Section 5.3-beta refined scalar budget constant is nonnegative. -/
theorem oneStepWeightedRefinedBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ oneStepWeightedRefinedBudgetConst hP4 := by
  unfold oneStepWeightedRefinedBudgetConst
  have hG :
      0 ≤ (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos
        (by simpa using section53CoarseFluctuationBeta_pos hP4)).le
  have hL : 0 ≤ oneStepCoarsePairLinearBudgetConst hP4 :=
    oneStepCoarsePairLinearBudgetConst_nonneg hP4
  have hM : 0 ≤ VarianceBoundGoodScale.pairPointwiseBudgetConst hP4 :=
    pairPointwiseBudgetConst_nonneg hP4
  positivity

/-- Final constant for the Section 5.3-beta full-block fluctuation sum. -/
noncomputable def oneStepCoarseFullBlockConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  3 *
    (VarianceBoundGoodScale.refinedMatrixBudgetConst d *
      oneStepWeightedRefinedBudgetConst hP4)

theorem oneStepCoarseFullBlockConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ oneStepCoarseFullBlockConst hP4 := by
  unfold oneStepCoarseFullBlockConst
  have hM : 0 ≤ VarianceBoundGoodScale.refinedMatrixBudgetConst d := by
    unfold VarianceBoundGoodScale.refinedMatrixBudgetConst
    positivity
  have hB : 0 ≤ oneStepWeightedRefinedBudgetConst hP4 :=
    oneStepWeightedRefinedBudgetConst_nonneg hP4
  positivity

theorem sum_Icc_varianceWeight_mul_pairProbeRefinedK_le_section53
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight
            (section53CoarseFluctuationBeta hP4) m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) ≤
      oneStepCoarsePairLinearBudgetConst hP4 *
        widetildeThetaAtScale P 0 hP4 *
          Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) := by
  let β := section53CoarseFluctuationBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let Lp := Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi
  let Sqrt := Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi
  let γLp := VarianceBoundGoodScale.lpVarianceDecay d hP4
  let γSqrt := VarianceBoundGoodScale.sqrtVarianceDecay d
  let D := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let GLp := (geometricDiscount (γLp - β) 1)⁻¹
  let GSqrt := (geometricDiscount (γSqrt - β) 1)⁻¹
  have hθ : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hLp_nonneg : 0 ≤ Lp := by
    dsimp [Lp]
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Sqrt := by
    dsimp [Sqrt]
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hsumLp :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          Real.rpow (3 : ℝ) (-γLp * (j : ℝ))) ≤
        D * GLp := by
    simpa [β, γLp, D, GLp] using
      VarianceBoundGoodScale.sum_Icc_varianceWeight_mul_rpow_decay_le
        (β := section53CoarseFluctuationBeta hP4)
        (γ := VarianceBoundGoodScale.lpVarianceDecay d hP4)
        (lpVarianceDecay_gap_pos_section53 hP4) m
  have hsumSqrt :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ))) ≤
        D * GSqrt := by
    simpa [β, γSqrt, D, GSqrt, mul_comm, mul_left_comm, mul_assoc] using
      VarianceBoundGoodScale.sum_Icc_varianceWeight_mul_rpow_decay_le
        (β := section53CoarseFluctuationBeta hP4)
        (γ := VarianceBoundGoodScale.sqrtVarianceDecay d)
        (sqrtVarianceDecay_gap_pos_section53 hP4) m
  have hterm :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) ≤
          ∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              (16 * θ *
                (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ)) +
                  Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact mul_le_mul_of_nonneg_left
              (by
                simpa [β, θ, Lp, Sqrt, γLp, γSqrt] using
                  VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK_le_geometric
                    hP4 hdelta_le_half j)
              (VarianceBoundGoodScale.varianceWeight_nonneg β m j)
      _ =
          (∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
          ∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
  have hLp_part :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) ≤
        16 * θ * (Lp * (D * GLp)) := by
    have hLp_sum := mul_le_mul_of_nonneg_left hsumLp hLp_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hLp_sum
      (show 0 ≤ 16 * θ from mul_nonneg (by norm_num) hθ)
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hSqrt_part :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ))))) ≤
        16 * θ * (Sqrt * (D * GSqrt)) := by
    have hSqrt_sum := mul_le_mul_of_nonneg_left hsumSqrt hSqrt_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hSqrt_sum
      (show 0 ≤ 16 * θ from mul_nonneg (by norm_num) hθ)
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hscaled
  calc
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := hterm
    _ ≤
        16 * θ * (Lp * (D * GLp)) +
        16 * θ * (Sqrt * (D * GSqrt)) :=
        add_le_add hLp_part hSqrt_part
    _ =
        oneStepCoarsePairLinearBudgetConst hP4 *
          widetildeThetaAtScale P 0 hP4 *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) := by
        simp [oneStepCoarsePairLinearBudgetConst, β, θ, Lp, Sqrt, γLp, γSqrt,
          D, GLp, GSqrt]
        ring

theorem sum_Icc_varianceWeight_mul_pairProbeRefinedK_sq_le_section53
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight
            (section53CoarseFluctuationBeta hP4) m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
      VarianceBoundGoodScale.pairPointwiseBudgetConst hP4 *
        oneStepCoarsePairLinearBudgetConst hP4 *
          (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ) *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) := by
  let β := section53CoarseFluctuationBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let M := VarianceBoundGoodScale.pairPointwiseBudgetConst hP4
  let L := oneStepCoarsePairLinearBudgetConst hP4
  let D := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  have hθ : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using pairPointwiseBudgetConst_nonneg hP4
  have hlinear :=
    sum_Icc_varianceWeight_mul_pairProbeRefinedK_le_section53 hP4 hdelta_le_half m
  have hterm :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            ((M * θ) *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hK_nonneg :=
      VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK_nonneg
        hP4 hdelta_nonneg j
    have hK_le :
        VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ≤
          M * θ := by
      simpa [M, θ] using
        VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK_le_pointwiseConst
          hP4 hdelta_le_half j
    have hsq :
        VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) ≤
          (M * θ) *
            VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hK_le hK_nonneg
    exact mul_le_mul_of_nonneg_left hsq
      (VarianceBoundGoodScale.varianceWeight_nonneg β m j)
  calc
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            ((M * θ) *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) := hterm
    _ =
        (M * θ) *
          ∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
    _ ≤
        (M * θ) * (L * θ * D) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [β, θ, L, D] using hlinear)
          (mul_nonneg hM_nonneg hθ)
    _ =
        VarianceBoundGoodScale.pairPointwiseBudgetConst hP4 *
          oneStepCoarsePairLinearBudgetConst hP4 *
          (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ) *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) := by
        simp [M, L, θ, D, β]
        ring

private theorem sum_Icc_varianceWeight_mul_refinedVarianceBasicBudget_le_section53
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight
            (section53CoarseFluctuationBeta hP4) m j *
          VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) ≤
      oneStepWeightedRefinedBudgetConst hP4 *
        (delta +
          Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) *
            (widetildeThetaAtScale P 0 hP4 +
              (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ))) := by
  let β := section53CoarseFluctuationBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let D := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let C := oneStepWeightedRefinedBudgetConst hP4
  let L := oneStepCoarsePairLinearBudgetConst hP4
  let M := VarianceBoundGoodScale.pairPointwiseBudgetConst hP4
  let Gβ := (geometricDiscount β 1)⁻¹
  have hδ_nonneg : 0 ≤ delta := hdelta_pos.le
  have hθ : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (by norm_num) _
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using oneStepWeightedRefinedBudgetConst_nonneg hP4
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using oneStepCoarsePairLinearBudgetConst_nonneg hP4
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using pairPointwiseBudgetConst_nonneg hP4
  have hG_nonneg : 0 ≤ Gβ := by
    dsimp [Gβ, β]
    exact inv_nonneg.mpr
      (geometricDiscount_pos
        (by simpa using section53CoarseFluctuationBeta_pos hP4)).le
  have hC_ge_G : Gβ ≤ C := by
    dsimp [C, Gβ, oneStepWeightedRefinedBudgetConst]
    nlinarith [hL_nonneg, hM_nonneg]
  have hC_ge_2L : 2 * L ≤ C := by
    dsimp [C, L, Gβ, oneStepWeightedRefinedBudgetConst]
    nlinarith [hG_nonneg, hL_nonneg, hM_nonneg]
  have hC_ge_2ML : 2 * M * L ≤ C := by
    dsimp [C, M, L, Gβ, oneStepWeightedRefinedBudgetConst]
    nlinarith [hG_nonneg, hL_nonneg, hM_nonneg]
  have hbudgetTerm :
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) ≤
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (delta + 2 *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j +
              2 *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                  (2 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (VarianceBoundGoodScale.refinedVarianceBasicBudget_le_pairBudget hP4 hδ_nonneg j)
      (VarianceBoundGoodScale.varianceWeight_nonneg β m j)
  have hconst :
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j * delta) ≤ Gβ * delta := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j * delta) =
          (∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j) * delta := by
          rw [Finset.sum_mul]
      _ ≤ Gβ * delta := by
          exact mul_le_mul_of_nonneg_right
            (by
              simpa [β, Gβ] using
                VarianceBoundGoodScale.sum_Icc_varianceWeight_le_inv_geometricDiscount
                  (section53CoarseFluctuationBeta_pos hP4) m)
            hδ_nonneg
  have hlinear :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        L * θ * D := by
    simpa [β, L, θ, D] using
      sum_Icc_varianceWeight_mul_pairProbeRefinedK_le_section53
        hP4 hdelta_le_half m
  have hsquare :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
            (2 : ℕ)) ≤
        M * L * θ ^ (2 : ℕ) * D := by
    simpa [β, M, L, θ, D] using
      sum_Icc_varianceWeight_mul_pairProbeRefinedK_sq_le_section53
        hP4 hδ_nonneg hdelta_le_half m
  have hsum :
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (delta + 2 *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j +
              2 *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                  (2 : ℕ))) ≤
        Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (delta + 2 *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j +
              2 *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                  (2 : ℕ))) =
          (∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j * delta) +
          2 *
            (∑ j ∈ Finset.Icc 1 m,
              VarianceBoundGoodScale.varianceWeight β m j *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) +
          2 *
            (∑ j ∈ Finset.Icc 1 m,
              VarianceBoundGoodScale.varianceWeight β m j *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                  (2 : ℕ)) := by
          rw [show
            (∑ j ∈ Finset.Icc 1 m,
              VarianceBoundGoodScale.varianceWeight β m j *
                (delta + 2 *
                  VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j +
                  2 *
                    VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                      (2 : ℕ))) =
            (∑ j ∈ Finset.Icc 1 m,
              (VarianceBoundGoodScale.varianceWeight β m j * delta +
                2 * (VarianceBoundGoodScale.varianceWeight β m j *
                  VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j) +
                2 * (VarianceBoundGoodScale.varianceWeight β m j *
                  VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                    (2 : ℕ)))) by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ Gβ * delta + 2 * (L * θ * D) +
            2 * (M * L * θ ^ (2 : ℕ) * D) := by
          nlinarith
  have htail_nonneg : 0 ≤ θ + θ ^ (2 : ℕ) := add_nonneg hθ (sq_nonneg θ)
  have hinside_nonneg :
      0 ≤ delta + D * (θ + θ ^ (2 : ℕ)) :=
    add_nonneg hδ_nonneg (mul_nonneg hD htail_nonneg)
  calc
    (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) ≤
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            (delta + 2 *
              VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j +
              2 *
                VarianceBoundGoodScale.pairProbeRefinedDescendantAverageK hP4 delta j ^
                  (2 : ℕ)) := hbudgetTerm
    _ ≤ Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) :=
        hsum
    _ ≤ C * (delta + D * (θ + θ ^ (2 : ℕ))) := by
        calc
          Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) ≤
              C * delta + C * (D * θ) + C * (D * θ ^ (2 : ℕ)) := by
            have h1 := mul_le_mul_of_nonneg_right hC_ge_G hδ_nonneg
            have h2 := mul_le_mul_of_nonneg_right hC_ge_2L (mul_nonneg hθ hD)
            have h3 := mul_le_mul_of_nonneg_right hC_ge_2ML
              (mul_nonneg (sq_nonneg θ) hD)
            nlinarith
          _ = C * (delta + D * (θ + θ ^ (2 : ℕ))) := by ring

/-- The Section 5.3-beta full-block fluctuation sum is controlled by the
refined scalar budget at a good scale. -/
theorem oneStepCoarseFullBlockSumAtScale_le_budget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m ≤
      VarianceBoundGoodScale.refinedMatrixBudgetConst d *
        (oneStepWeightedRefinedBudgetConst hP4 *
          (delta +
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) *
              (widetildeThetaAtScale P 0 hP4 +
                (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ)))) := by
  let β := section53CoarseFluctuationBeta hP4
  let M := VarianceBoundGoodScale.refinedMatrixBudgetConst d
  have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    unfold VarianceBoundGoodScale.refinedMatrixBudgetConst
    positivity
  have hsum_matrix :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.refinedMatrixVarianceScaleBound hP4 delta j) ≤
        M *
          (∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.refinedMatrixVarianceScaleBound hP4 delta j) ≤
          ∑ j ∈ Finset.Icc 1 m,
            VarianceBoundGoodScale.varianceWeight β m j *
              (M * VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [M] using
                VarianceBoundGoodScale.refinedMatrixVarianceScaleBound_le_basicBudget
                  hP4 hdelta_nonneg (by linarith) j)
            (VarianceBoundGoodScale.varianceWeight_nonneg β m j)
      _ =
          M *
            (∑ j ∈ Finset.Icc 1 m,
              VarianceBoundGoodScale.varianceWeight β m j *
                VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
  have hsum_budget :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) ≤
        oneStepWeightedRefinedBudgetConst hP4 *
          (delta +
            Real.rpow (3 : ℝ) (-(β) * (m : ℝ)) *
              (widetildeThetaAtScale P 0 hP4 +
                (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ))) := by
    simpa [β] using
      sum_Icc_varianceWeight_mul_refinedVarianceBasicBudget_le_section53
        hP4 hdelta_pos hdelta_le_half m
  calc
    oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m =
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P := by
          simp [oneStepCoarseFullBlockSumAtScale, β]
    _ ≤
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            VarianceBoundGoodScale.refinedMatrixVarianceScaleBound hP4 delta j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_refinedMatrixVarianceScaleBound
              hP hStruct hP4 hdelta_nonneg m j (Finset.mem_Icc.mp hj).2
              hgood_upper hgood_lower)
            (VarianceBoundGoodScale.varianceWeight_nonneg β m j)
    _ ≤ M *
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            VarianceBoundGoodScale.refinedVarianceBasicBudget hP4 delta j) :=
        hsum_matrix
    _ ≤
        M *
          (oneStepWeightedRefinedBudgetConst hP4 *
            (delta +
              Real.rpow (3 : ℝ) (-(β) * (m : ℝ)) *
                (widetildeThetaAtScale P 0 hP4 +
                  (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hsum_budget hM_nonneg

/-- Under the one-step logarithmic scale separation, the Section 5.3-beta
full-block fluctuation sum is `O(sqrt(delta))`. -/
theorem oneStepCoarseFullBlockSumAtScale_le_sqrt_delta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (hsep :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ))
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m ≤
      oneStepCoarseFullBlockConst hP4 * Real.sqrt delta := by
  let θ := widetildeThetaAtScale P 0 hP4
  let D :=
    Real.rpow (3 : ℝ)
      (-(section53CoarseFluctuationBeta hP4) * (m : ℝ))
  let M := VarianceBoundGoodScale.refinedMatrixBudgetConst d
  let B := oneStepWeightedRefinedBudgetConst hP4
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    unfold VarianceBoundGoodScale.refinedMatrixBudgetConst
    positivity
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using oneStepWeightedRefinedBudgetConst_nonneg hP4
  have hMB_nonneg : 0 ≤ M * B := mul_nonneg hM_nonneg hB_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hbudget :=
    oneStepCoarseFullBlockSumAtScale_le_budget
      hP hStruct hP4 hdelta_pos hdelta_le_half m hgood_upper hgood_lower
  have habsorb :
      D * (θ + θ ^ (2 : ℕ)) ≤ 2 * Real.sqrt delta := by
    simpa [D, θ] using
      oneStepScaleSeparation_absorbs_section53Beta_widetildeThetaBudget
        hP4 hC hdelta_pos hdelta_le_half hsep
  have hdelta_le_sqrt :
      delta ≤ Real.sqrt delta :=
    delta_le_sqrt_of_pos_of_le_half hdelta_pos hdelta_le_half
  have hinside :
      delta + D * (θ + θ ^ (2 : ℕ)) ≤ 3 * Real.sqrt delta := by
    nlinarith
  calc
    oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m ≤
        M * (B * (delta + D * (θ + θ ^ (2 : ℕ)))) := by
          simpa [M, B, D, θ, mul_assoc] using hbudget
    _ = (M * B) * (delta + D * (θ + θ ^ (2 : ℕ))) := by ring
    _ ≤ (M * B) * (3 * Real.sqrt delta) :=
        mul_le_mul_of_nonneg_left hinside hMB_nonneg
    _ = oneStepCoarseFullBlockConst hP4 * Real.sqrt delta := by
        simp [oneStepCoarseFullBlockConst, M, B]
        ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
