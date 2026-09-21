/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.BudgetAbsorption

/-! # Final Absorption -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open scoped BigOperators

noncomputable section

/-!
# Final scalar absorption for the good-scale variance bound

This file finishes the purely deterministic part of the Section 5.4 variance
lemma.  The analytic work has already reduced the fluctuation estimate to the
refined scalar budgets in `BudgetAbsorption`; here we sum those budgets and
absorb the remaining `\widetilde\Theta_0` terms with the manuscript
scale-separation hypothesis.
-/

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P 0 hP4 := by
  simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

private theorem weighted_rpow_decay_eq
    {β γ : ℝ} {m j : ℕ} (hj : j ≤ m) :
    varianceWeight β m j * Real.rpow (3 : ℝ) (-γ * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
        Real.rpow (3 : ℝ) (-(γ - β) * (j : ℝ)) := by
  unfold varianceWeight
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub hj]
  rw [hcast]
  calc
    Real.rpow (3 : ℝ) (-β * ((m : ℝ) - (j : ℝ))) *
        Real.rpow (3 : ℝ) (-γ * (j : ℝ)) =
      Real.rpow (3 : ℝ)
        (-β * ((m : ℝ) - (j : ℝ)) + -γ * (j : ℝ)) := by
        exact (Real.rpow_add h3 _ _).symm
    _ = Real.rpow (3 : ℝ)
        (-β * (m : ℝ) + -(γ - β) * (j : ℝ)) := by
        congr 1
        ring
    _ = Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
        Real.rpow (3 : ℝ) (-(γ - β) * (j : ℝ)) := by
        exact Real.rpow_add h3 _ _

/-- A beta-weighted finite sum with an additional scale decay gains the
top-scale factor `3^{-βm}`. -/
theorem sum_Icc_varianceWeight_mul_rpow_decay_le
    {β γ : ℝ} (hgap : 0 < γ - β) (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
      varianceWeight β m j * Real.rpow (3 : ℝ) (-γ * (j : ℝ))) ≤
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
        (geometricDiscount (γ - β) 1)⁻¹ := by
  let f : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-(γ - β) * (j : ℝ))
  have hsummable : Summable f := by
    simpa [f] using Section52.summable_rpow_three_neg_mul_nat hgap
  have hnonneg : ∀ j : ℕ, 0 ≤ f j := by
    intro j
    dsimp [f]
    exact Real.rpow_nonneg (by norm_num) _
  calc
    (∑ j ∈ Finset.Icc 1 m,
      varianceWeight β m j * Real.rpow (3 : ℝ) (-γ * (j : ℝ))) =
        Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
          ∑ j ∈ Finset.Icc 1 m, f j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact weighted_rpow_decay_eq (β := β) (γ := γ)
          (m := m) (j := j) (Finset.mem_Icc.mp hj).2
    _ ≤ Real.rpow (3 : ℝ) (-β * (m : ℝ)) * ∑' j : ℕ, f j := by
        exact mul_le_mul_of_nonneg_left
          (hsummable.sum_le_tsum (Finset.Icc 1 m) (fun j _ => hnonneg j))
          (Real.rpow_nonneg (by norm_num) _)
    _ = Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
        (geometricDiscount (γ - β) 1)⁻¹ := by
        rw [Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hgap]

/-- The pair-probe descendant-average budget has the expected two geometric
decay components. -/
theorem pairProbeRefinedDescendantAverageK_eq_geometric
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (delta : ℝ) (j : ℕ) :
    pairProbeRefinedDescendantAverageK hP4 delta j =
      8 * ((1 + delta) *
          Ch04.widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi) *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ)
              (((d : ℝ) / (hP4.xi : ℝ) - (d : ℝ)) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-((d : ℝ) / 2 * (j : ℝ)))) := by
  have hj_nonneg : 0 ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
  rw [pairProbeRefinedDescendantAverageK]
  rw [Section52.section52_descendantsAtScale_originCube_int_zero_card_inv d hj_nonneg]
  rw [Section52.section52_descendantsAtScale_originCube_int_zero_card_rpow d hP4.xi hj_nonneg]
  rw [Section52.section52_descendantsAtScale_originCube_int_zero_card_sqrt d hj_nonneg]
  simp [widetildeThetaAtScale]
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hLp_pow :
      Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) =
        Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ) - (d : ℝ)) *
          (j : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) =
        Real.rpow (3 : ℝ)
          (-((d : ℝ) * (j : ℝ)) + ((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) := by
        exact (Real.rpow_add h3 _ _).symm
      _ = Real.rpow (3 : ℝ)
          (((d : ℝ) / (hP4.xi : ℝ) - (d : ℝ)) * (j : ℝ)) := by
        congr 1
        ring
  have hSqrt_pow :
      Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
          Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (j : ℝ)) =
        Real.rpow (3 : ℝ) (-((d : ℝ) / 2 * (j : ℝ))) := by
    calc
      Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
          Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (j : ℝ)) =
        Real.rpow (3 : ℝ)
          (-((d : ℝ) * (j : ℝ)) + ((d : ℝ) / 2) * (j : ℝ)) := by
        exact (Real.rpow_add h3 _ _).symm
      _ = Real.rpow (3 : ℝ) (-((d : ℝ) / 2 * (j : ℝ))) := by
        congr 1
        ring
  calc
    Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
              Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) *
            (8 * ((1 + delta) *
              Ch04.widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (j : ℝ)) *
            (8 * ((1 + delta) *
              Ch04.widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi))) =
      8 * ((1 + delta) *
          Ch04.widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi) *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            (Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ))) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            (Real.rpow (3 : ℝ) (-((d : ℝ) * (j : ℝ))) *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (j : ℝ)))) := by
        ring
    _ =
      8 * ((1 + delta) *
          Ch04.widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi) *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ)
              (((d : ℝ) / (hP4.xi : ℝ) - (d : ℝ)) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-((d : ℝ) / 2 * (j : ℝ)))) := by
        rw [hLp_pow, hSqrt_pow]

/-- The `L^ξ` geometric decay exponent in the refined pair budget. -/
noncomputable def lpVarianceDecay
    (d : ℕ) [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  (d : ℝ) - (d : ℝ) / (hP4.xi : ℝ)

/-- The square-root geometric decay exponent in the refined pair budget. -/
noncomputable def sqrtVarianceDecay (d : ℕ) : ℝ :=
  (d : ℝ) / 2

private theorem lpVarianceDecay_gap_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < lpVarianceDecay d hP4 - section54VarianceBeta hP4 := by
  have hbeta := section54VarianceBeta_lt_dim_div_two hP4
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast hP4.two_le_xi
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdiv_le : (d : ℝ) / (hP4.xi : ℝ) ≤ (d : ℝ) / 2 := by
    exact div_le_div_of_nonneg_left hd_nonneg (by norm_num) hxi_two
  dsimp [lpVarianceDecay]
  linarith

private theorem sqrtVarianceDecay_gap_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < sqrtVarianceDecay d - section54VarianceBeta hP4 := by
  simpa [sqrtVarianceDecay] using section54VarianceBeta_lt_dim_div_two hP4

private theorem lpVarianceDecay_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ lpVarianceDecay d hP4 := by
  have hgap := lpVarianceDecay_gap_pos hP4
  have hbeta := section54VarianceBeta_nonneg hP4
  linarith

private theorem sqrtVarianceDecay_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ sqrtVarianceDecay d := by
  have hgap := sqrtVarianceDecay_gap_pos hP4
  have hbeta := section54VarianceBeta_nonneg hP4
  linarith

/-- Linear constant for the weighted refined pair budgets. -/
noncomputable def pairLinearBudgetConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        (geometricDiscount (lpVarianceDecay d hP4 - section54VarianceBeta hP4) 1)⁻¹ +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        (geometricDiscount (sqrtVarianceDecay d - section54VarianceBeta hP4) 1)⁻¹)

/-- Pointwise constant for the refined pair budget before the extra
top-scale decay is summed. -/
noncomputable def pairPointwiseBudgetConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi)

private theorem pairLinearBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ pairLinearBudgetConst hP4 := by
  unfold pairLinearBudgetConst
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hdiscLp :
      0 ≤ (geometricDiscount (lpVarianceDecay d hP4 -
        section54VarianceBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos (by simpa using lpVarianceDecay_gap_pos hP4)).le
  have hdiscSqrt :
      0 ≤ (geometricDiscount (sqrtVarianceDecay d -
        section54VarianceBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos (by simpa using sqrtVarianceDecay_gap_pos hP4)).le
  positivity

private theorem pairPointwiseBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ pairPointwiseBudgetConst hP4 := by
  unfold pairPointwiseBudgetConst
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  positivity

/-- Pointwise refined pair budgets are controlled by the two geometric
decays with the scale-zero moment factor. -/
theorem pairProbeRefinedDescendantAverageK_le_geometric
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_le_half : delta ≤ 1 / 2)
    (j : ℕ) :
    pairProbeRefinedDescendantAverageK hP4 delta j ≤
      16 * widetildeThetaAtScale P 0 hP4 *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ))) := by
  have htheta : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_zero_nonneg hP4
  let A : ℝ :=
    Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
      unfold Ch04.rosenthalDescendantsAtScaleLpConst
      positivity
    have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
      unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
        IndependentSums.rosenthalBennettIntegralConst
      positivity
    positivity
  have hfactor :
      8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) ≤
        16 * widetildeThetaAtScale P 0 hP4 := by
    have hcoef : 8 * (1 + delta) ≤ (16 : ℝ) := by linarith
    calc
      8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)
          = (8 * (1 + delta)) * widetildeThetaAtScale P 0 hP4 := by ring
      _ ≤ 16 * widetildeThetaAtScale P 0 hP4 :=
          mul_le_mul_of_nonneg_right hcoef htheta
  have heq := pairProbeRefinedDescendantAverageK_eq_geometric hP4 delta j
  have heq' :
      pairProbeRefinedDescendantAverageK hP4 delta j =
        8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) * A := by
    simpa [A, widetildeThetaAtScale, lpVarianceDecay, sqrtVarianceDecay] using heq
  calc
    pairProbeRefinedDescendantAverageK hP4 delta j =
        8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) * A := heq'
    _ ≤ (16 * widetildeThetaAtScale P 0 hP4) * A :=
      mul_le_mul_of_nonneg_right hfactor hA_nonneg
    _ = 16 * widetildeThetaAtScale P 0 hP4 * A := by ring
    _ =
      16 * widetildeThetaAtScale P 0 hP4 *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ))) := rfl

/-- A scale-uniform pointwise bound for refined pair budgets. -/
theorem pairProbeRefinedDescendantAverageK_le_pointwiseConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_le_half : delta ≤ 1 / 2)
    (j : ℕ) :
    pairProbeRefinedDescendantAverageK hP4 delta j ≤
      pairPointwiseBudgetConst hP4 * widetildeThetaAtScale P 0 hP4 := by
  have hgeo := pairProbeRefinedDescendantAverageK_le_geometric hP4 hdelta_le_half j
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hLp_decay :
      Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by
        have hγ := lpVarianceDecay_nonneg hP4
        have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hj)
  have hSqrt_decay :
      Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by
        have hγ := sqrtVarianceDecay_nonneg hP4
        have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hj)
  have htheta : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_zero_nonneg hP4
  have hinside :
      Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ)) ≤
        Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    exact add_le_add
      (by simpa using mul_le_mul_of_nonneg_left hLp_decay hLp_nonneg)
      (by simpa using mul_le_mul_of_nonneg_left hSqrt_decay hSqrt_nonneg)
  calc
    pairProbeRefinedDescendantAverageK hP4 delta j ≤
      16 * widetildeThetaAtScale P 0 hP4 *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ))) := hgeo
    _ ≤
      16 * widetildeThetaAtScale P 0 hP4 *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi) :=
        mul_le_mul_of_nonneg_left hinside (mul_nonneg (by norm_num) htheta)
    _ = pairPointwiseBudgetConst hP4 * widetildeThetaAtScale P 0 hP4 := by
        simp [pairPointwiseBudgetConst]
        ring

/-- The compressed scalar budget is controlled by the pair budget. -/
theorem refinedVarianceBasicBudget_le_pairBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (j : ℕ) :
    refinedVarianceBasicBudget hP4 delta j ≤
      delta + 2 * pairProbeRefinedDescendantAverageK hP4 delta j +
        2 * pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) := by
  let c := coordinateProbeRefinedDescendantAverageK hP4 delta j
  let p := pairProbeRefinedDescendantAverageK hP4 delta j
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using coordinateProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
  have hp_eq : p = 4 * c := by
    dsimp [p, c]
    simp [pairProbeRefinedDescendantAverageK, coordinateProbeRefinedDescendantAverageK]
    ring
  have hp_nonneg : 0 ≤ p := by
    rw [hp_eq]
    positivity
  have hc_le_p : c ≤ p := by
    rw [hp_eq]
    calc
      c = 1 * c := by ring
      _ ≤ 4 * c := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4) hc_nonneg
  have hc_sq_le_p_sq : c ^ (2 : ℕ) ≤ p ^ (2 : ℕ) :=
    pow_le_pow_left₀ hc_nonneg hc_le_p 2
  unfold refinedVarianceBasicBudget
  dsimp [c, p] at *
  linarith [sq_nonneg p]

/-- Constant controlling the beta-weighted refined scalar budget before the
scale-separation absorption. -/
noncomputable def weightedRefinedBudgetConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  (geometricDiscount (section54VarianceBeta hP4) 1)⁻¹ +
    2 * pairLinearBudgetConst hP4 +
      2 * pairPointwiseBudgetConst hP4 * pairLinearBudgetConst hP4

theorem weightedRefinedBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ weightedRefinedBudgetConst hP4 := by
  unfold weightedRefinedBudgetConst
  have hdisc :
      0 ≤ (geometricDiscount (section54VarianceBeta hP4) 1)⁻¹ :=
    inv_nonneg.mpr
      (geometricDiscount_pos (by simpa using section54VarianceBeta_pos hP4)).le
  have hlin := pairLinearBudgetConst_nonneg hP4
  have hpoint := pairPointwiseBudgetConst_nonneg hP4
  have hprod : 0 ≤ pairPointwiseBudgetConst hP4 * pairLinearBudgetConst hP4 :=
    mul_nonneg hpoint hlin
  linarith

/-- Weighted sum of the refined pair budgets. -/
theorem sum_Icc_varianceWeight_mul_pairProbeRefinedK_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          pairProbeRefinedDescendantAverageK hP4 delta j) ≤
      pairLinearBudgetConst hP4 *
        widetildeThetaAtScale P 0 hP4 *
          Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) := by
  let β := section54VarianceBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let Lp := Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi
  let Sqrt := Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi
  let γLp := lpVarianceDecay d hP4
  let γSqrt := sqrtVarianceDecay d
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
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (by norm_num) _
  have hsumLp :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))) ≤
        D * GLp := by
    simpa [β, γLp, D, GLp] using
      sum_Icc_varianceWeight_mul_rpow_decay_le
        (β := section54VarianceBeta hP4) (γ := lpVarianceDecay d hP4)
        (lpVarianceDecay_gap_pos hP4) m
  have hsumSqrt :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ))) ≤
        D * GSqrt := by
    simpa [β, γSqrt, D, GSqrt, mul_comm, mul_left_comm, mul_assoc] using
      sum_Icc_varianceWeight_mul_rpow_decay_le
        (β := section54VarianceBeta hP4) (γ := sqrtVarianceDecay d)
        (sqrtVarianceDecay_gap_pos hP4) m
  have hterm :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j * pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j * pairProbeRefinedDescendantAverageK hP4 delta j) ≤
          ∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              (16 * θ *
                (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ)) +
                  Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact mul_le_mul_of_nonneg_left
              (by
                simpa [β, θ, Lp, Sqrt, γLp, γSqrt] using
                  pairProbeRefinedDescendantAverageK_le_geometric hP4 hdelta_le_half j)
              (varianceWeight_nonneg β m j)
      _ =
          (∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
          ∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
  have hLp_part :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) ≤
        16 * θ * (Lp * (D * GLp)) := by
    have hLp_sum := mul_le_mul_of_nonneg_left hsumLp hLp_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hLp_sum
      (show 0 ≤ 16 * θ from mul_nonneg (by norm_num) hθ)
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hSqrt_part :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ))))) ≤
        16 * θ * (Sqrt * (D * GSqrt)) := by
    have hSqrt_sum := mul_le_mul_of_nonneg_left hsumSqrt hSqrt_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hSqrt_sum
      (show 0 ≤ 16 * θ from mul_nonneg (by norm_num) hθ)
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hscaled
  calc
    (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j * pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (16 * θ * (Lp * Real.rpow (3 : ℝ) (-γLp * (j : ℝ))))) +
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (16 * θ * (Sqrt * Real.rpow (3 : ℝ) (-γSqrt * (j : ℝ)))) := hterm
    _ ≤
        16 * θ * (Lp * (D * GLp)) +
        16 * θ * (Sqrt * (D * GSqrt)) :=
        add_le_add hLp_part hSqrt_part
    _ =
        16 * θ * (Lp * (D * GLp) + Sqrt * (D * GSqrt)) := by
        ring
    _ =
        pairLinearBudgetConst hP4 * widetildeThetaAtScale P 0 hP4 *
          Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) := by
        simp [pairLinearBudgetConst, β, θ, Lp, Sqrt, γLp, γSqrt, D, GLp, GSqrt]
        ring

/-- Weighted sum of the squares of the refined pair budgets. -/
theorem sum_Icc_varianceWeight_mul_pairProbeRefinedK_sq_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
      pairPointwiseBudgetConst hP4 * pairLinearBudgetConst hP4 *
        (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ) *
          Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) := by
  let β := section54VarianceBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let M := pairPointwiseBudgetConst hP4
  let L := pairLinearBudgetConst hP4
  let D := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  have hθ : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using pairPointwiseBudgetConst_nonneg hP4
  have hlinear :=
    sum_Icc_varianceWeight_mul_pairProbeRefinedK_le hP4 hdelta_le_half m
  have hterm :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            ((M * θ) * pairProbeRefinedDescendantAverageK hP4 delta j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hK_nonneg :=
      pairProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
    have hK_le : pairProbeRefinedDescendantAverageK hP4 delta j ≤ M * θ := by
      simpa [M, θ] using
        pairProbeRefinedDescendantAverageK_le_pointwiseConst hP4 hdelta_le_half j
    have hsq :
        pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) ≤
          (M * θ) * pairProbeRefinedDescendantAverageK hP4 delta j := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hK_le hK_nonneg
    exact mul_le_mul_of_nonneg_left hsq (varianceWeight_nonneg β m j)
  calc
    (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            ((M * θ) * pairProbeRefinedDescendantAverageK hP4 delta j) := hterm
    _ =
        (M * θ) *
          ∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              pairProbeRefinedDescendantAverageK hP4 delta j := by
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
        pairPointwiseBudgetConst hP4 * pairLinearBudgetConst hP4 *
          (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ) *
            Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) := by
        simp [M, L, θ, D, β]
        ring

/-- The full weighted refined scalar budget has only the manuscript-size
terms `δ` and `3^{-βm}(\widetilde\Theta_0+\widetilde\Theta_0^2)`. -/
theorem sum_Icc_varianceWeight_mul_refinedVarianceBasicBudget_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          refinedVarianceBasicBudget hP4 delta j) ≤
      weightedRefinedBudgetConst hP4 *
        (delta +
          Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) *
            (widetildeThetaAtScale P 0 hP4 +
              (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ))) := by
  let β := section54VarianceBeta hP4
  let θ := widetildeThetaAtScale P 0 hP4
  let D := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let C := weightedRefinedBudgetConst hP4
  let L := pairLinearBudgetConst hP4
  let M := pairPointwiseBudgetConst hP4
  let Gβ := (geometricDiscount β 1)⁻¹
  have hδ_nonneg : 0 ≤ delta := hdelta_pos.le
  have hθ : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (by norm_num) _
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using weightedRefinedBudgetConst_nonneg hP4
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using pairLinearBudgetConst_nonneg hP4
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using pairPointwiseBudgetConst_nonneg hP4
  have hG_nonneg : 0 ≤ Gβ := by
    dsimp [Gβ, β]
    exact inv_nonneg.mpr
      (geometricDiscount_pos (by simpa using section54VarianceBeta_pos hP4)).le
  have hC_ge_G : Gβ ≤ C := by
    dsimp [C, Gβ, weightedRefinedBudgetConst]
    have hML_nonneg : 0 ≤ M * L := mul_nonneg hM_nonneg hL_nonneg
    linarith
  have hC_ge_2L : 2 * L ≤ C := by
    dsimp [C, L, Gβ, weightedRefinedBudgetConst]
    have hML_nonneg : 0 ≤ M * L := mul_nonneg hM_nonneg hL_nonneg
    linarith
  have hC_ge_2ML : 2 * M * L ≤ C := by
    dsimp [C, M, L, Gβ, weightedRefinedBudgetConst]
    linarith
  have hbudgetTerm :
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            refinedVarianceBasicBudget hP4 delta j) ≤
        ∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (delta + 2 * pairProbeRefinedDescendantAverageK hP4 delta j +
              2 * pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (refinedVarianceBasicBudget_le_pairBudget hP4 hδ_nonneg j)
      (varianceWeight_nonneg β m j)
  have hconst :
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * delta) ≤ Gβ * delta := by
    calc
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * delta) =
          (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) * delta := by
          rw [Finset.sum_mul]
      _ ≤ Gβ * delta := by
          exact mul_le_mul_of_nonneg_right
            (by
              simpa [β, Gβ] using
                sum_Icc_varianceWeight_le_inv_geometricDiscount
                  (section54VarianceBeta_pos hP4) m)
            hδ_nonneg
  have hlinear :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          pairProbeRefinedDescendantAverageK hP4 delta j) ≤
        L * θ * D := by
    simpa [β, L, θ, D] using
      sum_Icc_varianceWeight_mul_pairProbeRefinedK_le hP4 hdelta_le_half m
  have hsquare :
      (∑ j ∈ Finset.Icc 1 m,
        varianceWeight β m j *
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) ≤
        M * L * θ ^ (2 : ℕ) * D := by
    simpa [β, M, L, θ, D, mul_assoc] using
      sum_Icc_varianceWeight_mul_pairProbeRefinedK_sq_le
        hP4 hδ_nonneg hdelta_le_half m
  have hsplit :
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (delta + 2 * pairProbeRefinedDescendantAverageK hP4 delta j +
              2 * pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ))) =
        2 * (∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              pairProbeRefinedDescendantAverageK hP4 delta j) +
          2 * (∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) +
          (∑ j ∈ Finset.Icc 1 m, delta * varianceWeight β m j) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            (delta + 2 * pairProbeRefinedDescendantAverageK hP4 delta j +
              2 * pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ))) =
          ∑ j ∈ Finset.Icc 1 m,
            (2 * (varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j) +
              2 * (varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) +
              delta * varianceWeight β m j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ =
          2 * (∑ j ∈ Finset.Icc 1 m,
              varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j) +
            2 * (∑ j ∈ Finset.Icc 1 m,
              varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) +
            (∑ j ∈ Finset.Icc 1 m, delta * varianceWeight β m j) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hconst' :
      (∑ j ∈ Finset.Icc 1 m, delta * varianceWeight β m j) ≤ Gβ * delta := by
    simpa [mul_comm] using hconst
  have hraw :
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            refinedVarianceBasicBudget hP4 delta j) ≤
        Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) := by
    calc
      (∑ j ∈ Finset.Icc 1 m,
          varianceWeight β m j *
            refinedVarianceBasicBudget hP4 delta j) ≤
          ∑ j ∈ Finset.Icc 1 m,
            varianceWeight β m j *
              (delta + 2 * pairProbeRefinedDescendantAverageK hP4 delta j +
                2 * pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) := hbudgetTerm
      _ =
          2 * (∑ j ∈ Finset.Icc 1 m,
              varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j) +
            2 * (∑ j ∈ Finset.Icc 1 m,
              varianceWeight β m j *
                pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) +
            (∑ j ∈ Finset.Icc 1 m, delta * varianceWeight β m j) := hsplit
      _ ≤ Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) := by
          linarith
  have hfinal :
      Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D) ≤
        C * (delta + D * (θ + θ ^ (2 : ℕ))) := by
    have h1 : Gβ * delta ≤ C * delta :=
      mul_le_mul_of_nonneg_right hC_ge_G hδ_nonneg
    have h2 : 2 * (L * θ * D) ≤ C * (D * θ) := by
      have hcoef : 2 * L ≤ C := hC_ge_2L
      have hDθ : 0 ≤ D * θ := mul_nonneg hD hθ
      have hmul := mul_le_mul_of_nonneg_right hcoef hDθ
      calc
        2 * (L * θ * D) = (2 * L) * (D * θ) := by ring
        _ ≤ C * (D * θ) := hmul
    have h3 : 2 * (M * L * θ ^ (2 : ℕ) * D) ≤ C * (D * θ ^ (2 : ℕ)) := by
      have hcoef : 2 * M * L ≤ C := hC_ge_2ML
      have hDθ2 : 0 ≤ D * θ ^ (2 : ℕ) := mul_nonneg hD (sq_nonneg θ)
      have hmul := mul_le_mul_of_nonneg_right hcoef hDθ2
      calc
        2 * (M * L * θ ^ (2 : ℕ) * D) = (2 * M * L) * (D * θ ^ (2 : ℕ)) := by
          ring
        _ ≤ C * (D * θ ^ (2 : ℕ)) := hmul
    calc
      Gβ * delta + 2 * (L * θ * D) + 2 * (M * L * θ ^ (2 : ℕ) * D)
          ≤ C * delta + C * (D * θ) + C * (D * θ ^ (2 : ℕ)) := by
            exact add_le_add (add_le_add h1 h2) h3
      _ = C * (delta + D * (θ + θ ^ (2 : ℕ))) := by ring
  exact hraw.trans hfinal

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
