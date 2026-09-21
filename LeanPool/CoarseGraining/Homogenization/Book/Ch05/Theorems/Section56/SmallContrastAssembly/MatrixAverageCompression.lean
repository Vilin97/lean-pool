/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAverageEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastJBound.Preliminaries

/-! # Matrix Average Compression -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section54.VarianceBoundGoodScale

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P 0 hP4 := by
  simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

private theorem rosenthalDescendantsAtScaleLpConst_nonneg
    (d : ℕ) (k : ℤ) (p : ℕ) :
    0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d k p := by
  unfold Ch04.rosenthalDescendantsAtScaleLpConst
  positivity

private theorem rosenthalDescendantsAtScaleSqrtConst_nonneg
    (d : ℕ) (k : ℤ) (p : ℕ) :
    0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d k p := by
  unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
    IndependentSums.rosenthalBennettIntegralConst
  positivity

private theorem pairPointwiseBudgetConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ pairPointwiseBudgetConst hP4 := by
  have hLp := rosenthalDescendantsAtScaleLpConst_nonneg d 0 hP4.xi
  have hSqrt := rosenthalDescendantsAtScaleSqrtConst_nonneg d 0 hP4.xi
  unfold pairPointwiseBudgetConst
  positivity

private theorem scaleColorPeriod_natCast_eq_zero (n : ℕ) :
    scaleColorPeriod (n : ℤ) = scaleColorPeriod 0 := by
  have hle_one : (3 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
    exact zpow_le_one_of_nonpos₀
      (show (1 : ℝ) ≤ 3 by norm_num)
      (by exact neg_nonpos.mpr (Int.natCast_nonneg n))
  have hceil :
      Nat.ceil ((3 : ℝ) ^ (-(n : ℤ))) = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
    constructor
    · norm_num
    · simpa using hle_one
  unfold scaleColorPeriod
  rw [hceil]
  norm_num

private theorem rosenthalDescendantsAtScaleLpConst_natCast_eq_zero
    (d p n : ℕ) :
    Ch04.rosenthalDescendantsAtScaleLpConst d (n : ℤ) p =
      Ch04.rosenthalDescendantsAtScaleLpConst d 0 p := by
  simp [Ch04.rosenthalDescendantsAtScaleLpConst, scaleColorPeriod_natCast_eq_zero n]

private theorem rosenthalDescendantsAtScaleSqrtConst_natCast_eq_zero
    (d p n : ℕ) :
    Ch04.rosenthalDescendantsAtScaleSqrtConst d (n : ℤ) p =
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 p := by
  simp [Ch04.rosenthalDescendantsAtScaleSqrtConst, scaleColorPeriod_natCast_eq_zero n]

private theorem smallContrast_goodScale_upper_delta_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (m : ℕ) :
    hP.barSigmaAtScale hStruct 0 ≤
      (1 + (1 : ℝ)) * hP.barSigmaAtScale hStruct (m : ℤ) := by
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hc0_pos : 0 < c0 := by
    simpa [c0] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 0
  have hchain := Section54.Pigeonhole.scalarChain_of_P4
    hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have hc0_le_cm : c0 ≤ cm := by simpa [c0, cm] using hchain.1
  have hcm_le_bm : cm ≤ bm := by
    simpa [bm, cm] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hθ0_two : b0 * c0⁻¹ ≤ 2 := by
    have hθ0 :
        thetaAtScale hP hStruct (0 : ℤ) ≤ 2 :=
      (thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
        hP hStruct hP4).trans hsmall
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, c0] using hθ0
  have hb0_le_two_c0 : b0 ≤ 2 * c0 := by
    have hmul := mul_le_mul_of_nonneg_right hθ0_two hc0_pos.le
    have hcancel : b0 * c0⁻¹ * c0 = b0 := by field_simp [ne_of_gt hc0_pos]
    simpa [hcancel] using hmul
  calc
    hP.barSigmaAtScale hStruct 0 = b0 := rfl
    _ ≤ 2 * c0 := hb0_le_two_c0
    _ ≤ 2 * bm := mul_le_mul_of_nonneg_left (hc0_le_cm.trans hcm_le_bm) (by norm_num)
    _ = (1 + (1 : ℝ)) * hP.barSigmaAtScale hStruct (m : ℤ) := by ring

private theorem smallContrast_goodScale_lower_delta_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (m : ℕ) :
    (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
      (1 + (1 : ℝ)) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hc0_pos : 0 < c0 := by
    simpa [c0] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 0
  have hcm_pos : 0 < cm := by
    simpa [cm] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hchain := Section54.Pigeonhole.scalarChain_of_P4
    hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have hbm_le_b0 : bm ≤ b0 := by simpa [bm, b0] using hchain.2.2
  have hcm_le_bm : cm ≤ bm := by
    simpa [bm, cm] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hθ0_two : b0 * c0⁻¹ ≤ 2 := by
    have hθ0 :
        thetaAtScale hP hStruct (0 : ℤ) ≤ 2 :=
      (thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
        hP hStruct hP4).trans hsmall
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, c0] using hθ0
  have hb0_le_two_c0 : b0 ≤ 2 * c0 := by
    have hmul := mul_le_mul_of_nonneg_right hθ0_two hc0_pos.le
    have hcancel : b0 * c0⁻¹ * c0 = b0 := by field_simp [ne_of_gt hc0_pos]
    simpa [hcancel] using hmul
  have hcm_le_two_c0 : cm ≤ 2 * c0 :=
    hcm_le_bm.trans (hbm_le_b0.trans hb0_le_two_c0)
  have hinv_le : c0⁻¹ ≤ 2 * cm⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hcm_le_two_c0
      (mul_nonneg (inv_pos.mpr hc0_pos).le (inv_pos.mpr hcm_pos).le)
    have hleft : cm * (c0⁻¹ * cm⁻¹) = c0⁻¹ := by
      field_simp [ne_of_gt hcm_pos]
    have hright : (2 * c0) * (c0⁻¹ * cm⁻¹) = 2 * cm⁻¹ := by
      field_simp [ne_of_gt hc0_pos]
    simpa [hleft, hright] using hmul
  calc
    (hP.barSigmaStarAtScale hStruct 0)⁻¹ = c0⁻¹ := rfl
    _ ≤ 2 * cm⁻¹ := hinv_le
    _ = (1 + (1 : ℝ)) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by ring

private theorem pairProbeRefinedDescendantAverageK_le_pointwiseConst_delta_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (j : ℕ) :
    pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j ≤
      pairPointwiseBudgetConst hP4 * widetildeThetaAtScale P 0 hP4 := by
  let A : ℝ :=
    Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ))
  have hgeo := pairProbeRefinedDescendantAverageK_eq_geometric hP4 (1 : ℝ) j
  have hpair_eq :
      pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j =
        16 * widetildeThetaAtScale P 0 hP4 * A := by
    have hgeo' :
        pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j =
          8 * ((1 + (1 : ℝ)) * widetildeThetaAtScale P 0 hP4) * A := by
      simpa [A, widetildeThetaAtScale, lpVarianceDecay, sqrtVarianceDecay,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgeo
    calc
      pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j =
          8 * ((1 + (1 : ℝ)) * widetildeThetaAtScale P 0 hP4) * A := hgeo'
      _ = 16 * widetildeThetaAtScale P 0 hP4 * A := by ring
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi :=
    rosenthalDescendantsAtScaleLpConst_nonneg d 0 hP4.xi
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi :=
    rosenthalDescendantsAtScaleSqrtConst_nonneg d 0 hP4.xi
  have hLp_decay :
      Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by
        have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by
          exact_mod_cast hP4.two_le_xi
        have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
        have hdiv_le : (d : ℝ) / (hP4.xi : ℝ) ≤ (d : ℝ) / 2 := by
          exact div_le_div_of_nonneg_left hd_nonneg (by norm_num) hxi_two
        have hγ : 0 ≤ lpVarianceDecay d hP4 := by
          dsimp [lpVarianceDecay]
          linarith
        have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hj)
  have hSqrt_decay :
      Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by
        have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
        have hγ : 0 ≤ sqrtVarianceDecay d := by
          dsimp [sqrtVarianceDecay]
          positivity
        have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hj)
  have hinside :
      A ≤
        Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    have hLp_part :
        Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(lpVarianceDecay d hP4) * (j : ℝ)) ≤
          Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
      simpa using mul_le_mul_of_nonneg_left hLp_decay hLp_nonneg
    have hSqrt_part :
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.rpow (3 : ℝ) (-(sqrtVarianceDecay d) * (j : ℝ)) ≤
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
      simpa using mul_le_mul_of_nonneg_left hSqrt_decay hSqrt_nonneg
    dsimp [A]
    exact add_le_add hLp_part hSqrt_part
  have htheta : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_zero_nonneg hP4
  calc
    pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j =
        16 * widetildeThetaAtScale P 0 hP4 * A := hpair_eq
    _ ≤
        16 * widetildeThetaAtScale P 0 hP4 *
          (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi +
            Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi) :=
        mul_le_mul_of_nonneg_left hinside (mul_nonneg (by norm_num) htheta)
    _ = pairPointwiseBudgetConst hP4 * widetildeThetaAtScale P 0 hP4 := by
        simp [pairPointwiseBudgetConst]
        ring

noncomputable def refinedVarianceBasicBudgetSmallContrastConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  1 + 4 * pairPointwiseBudgetConst hP4 +
    8 * pairPointwiseBudgetConst hP4 ^ (2 : ℕ)

private theorem refinedVarianceBasicBudgetSmallContrastConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ refinedVarianceBasicBudgetSmallContrastConst hP4 := by
  have hM := pairPointwiseBudgetConst_nonneg hP4
  unfold refinedVarianceBasicBudgetSmallContrastConst
  exact add_nonneg
    (add_nonneg zero_le_one (mul_nonneg (by norm_num) hM))
    (mul_nonneg (by norm_num) (sq_nonneg (pairPointwiseBudgetConst hP4)))

private theorem refinedVarianceBasicBudget_one_le_smallContrastConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (j : ℕ) :
    refinedVarianceBasicBudget hP4 (1 : ℝ) j ≤
      refinedVarianceBasicBudgetSmallContrastConst hP4 := by
  let K := pairProbeRefinedDescendantAverageK hP4 (1 : ℝ) j
  let M := pairPointwiseBudgetConst hP4
  let θ := widetildeThetaAtScale P 0 hP4
  have hK_nonneg : 0 ≤ K := by
    simpa [K] using pairProbeRefinedDescendantAverageK_nonneg hP4 (by norm_num) j
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using pairPointwiseBudgetConst_nonneg hP4
  have hθ_nonneg : 0 ≤ θ := by
    simpa [θ] using widetildeThetaAtScale_zero_nonneg hP4
  have hK_le_Mθ : K ≤ M * θ := by
    simpa [K, M, θ] using
      pairProbeRefinedDescendantAverageK_le_pointwiseConst_delta_one hP4 j
  have hK_le_twoM : K ≤ 2 * M := by
    calc
      K ≤ M * θ := hK_le_Mθ
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left (by simpa [θ] using hsmall) hM_nonneg
      _ = 2 * M := by ring
  have hK_sq_le : K ^ (2 : ℕ) ≤ (2 * M) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hK_nonneg hK_le_twoM 2
  have hbasic :=
    refinedVarianceBasicBudget_le_pairBudget hP4 (by norm_num : (0 : ℝ) ≤ 1) j
  calc
    refinedVarianceBasicBudget hP4 (1 : ℝ) j ≤
        1 + 2 * K + 2 * K ^ (2 : ℕ) := by simpa [K] using hbasic
    _ ≤ 1 + 4 * M + 8 * M ^ (2 : ℕ) := by
        have hlinear : 2 * K ≤ 4 * M := by
          calc
            2 * K ≤ 2 * (2 * M) :=
              mul_le_mul_of_nonneg_left hK_le_twoM (by norm_num)
            _ = 4 * M := by ring
        have hquad : 2 * K ^ (2 : ℕ) ≤ 8 * M ^ (2 : ℕ) := by
          calc
            2 * K ^ (2 : ℕ) ≤ 2 * (2 * M) ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_left hK_sq_le (by norm_num)
            _ = 8 * M ^ (2 : ℕ) := by ring
        exact add_le_add (add_le_add le_rfl hlinear) hquad
    _ = refinedVarianceBasicBudgetSmallContrastConst hP4 := by
        simp [refinedVarianceBasicBudgetSmallContrastConst, M]

private theorem centeredOriginNormalizedQuadratic_sq_integral_le_smallContrastConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (child : ℕ) (q : FullBlockVec d) :
    ∫ a,
        |Ch04.restrictionCenteredOriginObservable P (child : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q) a| ^
          (2 : ℕ) ∂P ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 *
        (dotProduct q q) ^ (2 : ℕ) := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q
  let F : RegCoeffField d → ℝ := fun a =>
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
      hP hStruct (child : ℤ) (originCube d (child : ℤ)) a
  let Dq : ℝ := (dotProduct q q) ^ (2 : ℕ)
  have hleft_int :
      Integrable
        (fun a : RegCoeffField d =>
          |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ)) P := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_centeredOrigin_sq_integrable_at_self
        hP hStruct hP4 child q
  have hF_int : Integrable F P := by
    simpa [F] using
      integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
        hP hStruct hP4 (child : ℤ) child
  have hright_int : Integrable (fun a : RegCoeffField d => F a * Dq) P :=
    hF_int.mul_const Dq
  have hpoint :
      (fun a : RegCoeffField d =>
          |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ))
        ≤ᵐ[P] fun a => F a * Dq := by
    filter_upwards with a
    have hmean :
        (∫ b,
          fullBlockNormalizedQuadraticObservable hP hStruct (child : ℤ) q
            (cubeSet (originCube d (child : ℤ))) b.toFun ∂P) =
          dotProduct q q :=
      integral_origin_fullBlockNormalizedQuadraticObservable_self_eq_dotProduct
        hP hStruct hP4 child q
    have hcenter :
        Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a =
          fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (child : ℤ)
              (cubeSet (originCube d (child : ℤ))) a) q := by
      simp only [Ch04.restrictionCenteredOriginObservable, X,
        fullBlockNormalizedQuadraticObservableR]
      rw [hmean]
      exact
        fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
          hP hStruct hP4 child q (cubeSet (originCube d (child : ℤ))) a
    have hquad :=
      fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq
        (fullBlockNormalizedFluctuationMatrix hP hStruct (child : ℤ)
          (cubeSet (originCube d (child : ℤ))) a) q
    simpa [X, F, Dq, hcenter,
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
      fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq] using hquad
  have hmono :
      ∫ a, |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ) ∂P ≤
        ∫ a, F a * Dq ∂P :=
    integral_mono_ae hleft_int hright_int hpoint
  have hgood_upper :=
    smallContrast_goodScale_upper_delta_one hP hStruct hP4 hsmall child
  have hgood_lower :=
    smallContrast_goodScale_lower_delta_one hP hStruct hP4 hsmall child
  have hOp :
      ∫ a, F a ∂P ≤
        refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 := by
    have hrefined :
        ∫ a, F a ∂P ≤ refinedMatrixVarianceScaleBound hP4 (1 : ℝ) child := by
      simpa [F] using
        fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_refinedMatrixVarianceScaleBound
          hP hStruct hP4 (by norm_num : (0 : ℝ) ≤ 1) child child
          (le_rfl : child ≤ child) hgood_upper hgood_lower
    have hbasic :
        refinedMatrixVarianceScaleBound hP4 (1 : ℝ) child ≤
          refinedMatrixBudgetConst d * refinedVarianceBasicBudget hP4 (1 : ℝ) child :=
      refinedMatrixVarianceScaleBound_le_basicBudget
        hP4 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) child
    have hconst :=
      refinedVarianceBasicBudget_one_le_smallContrastConst hP4 hsmall child
    exact hrefined.trans
      (hbasic.trans
        (mul_le_mul_of_nonneg_left hconst (by
          unfold refinedMatrixBudgetConst
          positivity)))
  have hDq_nonneg : 0 ≤ Dq := by
    dsimp [Dq]
    exact sq_nonneg (dotProduct q q)
  calc
    ∫ a,
        |Ch04.restrictionCenteredOriginObservable P (child : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q) a| ^
          (2 : ℕ) ∂P =
        ∫ a, |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^
          (2 : ℕ) ∂P := rfl
    _ ≤ ∫ a, F a * Dq ∂P := hmono
    _ = (∫ a, F a ∂P) * Dq := by rw [integral_mul_const]
    _ ≤ (refinedMatrixBudgetConst d *
          refinedVarianceBasicBudgetSmallContrastConst hP4) * Dq :=
        mul_le_mul_of_nonneg_right hOp hDq_nonneg
    _ = refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 *
          (dotProduct q q) ^ (2 : ℕ) := by
        simp [Dq, mul_assoc]

private noncomputable def normalizedQuadraticProbeAverageRootSqConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (q : FullBlockVec d) : ℝ :=
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2) ^ (2 : ℕ) *
    (refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 *
      (dotProduct q q) ^ (2 : ℕ))

noncomputable def normalizedQuadraticProbeAverageUniformRootSqConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2) ^ (2 : ℕ) *
    (refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 * 16)

noncomputable def normalizedMatrixAverageGeometricConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * 9 *
    normalizedQuadraticProbeAverageUniformRootSqConst hP4

private theorem refinedMatrixBudgetConst_nonneg (d : ℕ) :
    0 ≤ refinedMatrixBudgetConst d := by
  unfold refinedMatrixBudgetConst
  positivity

theorem normalizedQuadraticProbeAverageUniformRootSqConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ normalizedQuadraticProbeAverageUniformRootSqConst hP4 := by
  have hbudget : 0 ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 := by
    exact mul_nonneg (refinedMatrixBudgetConst_nonneg d)
      (refinedVarianceBasicBudgetSmallContrastConst_nonneg hP4)
  unfold normalizedQuadraticProbeAverageUniformRootSqConst
  exact mul_nonneg
    (sq_nonneg
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2))
    (mul_nonneg hbudget (by norm_num))

private theorem normalizedQuadraticProbeAverageRootSqConst_le_uniform_coordinate
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (α : BlockCoord d) :
    normalizedQuadraticProbeAverageRootSqConst hP4 (fullBlockCoordinateProbe α) ≤
      normalizedQuadraticProbeAverageUniformRootSqConst hP4 := by
  have hbudget : 0 ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 := by
    exact mul_nonneg (refinedMatrixBudgetConst_nonneg d)
      (refinedVarianceBasicBudgetSmallContrastConst_nonneg hP4)
  have hdot :
      (dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ≤
        (16 : ℝ) := by
    rw [dotProduct_coordinateProbe_self]
    norm_num
  unfold normalizedQuadraticProbeAverageRootSqConst
    normalizedQuadraticProbeAverageUniformRootSqConst
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hdot hbudget)
    (sq_nonneg
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2))

private theorem normalizedQuadraticProbeAverageRootSqConst_le_uniform_plus
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (α β : BlockCoord d) :
    normalizedQuadraticProbeAverageRootSqConst hP4 (fullBlockPlusProbe α β) ≤
      normalizedQuadraticProbeAverageUniformRootSqConst hP4 := by
  have hbudget : 0 ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 := by
    exact mul_nonneg (refinedMatrixBudgetConst_nonneg d)
      (refinedVarianceBasicBudgetSmallContrastConst_nonneg hP4)
  have hdot_nonneg :
      0 ≤ dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) :=
    dotProduct_self_nonneg (fullBlockPlusProbe α β)
  have hdot_le :
      dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) ≤ 4 :=
    dotProduct_plusProbe_self_le_four α β
  have hdot_sq :
      (dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ≤
        (16 : ℝ) := by
    have h := pow_le_pow_left₀ hdot_nonneg hdot_le 2
    norm_num at h ⊢
    exact h
  unfold normalizedQuadraticProbeAverageRootSqConst
    normalizedQuadraticProbeAverageUniformRootSqConst
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hdot_sq hbudget)
    (sq_nonneg
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2))

private theorem normalizedQuadraticProbeAverageRootSqConst_le_uniform_minus
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (α β : BlockCoord d) :
    normalizedQuadraticProbeAverageRootSqConst hP4 (fullBlockMinusProbe α β) ≤
      normalizedQuadraticProbeAverageUniformRootSqConst hP4 := by
  have hbudget : 0 ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 := by
    exact mul_nonneg (refinedMatrixBudgetConst_nonneg d)
      (refinedVarianceBasicBudgetSmallContrastConst_nonneg hP4)
  have hdot_nonneg :
      0 ≤ dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) :=
    dotProduct_self_nonneg (fullBlockMinusProbe α β)
  have hdot_le :
      dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) ≤ 4 :=
    dotProduct_minusProbe_self_le_four α β
  have hdot_sq :
      (dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ≤
        (16 : ℝ) := by
    have h := pow_le_pow_left₀ hdot_nonneg hdot_le 2
    norm_num at h ⊢
    exact h
  unfold normalizedQuadraticProbeAverageRootSqConst
    normalizedQuadraticProbeAverageUniformRootSqConst
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hdot_sq hbudget)
    (sq_nonneg
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2))

private theorem normalizedQuadraticProbeAverageRootBound_sq_le_card_inv_mul_smallContrastConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {child parent : ℕ} (hchild_parent : child ≤ parent) (q : FullBlockVec d) :
    (normalizedQuadraticProbeAverageRootBound hP hStruct child parent q) ^ (2 : ℕ) ≤
      (((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)⁻¹) *
        normalizedQuadraticProbeAverageRootSqConst hP4 q := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q
  let I : ℝ :=
    ∫ a, |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ) ∂P
  let K : ℝ := I ^ (1 / (2 : ℝ))
  let N : ℝ := ((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)
  let L : ℝ := Ch04.rosenthalDescendantsAtScaleLpConst d 0 2
  let S : ℝ := Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2
  let V : ℝ :=
    refinedMatrixBudgetConst d * refinedVarianceBasicBudgetSmallContrastConst hP4 *
      (dotProduct q q) ^ (2 : ℕ)
  have hscale_le : (child : ℤ) ≤ (parent : ℤ) := by exact_mod_cast hchild_parent
  have hcard_formula :=
    Section52.section52_descendantsAtScale_originCube_large_card
      d parent (n := (child : ℤ)) hscale_le
  have hN_pos : 0 < N := by
    dsimp [N]
    rw [hcard_formula]
    exact_mod_cast
      (pow_pos (pow_pos (by norm_num : 0 < 3) d)
        (Int.toNat ((parent : ℤ) - (child : ℤ))))
  have hN_nonneg : 0 ≤ N := hN_pos.le
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hI_nonneg : 0 ≤ I := by
    dsimp [I, X]
    exact integral_nonneg fun a => pow_nonneg (abs_nonneg _) (2 : ℕ)
  have hK_sq : K ^ (2 : ℕ) = I := by
    dsimp [K]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hI_nonneg]
  have hI_le : I ≤ V := by
    dsimp [I, X, V]
    exact centeredOriginNormalizedQuadratic_sq_integral_le_smallContrastConst
      hP hStruct hP4 hsmall child q
  have hK_sq_le : K ^ (2 : ℕ) ≤ V := by
    rw [hK_sq]
    exact hI_le
  have hroot_eq :
      normalizedQuadraticProbeAverageRootBound hP hStruct child parent q =
        N⁻¹ * ((L + S) * Real.sqrt N * K) := by
    rw [normalizedQuadraticProbeAverageRootBound]
    rw [rosenthalDescendantsAtScaleLpConst_natCast_eq_zero d 2 child,
      rosenthalDescendantsAtScaleSqrtConst_natCast_eq_zero d 2 child]
    rw [← Real.sqrt_eq_rpow N]
    simp [X, I, K, N, L, S, mul_comm, mul_assoc, add_mul]
    ring_nf
    left
    trivial
  have hroot_sq_eq :
      (normalizedQuadraticProbeAverageRootBound hP hStruct child parent q) ^ (2 : ℕ) =
        N⁻¹ * ((L + S) ^ (2 : ℕ) * K ^ (2 : ℕ)) := by
    rw [hroot_eq]
    calc
      (N⁻¹ * ((L + S) * Real.sqrt N * K)) ^ (2 : ℕ)
          = N⁻¹ ^ (2 : ℕ) *
              ((L + S) ^ (2 : ℕ) * (Real.sqrt N) ^ (2 : ℕ) * K ^ (2 : ℕ)) := by
            ring
      _ = N⁻¹ ^ (2 : ℕ) *
              ((L + S) ^ (2 : ℕ) * N * K ^ (2 : ℕ)) := by
            rw [Real.sq_sqrt hN_nonneg]
      _ = N⁻¹ * ((L + S) ^ (2 : ℕ) * K ^ (2 : ℕ)) := by
            field_simp [hN_ne]
  have hfactor_nonneg : 0 ≤ N⁻¹ * (L + S) ^ (2 : ℕ) := by
    exact mul_nonneg (inv_nonneg.mpr hN_nonneg) (sq_nonneg (L + S))
  calc
    (normalizedQuadraticProbeAverageRootBound hP hStruct child parent q) ^ (2 : ℕ)
        = N⁻¹ * ((L + S) ^ (2 : ℕ) * K ^ (2 : ℕ)) := hroot_sq_eq
    _ = (N⁻¹ * (L + S) ^ (2 : ℕ)) * K ^ (2 : ℕ) := by ring
    _ ≤ (N⁻¹ * (L + S) ^ (2 : ℕ)) * V :=
        mul_le_mul_of_nonneg_left hK_sq_le hfactor_nonneg
    _ = N⁻¹ * normalizedQuadraticProbeAverageRootSqConst hP4 q := by
        simp [normalizedQuadraticProbeAverageRootSqConst, V, L, S, mul_comm,
          mul_left_comm, mul_assoc]

private theorem normalizedMatrixAverageProbeRootBudget_le_of_probe_sq_bound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (child parent : ℕ) (B : ℝ)
    (hcoord :
      ∀ α : BlockCoord d,
        (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
          (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ≤ B)
    (hplus :
      ∀ α β : BlockCoord d,
        (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
          (fullBlockPlusProbe α β)) ^ (2 : ℕ) ≤ B)
    (hminus :
      ∀ α β : BlockCoord d,
        (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
          (fullBlockMinusProbe α β)) ^ (2 : ℕ) ≤ B) :
    normalizedMatrixAverageProbeRootBudget hP hStruct child parent ≤
      ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * 9 * B := by
  classical
  let c : ℝ := Fintype.card (BlockCoord d)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  unfold normalizedMatrixAverageProbeRootBudget
  calc
    ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
      ((Fintype.card (BlockCoord d) : ℝ) *
        ∑ α : BlockCoord d,
          (Fintype.card (BlockCoord d) : ℝ) *
            ∑ β : BlockCoord d,
              3 *
                ((normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                      (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                  (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                      (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                  (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                      (fullBlockMinusProbe α β)) ^ (2 : ℕ))) ≤
        ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          ((Fintype.card (BlockCoord d) : ℝ) *
            ∑ _α : BlockCoord d,
              (Fintype.card (BlockCoord d) : ℝ) *
                ∑ _β : BlockCoord d, 9 * B) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine Finset.sum_le_sum ?_
        intro α _hα
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine Finset.sum_le_sum ?_
        intro β _hβ
        calc
          3 *
              ((normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockMinusProbe α β)) ^ (2 : ℕ)) ≤
              3 * (B + B + B) := by
                exact mul_le_mul_of_nonneg_left
                  (add_le_add (add_le_add (hcoord α) (hplus α β)) (hminus α β))
                  (by norm_num)
          _ = 9 * B := by ring
    _ = ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * 9 * B := by
        change c ^ (2 : ℕ) *
            (c * ∑ _α : BlockCoord d,
              c * ∑ _β : BlockCoord d, 9 * B) =
          c ^ (6 : ℕ) * 9 * B
        simp [Finset.sum_const, c]
        ring

theorem normalizedMatrixAverageProbeRootBudget_le_card_inv_mul_smallContrastConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {child parent : ℕ} (hchild_parent : child ≤ parent) :
    normalizedMatrixAverageProbeRootBudget hP hStruct child parent ≤
      (((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)⁻¹) *
        normalizedMatrixAverageGeometricConst hP4 := by
  let Ninv : ℝ :=
    (((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)⁻¹)
  let R : ℝ := normalizedQuadraticProbeAverageUniformRootSqConst hP4
  have hNinv_nonneg : 0 ≤ Ninv := by
    dsimp [Ninv]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcoord : ∀ α : BlockCoord d,
      (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
        (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ≤ Ninv * R := by
    intro α
    have hroot :=
      normalizedQuadraticProbeAverageRootBound_sq_le_card_inv_mul_smallContrastConst
        hP hStruct hP4 hsmall hchild_parent (fullBlockCoordinateProbe α)
    exact hroot.trans
      (mul_le_mul_of_nonneg_left
        (by
          simpa [R] using
            normalizedQuadraticProbeAverageRootSqConst_le_uniform_coordinate hP4 α)
        hNinv_nonneg)
  have hplus : ∀ α β : BlockCoord d,
      (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
        (fullBlockPlusProbe α β)) ^ (2 : ℕ) ≤ Ninv * R := by
    intro α β
    have hroot :=
      normalizedQuadraticProbeAverageRootBound_sq_le_card_inv_mul_smallContrastConst
        hP hStruct hP4 hsmall hchild_parent (fullBlockPlusProbe α β)
    exact hroot.trans
      (mul_le_mul_of_nonneg_left
        (by
          simpa [R] using
            normalizedQuadraticProbeAverageRootSqConst_le_uniform_plus hP4 α β)
        hNinv_nonneg)
  have hminus : ∀ α β : BlockCoord d,
      (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
        (fullBlockMinusProbe α β)) ^ (2 : ℕ) ≤ Ninv * R := by
    intro α β
    have hroot :=
      normalizedQuadraticProbeAverageRootBound_sq_le_card_inv_mul_smallContrastConst
        hP hStruct hP4 hsmall hchild_parent (fullBlockMinusProbe α β)
    exact hroot.trans
      (mul_le_mul_of_nonneg_left
        (by
          simpa [R] using
            normalizedQuadraticProbeAverageRootSqConst_le_uniform_minus hP4 α β)
        hNinv_nonneg)
  have hbudget :=
    normalizedMatrixAverageProbeRootBudget_le_of_probe_sq_bound
      hP hStruct child parent (Ninv * R) hcoord hplus hminus
  calc
    normalizedMatrixAverageProbeRootBudget hP hStruct child parent ≤
        ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * 9 * (Ninv * R) := hbudget
    _ = Ninv * normalizedMatrixAverageGeometricConst hP4 := by
        simp [normalizedMatrixAverageGeometricConst, Ninv, R]
        ring

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
