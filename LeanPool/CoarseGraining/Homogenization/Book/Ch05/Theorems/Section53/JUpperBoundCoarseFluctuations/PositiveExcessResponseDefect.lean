/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.EllipticityMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ResponseMomentIntegrability

/-! # Positive Excess Response Defect -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

/-!
# Positive-excess response-defect estimates

This proof-internal file contains the positive-excess estimates whose response
side is a child-response average or the weighted response-defect square sum.
The Holder/P4 source estimates remain in `EllipticityMoments.lean`.
-/

noncomputable section

private theorem ellipticityPositiveExcessContribution_expectation_le_of_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d)
    (hLowerPowInt :
      let β := section53CoarseFluctuationBeta hP4
      let rLower := hP4.sLower + β
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField
                (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P)
    (hUpperPowInt :
      let β := section53CoarseFluctuationBeta hP4
      let rUpper := hP4.sUpper + β
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField
                (originCube d (m : ℤ)) rUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hResponsePowInt :
      let ζ := section53CoarseFluctuationZeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      Integrable
        (fun a : RegCoeffField d =>
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ) P) :
    ∃ C : ℝ, 0 ≤ C ∧
      let β := section53CoarseFluctuationBeta hP4
      let rLower := hP4.sLower + β
      let rUpper := hP4.sUpper + β
      let σ := sigmaHatAtScale hP hStruct (m : ℤ)
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let J : RegCoeffField d → ℝ :=
        fun a => Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a
      σ *
          (∫ a,
            (max
                ((Ch04.lambdaSqCoeffField
                    (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
                  (hP.barSigmaStarAtScale hStruct 0)⁻¹)
                0) * J a ∂P) +
        σ⁻¹ *
          (∫ a,
            (max
                (Ch04.LambdaSqCoeffField
                    (originCube d (m : ℤ)) rUpper (.finite 1) a -
                  hP.barSigmaAtScale hStruct 0)
                0) * J a ∂P)
        ≤
          C * (hP4.xi : ℝ) *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  let β := section53CoarseFluctuationBeta hP4
  let ζ := section53CoarseFluctuationZeta hP4
  let rLower := hP4.sLower + β
  let rUpper := hP4.sUpper + β
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let J : RegCoeffField d → ℝ :=
    fun a => Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField
            (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField
            (originCube d (m : ℤ)) rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let responseMoment :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  rcases Section52.multiscaleEllipticityMomentBounds_homogenizationScale
      (d := d) with ⟨C52, hC52_nonneg, hC52_bound⟩
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hrLower_gt : hP4.sLower < rLower := by
    dsimp [rLower, β]
    linarith
  have hrUpper_gt : hP4.sUpper < rUpper := by
    dsimp [rUpper, β]
    linarith
  have hrLower_lt_one : rLower < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [rLower, β]
    nlinarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hrUpper_lt_one : rUpper < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [rUpper, β]
    nlinarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have hBounds := hC52_bound hP hStruct hP4 rUpper rLower m
    hrUpper_gt hrUpper_lt_one hrLower_gt hrLower_lt_one
  let upperCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 hP4.sUpper rUpper m
  let lowerCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 hP4.sLower rLower m
  let upperLoss : ℝ :=
    section52MomentLossCoeff d hP4.xi hP4.sUpper rUpper
  let lowerLoss : ℝ :=
    section52MomentLossCoeff d hP4.xi hP4.sLower rLower
  let decay : ℝ := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let C0 : ℝ := max (C52 * lowerLoss) (C52 * upperLoss)
  have hUpperLoss_nonneg : 0 ≤ upperLoss := by
    simpa [upperLoss, rUpper] using
      section52MomentLossCoeff_nonneg_at_shift hP4
        hP4.sUpper_pos hrUpper_gt hrUpper_lt_one
  have hLowerLoss_nonneg : 0 ≤ lowerLoss := by
    simpa [lowerLoss, rLower] using
      section52MomentLossCoeff_nonneg_at_shift hP4
        hP4.sLower_pos hrLower_gt hrLower_lt_one
  have hC0_nonneg : 0 ≤ C0 := by
    exact (mul_nonneg hC52_nonneg hLowerLoss_nonneg).trans
      (le_max_left (C52 * lowerLoss) (C52 * upperLoss))
  have hdecay_nonneg : 0 ≤ decay := by
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hUpperCoeff_le : upperCoeff ≤ C0 * decay := by
    have hdecay_upper :=
      shiftedUpperDecay_le_betaDecay hP4 m
    have hpref_nonneg : 0 ≤ C52 * upperLoss :=
      mul_nonneg hC52_nonneg hUpperLoss_nonneg
    calc
      upperCoeff =
          (C52 * upperLoss) *
            Real.rpow (3 : ℝ)
              (-((hP4.sUpper + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) := by
            simp [upperCoeff, upperLoss, rUpper, β,
              section52TwoExponentMomentBoundCoeff, mul_assoc]
      _ ≤ (C52 * upperLoss) * decay :=
            mul_le_mul_of_nonneg_left (by simpa [β, decay] using hdecay_upper)
              hpref_nonneg
      _ ≤ C0 * decay :=
            mul_le_mul_of_nonneg_right
              (le_max_right (C52 * lowerLoss) (C52 * upperLoss)) hdecay_nonneg
  have hLowerCoeff_le : lowerCoeff ≤ C0 * decay := by
    have hdecay_lower :=
      shiftedLowerDecay_le_betaDecay hP4 m
    have hpref_nonneg : 0 ≤ C52 * lowerLoss :=
      mul_nonneg hC52_nonneg hLowerLoss_nonneg
    calc
      lowerCoeff =
          (C52 * lowerLoss) *
            Real.rpow (3 : ℝ)
              (-((hP4.sLower + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) := by
            simp [lowerCoeff, lowerLoss, rLower, β,
              section52TwoExponentMomentBoundCoeff, mul_assoc]
      _ ≤ (C52 * lowerLoss) * decay :=
            mul_le_mul_of_nonneg_left (by simpa [β, decay] using hdecay_lower)
              hpref_nonneg
      _ ≤ C0 * decay :=
            mul_le_mul_of_nonneg_right
              (le_max_left (C52 * lowerLoss) (C52 * upperLoss)) hdecay_nonneg
  refine ⟨C0, hC0_nonneg, ?_⟩
  dsimp only
  have hLowerHolder :=
    lowerPositiveExcess_responseJ_expectation_le_of_integrable hP hStruct hP4 k m e
      (by simpa [β, rLower] using hLowerPowInt)
      (by simpa [ζ, p_e, q_e] using hResponsePowInt)
  have hUpperHolder :=
    upperPositiveExcess_responseJ_expectation_le_of_integrable hP hStruct hP4 k m e
      (by simpa [β, rUpper] using hUpperPowInt)
      (by simpa [ζ, p_e, q_e] using hResponsePowInt)
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hLower0_nonneg :
      0 ≤ Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi :=
    Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUpper0_nonneg :
      0 ≤ Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi :=
    Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hJpow_nonneg :
      ∀ a, 0 ≤ Real.rpow (J a) ζ := by
    intro a
    exact Real.rpow_nonneg
      (Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a) _
  have hJpow_integral_nonneg :
      0 ≤ ∫ a, Real.rpow (J a) ζ ∂P :=
    integral_nonneg hJpow_nonneg
  have hResponse_nonneg : 0 ≤ responseMoment := by
    dsimp [responseMoment, coarseFluctuationResponseMomentAtScale, J, ζ, p_e, q_e]
    exact Real.rpow_nonneg hJpow_integral_nonneg _
  have hLowerMomentBound :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct ≤
        lowerCoeff * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
    simpa [lowerCoeff, rLower] using hBounds.2
  have hUpperMomentBound :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct ≤
        upperCoeff * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
    simpa [upperCoeff, rUpper] using hBounds.1
  have hLowerIntegral_le :
      ∫ a, lowerExcess a * J a ∂P ≤
        ((C0 * decay) *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
    calc
      ∫ a, lowerExcess a * J a ∂P
          ≤
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
          responseMoment := by
            simpa [lowerExcess, J, responseMoment, rLower, β, p_e, q_e] using hLowerHolder
      _ ≤
        (lowerCoeff * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment :=
            mul_le_mul_of_nonneg_right hLowerMomentBound hResponse_nonneg
      _ ≤
        ((C0 * decay) *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLowerCoeff_le hLower0_nonneg)
              hResponse_nonneg
  have hUpperIntegral_le :
      ∫ a, upperExcess a * J a ∂P ≤
        ((C0 * decay) *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
    calc
      ∫ a, upperExcess a * J a ∂P
          ≤
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          responseMoment := by
            simpa [upperExcess, J, responseMoment, rUpper, β, p_e, q_e] using hUpperHolder
      _ ≤
        (upperCoeff * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment :=
            mul_le_mul_of_nonneg_right hUpperMomentBound hResponse_nonneg
      _ ≤
        ((C0 * decay) *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hUpperCoeff_le hUpper0_nonneg)
              hResponse_nonneg
  have hWeightedLower :
      σ * (∫ a, lowerExcess a * J a ∂P) ≤
        (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
    calc
      σ * (∫ a, lowerExcess a * J a ∂P)
          ≤ σ *
            (((C0 * decay) *
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
              responseMoment) :=
            mul_le_mul_of_nonneg_left hLowerIntegral_le hσ_nonneg
      _ =
        (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by ring
  have hWeightedUpper :
      σ⁻¹ * (∫ a, upperExcess a * J a ∂P) ≤
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
    calc
      σ⁻¹ * (∫ a, upperExcess a * J a ∂P)
          ≤ σ⁻¹ *
            (((C0 * decay) *
              Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
              responseMoment) :=
            mul_le_mul_of_nonneg_left hUpperIntegral_le hσ_inv_nonneg
      _ =
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by ring
  have hUnit_nonneg :
      0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
    dsimp [coarseFluctuationUnitMomentWeightAtScale, σ]
    exact add_nonneg
      (mul_nonneg hσ_nonneg hLower0_nonneg)
      (mul_nonneg hσ_inv_nonneg hUpper0_nonneg)
  have hXi_one : (1 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hP4.xi_pos
  calc
    σ * (∫ a, lowerExcess a * J a ∂P) +
        σ⁻¹ * (∫ a, upperExcess a * J a ∂P)
        ≤
      (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment +
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment :=
        add_le_add hWeightedLower hWeightedUpper
    _ =
      C0 * decay *
        coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
          responseMoment := by
          simp [coarseFluctuationUnitMomentWeightAtScale, σ]
          ring
    _ ≤
      C0 * (hP4.xi : ℝ) * decay *
        coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
          responseMoment := by
          have hC0_le : C0 ≤ C0 * (hP4.xi : ℝ) := by
            calc
              C0 = C0 * 1 := by ring
              _ ≤ C0 * (hP4.xi : ℝ) :=
                mul_le_mul_of_nonneg_left hXi_one hC0_nonneg
          have htail_nonneg :
              0 ≤ decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment :=
            mul_nonneg (mul_nonneg hdecay_nonneg hUnit_nonneg) hResponse_nonneg
          calc
            C0 * decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment
                =
              C0 *
                (decay *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    responseMoment) := by ring
            _ ≤
              (C0 * (hP4.xi : ℝ)) *
                (decay *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    responseMoment) :=
                mul_le_mul_of_nonneg_right hC0_le htail_nonneg
            _ =
              C0 * (hP4.xi : ℝ) * decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment := by ring

theorem ellipticityPositiveExcess_childResponseAverage_expectation_le_uniform
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d,
        let β := section53CoarseFluctuationBeta hP4
        let rLower := hP4.sLower + β
        let rUpper := hP4.sUpper + β
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let childAvg : RegCoeffField d → ℝ :=
          fun a =>
            descendantsAverage (originCube d (m : ℤ))
              (Int.toNat ((m : ℤ) - (k : ℤ)))
              (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
        σ *
            (∫ a,
              (max
                  ((Ch04.lambdaSqCoeffField
                      (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
                    (hP.barSigmaStarAtScale hStruct 0)⁻¹)
                  0) * childAvg a ∂P) +
          σ⁻¹ *
            (∫ a,
              (max
                  (Ch04.LambdaSqCoeffField
                      (originCube d (m : ℤ)) rUpper (.finite 1) a -
                    hP.barSigmaAtScale hStruct 0)
                  0) * childAvg a ∂P)
          ≤
            C * (hP4.xi : ℝ) *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  let β := section53CoarseFluctuationBetaParams params
  let ζ := section53CoarseFluctuationZetaParams params
  let rLower := params.sLower + β
  let rUpper := params.sUpper + β
  rcases Section52.multiscaleEllipticityMomentBounds_homogenizationScale
      (d := d) with ⟨C52, hC52_nonneg, hC52_bound⟩
  let upperLoss : ℝ :=
    section52MomentLossCoeff d params.xi params.sUpper rUpper
  let lowerLoss : ℝ :=
    section52MomentLossCoeff d params.xi params.sLower rLower
  let C0 : ℝ := max 0 (max (C52 * lowerLoss) (C52 * upperLoss))
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    exact le_max_left _ _
  refine ⟨C0, hC0_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e
  subst params
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hrLower_gt : hP4.sLower < rLower := by
    simpa [rLower, β] using sLower_lt_sLower_add_beta hP4
  have hrUpper_gt : hP4.sUpper < rUpper := by
    simpa [rUpper, β] using sUpper_lt_sUpper_add_beta hP4
  have hrLower_lt_one : rLower < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    have hbeta := section53CoarseFluctuationBeta_pos hP4
    have hlt : hP4.sLower + section53CoarseFluctuationBeta hP4 < 1 := by
      nlinarith [hP4.sUpper_pos]
    simpa [rLower, β] using hlt
  have hrUpper_lt_one : rUpper < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    have hbeta := section53CoarseFluctuationBeta_pos hP4
    have hlt : hP4.sUpper + section53CoarseFluctuationBeta hP4 < 1 := by
      nlinarith [hP4.sLower_pos]
    simpa [rUpper, β] using hlt
  have hUpperLoss_nonneg : 0 ≤ upperLoss := by
    simpa [upperLoss, rUpper] using
      section52MomentLossCoeff_nonneg_at_shift hP4
        hP4.sUpper_pos hrUpper_gt hrUpper_lt_one
  have hLowerLoss_nonneg : 0 ≤ lowerLoss := by
    simpa [lowerLoss, rLower] using
      section52MomentLossCoeff_nonneg_at_shift hP4
        hP4.sLower_pos hrLower_gt hrLower_lt_one
  have hC0_ge_lower : C52 * lowerLoss ≤ C0 := by
    dsimp [C0]
    exact (le_max_left (C52 * lowerLoss) (C52 * upperLoss)).trans
      (le_max_right 0 (max (C52 * lowerLoss) (C52 * upperLoss)))
  have hC0_ge_upper : C52 * upperLoss ≤ C0 := by
    dsimp [C0]
    exact (le_max_right (C52 * lowerLoss) (C52 * upperLoss)).trans
      (le_max_right 0 (max (C52 * lowerLoss) (C52 * upperLoss)))
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : RegCoeffField d → ℝ :=
    fun a =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - (k : ℤ)))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField
            (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField
            (originCube d (m : ℤ)) rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let responseMoment :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hBounds := hC52_bound hP hStruct hP4 rUpper rLower m
    hrUpper_gt hrUpper_lt_one hrLower_gt hrLower_lt_one
  let upperCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 hP4.sUpper rUpper m
  let lowerCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 hP4.sLower rLower m
  let decay : ℝ := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  have hdecay_nonneg : 0 ≤ decay := by
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hUpperCoeff_le : upperCoeff ≤ C0 * decay := by
    have hdecay_upper :=
      shiftedUpperDecay_le_betaDecay hP4 m
    have hpref_nonneg : 0 ≤ C52 * upperLoss :=
      mul_nonneg hC52_nonneg hUpperLoss_nonneg
    calc
      upperCoeff =
          (C52 * upperLoss) *
            Real.rpow (3 : ℝ)
              (-((hP4.sUpper + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) := by
            simp [upperCoeff, upperLoss, rUpper, β,
              section52TwoExponentMomentBoundCoeff, mul_assoc]
      _ ≤ (C52 * upperLoss) * decay :=
            mul_le_mul_of_nonneg_left (by simpa [β, decay] using hdecay_upper)
              hpref_nonneg
      _ ≤ C0 * decay :=
            mul_le_mul_of_nonneg_right hC0_ge_upper hdecay_nonneg
  have hLowerCoeff_le : lowerCoeff ≤ C0 * decay := by
    have hdecay_lower :=
      shiftedLowerDecay_le_betaDecay hP4 m
    have hpref_nonneg : 0 ≤ C52 * lowerLoss :=
      mul_nonneg hC52_nonneg hLowerLoss_nonneg
    calc
      lowerCoeff =
          (C52 * lowerLoss) *
            Real.rpow (3 : ℝ)
              (-((hP4.sLower + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) := by
            simp [lowerCoeff, lowerLoss, rLower, β,
              section52TwoExponentMomentBoundCoeff, mul_assoc]
      _ ≤ (C52 * lowerLoss) * decay :=
            mul_le_mul_of_nonneg_left (by simpa [β, decay] using hdecay_lower)
              hpref_nonneg
      _ ≤ C0 * decay :=
            mul_le_mul_of_nonneg_right hC0_ge_lower hdecay_nonneg
  have hLowerPowInt :
      Integrable (fun a : RegCoeffField d => lowerExcess a ^ hP4.xi) P := by
    simpa [lowerExcess, rLower, β] using
      Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hrLower_gt hrLower_lt_one m
  have hUpperPowInt :
      Integrable (fun a : RegCoeffField d => upperExcess a ^ hP4.xi) P := by
    simpa [upperExcess, rUpper, β] using
      Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hrUpper_gt hrUpper_lt_one m
  have hLower_aemeas : AEMeasurable lowerExcess P := by
    have hrLower_pos : 0 < rLower := by
      dsimp [rLower, β]
      linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
    exact
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (m : ℤ)) hrLower_pos).sub aemeasurable_const).max
        aemeasurable_const
  have hUpper_aemeas : AEMeasurable upperExcess P := by
    have hrUpper_pos : 0 < rUpper := by
      dsimp [rUpper, β]
      linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
    exact
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (m : ℤ)) hrUpper_pos).sub aemeasurable_const).max
        aemeasurable_const
  have hLower_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpper_nonneg : ∀ᵐ a ∂P, 0 ≤ upperExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hLower_mem :
      MemLp lowerExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLower_aemeas
      hLower_nonneg hLowerPowInt
  have hUpper_mem :
      MemLp upperExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpper_aemeas
      hUpper_nonneg hUpperPowInt
  have hChild_aemeas : AEMeasurable childAvg P := by
    simpa [childAvg] using
      hP.aemeasurable_descendantsAverage_restrictionResponseJObservableCubeSet
        (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - (k : ℤ))) p_e q_e
  have hChild_nonneg : ∀ᵐ a ∂P, 0 ≤ childAvg a := by
    filter_upwards with a
    dsimp [childAvg]
    exact descendantsAverage_nonneg (originCube d (m : ℤ))
      (Int.toNat ((m : ℤ) - (k : ℤ)))
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hChild_mem :
      MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, ζ, p_e, q_e] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hChildMomentRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    have hIntLe :=
      integral_rpow_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_le_originCube_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
    have hChildPow_nonneg :
        0 ≤ ∫ a, childAvg a ^ ζ ∂P := by
      refine integral_nonneg ?_
      intro a
      have hnonneg : 0 ≤ childAvg a := by
        dsimp [childAvg]
        exact descendantsAverage_nonneg (originCube d (m : ℤ))
          (Int.toNat ((m : ℤ) - (k : ℤ)))
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
          (fun R hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
      exact Real.rpow_nonneg hnonneg _
    have hroot_nonneg : 0 ≤ 1 / ζ := by positivity
    have hroot :=
      Real.rpow_le_rpow hChildPow_nonneg
        (by simpa [childAvg, ζ, p_e, q_e, Real.rpow_eq_pow] using hIntLe)
        hroot_nonneg
    simpa [responseMoment, coarseFluctuationResponseMomentAtScale, ζ, p_e, q_e,
      one_div] using hroot
  have hLowerHolder :
      ∫ a, lowerExcess a * childAvg a ∂P ≤
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
          responseMoment := by
    have hHolderRaw :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) (holderConjugate_xi_section53CoarseFluctuationZeta hP4)
        hLower_nonneg hChild_nonneg hLower_mem hChild_mem
    have hHolder :
        ∫ a, lowerExcess a * childAvg a ∂P ≤
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa [lowerExcess, lambdaInvPositiveExcessMomentAtScale,
        Ch04.annealedMomentRoot, rLower, ζ, one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul_of_nonneg_left hChildMomentRoot_le
        (Section52.lambdaInvPositiveExcessMomentAtScale_nonneg
          rLower hP4.xi hP hStruct (m : ℤ)))
  have hUpperHolder :
      ∫ a, upperExcess a * childAvg a ∂P ≤
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          responseMoment := by
    have hHolderRaw :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) (holderConjugate_xi_section53CoarseFluctuationZeta hP4)
        hUpper_nonneg hChild_nonneg hUpper_mem hChild_mem
    have hHolder :
        ∫ a, upperExcess a * childAvg a ∂P ≤
          LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa [upperExcess, LambdaPositiveExcessMomentAtScale,
        Ch04.annealedMomentRoot, rUpper, ζ, one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul_of_nonneg_left hChildMomentRoot_le
        (Section52.LambdaPositiveExcessMomentAtScale_nonneg
          rUpper hP4.xi hP hStruct (m : ℤ)))
  -- The remaining coefficient bookkeeping is identical to
  -- `ellipticityPositiveExcessContribution_expectation_le_of_integrable`.
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hLower0_nonneg :
      0 ≤ Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi :=
    Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUpper0_nonneg :
      0 ≤ Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi :=
    Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hResponse_nonneg : 0 ≤ responseMoment := by
    dsimp [responseMoment, coarseFluctuationResponseMomentAtScale, ζ, p_e, q_e]
    refine Real.rpow_nonneg ?_ _
    refine integral_nonneg ?_
    intro a
    exact Real.rpow_nonneg
      (Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a) _
  have hLowerMomentBound :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct ≤
        lowerCoeff * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
    simpa [lowerCoeff, rLower] using hBounds.2
  have hUpperMomentBound :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct ≤
        upperCoeff * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
    simpa [upperCoeff, rUpper] using hBounds.1
  have hLowerIntegral_le :
      ∫ a, lowerExcess a * childAvg a ∂P ≤
        ((C0 * decay) *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
    calc
      ∫ a, lowerExcess a * childAvg a ∂P
          ≤
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
          responseMoment := hLowerHolder
      _ ≤
        (lowerCoeff * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment :=
            mul_le_mul_of_nonneg_right hLowerMomentBound hResponse_nonneg
      _ ≤
        ((C0 * decay) *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLowerCoeff_le hLower0_nonneg)
              hResponse_nonneg
  have hUpperIntegral_le :
      ∫ a, upperExcess a * childAvg a ∂P ≤
        ((C0 * decay) *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
    calc
      ∫ a, upperExcess a * childAvg a ∂P
          ≤
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          responseMoment := hUpperHolder
      _ ≤
        (upperCoeff * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment :=
            mul_le_mul_of_nonneg_right hUpperMomentBound hResponse_nonneg
      _ ≤
        ((C0 * decay) *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hUpperCoeff_le hUpper0_nonneg)
              hResponse_nonneg
  have hWeightedLower :
      σ * (∫ a, lowerExcess a * childAvg a ∂P) ≤
        (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by
    calc
      σ * (∫ a, lowerExcess a * childAvg a ∂P)
          ≤ σ *
            (((C0 * decay) *
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
              responseMoment) :=
            mul_le_mul_of_nonneg_left hLowerIntegral_le hσ_nonneg
      _ =
        (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment := by ring
  have hWeightedUpper :
      σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P) ≤
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
    calc
      σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
          ≤ σ⁻¹ *
            (((C0 * decay) *
              Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
              responseMoment) :=
            mul_le_mul_of_nonneg_left hUpperIntegral_le hσ_inv_nonneg
      _ =
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment := by ring
  have hUnit_nonneg :
      0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
    dsimp [coarseFluctuationUnitMomentWeightAtScale, σ]
    exact add_nonneg
      (mul_nonneg hσ_nonneg hLower0_nonneg)
      (mul_nonneg hσ_inv_nonneg hUpper0_nonneg)
  have hXi_one : (1 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hP4.xi_pos
  dsimp only
  calc
    σ * (∫ a, lowerExcess a * childAvg a ∂P) +
        σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
        ≤
      (C0 * decay) *
          (σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) *
          responseMoment +
        (C0 * decay) *
          (σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi) *
          responseMoment :=
        add_le_add hWeightedLower hWeightedUpper
    _ =
      C0 * decay *
        coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
          responseMoment := by
          simp [coarseFluctuationUnitMomentWeightAtScale, σ]
          ring
    _ ≤
      C0 * (hP4.xi : ℝ) * decay *
        coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
          responseMoment := by
          have hC0_le : C0 ≤ C0 * (hP4.xi : ℝ) := by
            calc
              C0 = C0 * 1 := by ring
              _ ≤ C0 * (hP4.xi : ℝ) :=
                mul_le_mul_of_nonneg_left hXi_one hC0_nonneg
          have htail_nonneg :
              0 ≤ decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment :=
            mul_nonneg (mul_nonneg hdecay_nonneg hUnit_nonneg) hResponse_nonneg
          calc
            C0 * decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment
                =
              C0 *
                (decay *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    responseMoment) := by ring
            _ ≤
              (C0 * (hP4.xi : ℝ)) *
                (decay *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    responseMoment) :=
                mul_le_mul_of_nonneg_right hC0_le htail_nonneg
            _ =
              C0 * (hP4.xi : ℝ) * decay *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  responseMoment := by ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
