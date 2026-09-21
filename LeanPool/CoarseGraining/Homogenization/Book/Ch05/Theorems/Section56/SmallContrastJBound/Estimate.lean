/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastJBound.Preliminaries

/-! # Estimate -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

open Section53.JUpperBoundCoarseFluctuations

theorem expectedResponseJCubeSet_special_le_two_smallContrastReducedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (C0 η : ℝ) (hC0_nonneg : 0 ≤ C0)
    (hC0_eta_le_quarter : 2 * C0 * η ≤ 1 / 4)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1)
    (hyoung :
      expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) ≤
        coarseFluctuationYoungManuscriptRHSAtScale
          hP hStruct hP4 C0 1 η k m e)
    (hlow_coeff :
      32 * C0 * (section53CoarseFluctuationBeta hP4 ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * section53CoarseFluctuationBeta hP4 * (((m - k : ℕ) : ℝ))) ≤
        1 / 4) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
      2 * smallContrastReducedRHSAtScale hP hStruct hP4 C0 η k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let J := Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e
  let Jk := Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e
  let tau := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  let F := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let tauSum := coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
  let scalar := coarseFluctuationScalarWeightAtScale hP hStruct m
  let U := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
  let Rm := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let D1 := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let D2 := Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let Center := (Real.sqrt θ - 1) ^ (2 : ℕ)
  let ThetaSq := (θ - 1) ^ (2 : ℕ)
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hkm_le : k ≤ m := hkm.le
  have hraw_center :
      J ≤ 2 * expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e := by
    simpa [J, p_e, q_e] using
      expectedResponseJCubeSet_special_le_two_expectedCenteredResponseJAtScale
        hP hStruct hP4 m e he
  have hraw_young :
      J ≤
        2 * coarseFluctuationYoungManuscriptRHSAtScale
          hP hStruct hP4 C0 1 η k m e := by
    calc
      J ≤ 2 * expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e :=
        hraw_center
      _ ≤ 2 * coarseFluctuationYoungManuscriptRHSAtScale
          hP hStruct hP4 C0 1 η k m e :=
        mul_le_mul_of_nonneg_left
          (by simpa [p_e, q_e] using hyoung) (by norm_num)
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J, Ch04.expectedResponseJCubeSet]
    exact integral_nonneg fun a =>
      Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (m : ℤ)) p_e q_e a
  have htau_nonneg : 0 ≤ tau := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm_le
    have hBlockM :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
    have hBlockK :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
    have hDescBlock :
        ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
          Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
      intro R hR
      exact
        hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
          hstat hk_nonneg hkm_int hR hBlockK
    simpa [tau] using
      Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
        hP hstat hk_nonneg hkm_int p_e q_e hBlockM hDescBlock
  have hF_nonneg : 0 ≤ F := by
    simpa [F] using
      coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m
  have htauSum_nonneg : 0 ≤ tauSum := by
    simpa [tauSum] using
      coarseFluctuationTauSumAtScale_nonneg hP hstat hStruct hP4 k m e
  have hscalar_nonneg : 0 ≤ scalar := by
    simpa [scalar] using
      coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hD1_nonneg : 0 ≤ D1 := by
    dsimp [D1]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hD2_nonneg : 0 ≤ D2 := by
    dsimp [D2]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_two : θ ≤ 2 := by
    simpa [θ] using
      thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
        hP hStruct hP4 hsmall m
  have hθ_minus_nonneg : 0 ≤ θ - 1 := by linarith
  have hCenter_le_ThetaSq : Center ≤ ThetaSq := by
    simpa [Center, ThetaSq, θ] using sqrt_sub_one_sq_le_theta_sub_one_sq hθ_one
  have hscalar_le : scalar ≤ 4 := by
    simpa [scalar] using
      coarseFluctuationScalarWeightAtScale_le_four_of_smallContrast
        hP hStruct hP4 hsmall m
  have htauSum_le : tauSum ≤ 5 * β⁻¹ * tau := by
    simpa [tauSum, tau, β, p_e, q_e] using
      coarseFluctuationTauSumAtScale_le_five_beta_inv_tauAtScale
        hP hstat hStruct hP4 hkm_le e
  have hUR_le : U * Rm ≤ 16 := by
    simpa [U, Rm] using
      coarseFluctuationUnitMomentWeight_mul_responseMoment_le_sixteen_of_smallContrast
        hP hstat hStruct hP4 hsmall hkm_le e he
  have hUR_nonneg : 0 ≤ U * Rm := by
    exact mul_nonneg
      (coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m)
      (coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e)
  have hJ_lower :
      (1 / 4 : ℝ) * (θ - 1) ≤ J := by
    simpa [J, θ, p_e, q_e] using
      expectedResponseJCubeSet_special_ge_quarter_theta_sub_one
        hP hStruct hP4 hsmall m e he
  have hθ_minus_le_J : θ - 1 ≤ 4 * J := by nlinarith
  have hJk_eq : Jk = J + tau := by
    simpa [Jk, J, tau, p_e, q_e] using
      expectedResponseJCubeSet_origin_eq_origin_add_tauAtScale
        P (m : ℤ) (k : ℤ) p_e q_e
  have hfirst :
      2 * (C0 * (η * Jk + η⁻¹ * tau)) ≤
        (1 / 4 : ℝ) * J + 2 * C0 * (η + η⁻¹) * tau := by
    have hJpart : 2 * C0 * η * J ≤ (1 / 4 : ℝ) * J :=
      mul_le_mul_of_nonneg_right hC0_eta_le_quarter hJ_nonneg
    rw [hJk_eq]
    nlinarith
  have hfluct :
      2 * (C0 * β⁻¹ * θ * F) ≤ 4 * C0 * β⁻¹ * F := by
    have hcoeff_nonneg : 0 ≤ 2 * C0 * β⁻¹ * F := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0_nonneg)
        (inv_nonneg.mpr hβ_pos.le)) hF_nonneg
    calc
      2 * (C0 * β⁻¹ * θ * F) =
          (2 * C0 * β⁻¹ * F) * θ := by ring
      _ ≤ (2 * C0 * β⁻¹ * F) * 2 :=
          mul_le_mul_of_nonneg_left hθ_two hcoeff_nonneg
      _ = 4 * C0 * β⁻¹ * F := by ring
  have htau_sum_term :
      2 * (C0 * (β ^ 2)⁻¹ * scalar * tauSum) ≤
        40 * C0 * (β ^ 3)⁻¹ * tau := by
    have hscalar_tau :
        scalar * tauSum ≤ 20 * β⁻¹ * tau := by
      calc
        scalar * tauSum ≤ 4 * tauSum :=
          mul_le_mul_of_nonneg_right hscalar_le htauSum_nonneg
        _ ≤ 4 * (5 * β⁻¹ * tau) :=
          mul_le_mul_of_nonneg_left htauSum_le (by norm_num)
        _ = 20 * β⁻¹ * tau := by ring
    have hcoeff_nonneg : 0 ≤ 2 * C0 * (β ^ 2)⁻¹ := by
      exact mul_nonneg (mul_nonneg (by positivity) hC0_nonneg)
        (inv_nonneg.mpr (sq_nonneg β))
    calc
      2 * (C0 * (β ^ 2)⁻¹ * scalar * tauSum) =
          (2 * C0 * (β ^ 2)⁻¹) * (scalar * tauSum) := by ring
      _ ≤ (2 * C0 * (β ^ 2)⁻¹) * (20 * β⁻¹ * tau) :=
          mul_le_mul_of_nonneg_left hscalar_tau hcoeff_nonneg
      _ = 40 * C0 * (β ^ 3)⁻¹ * tau := by
          field_simp [hβ_ne]
          ring
  have hresponse_term :
      2 * (C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 * U * Rm) ≤
        32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 := by
    have hcoeff_nonneg :
        0 ≤ 2 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) hC0_nonneg)
            (by exact_mod_cast Nat.zero_le hP4.xi))
          (inv_nonneg.mpr (pow_nonneg hβ_pos.le 3)))
        hD1_nonneg
    calc
      2 * (C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 * U * Rm) =
          (2 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1) * (U * Rm) := by ring
      _ ≤ (2 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1) * 16 :=
          mul_le_mul_of_nonneg_left hUR_le hcoeff_nonneg
      _ = 32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 := by ring
  have hlow :
      2 * (C0 * (β ^ 2)⁻¹ * D2 * scalar * (θ - 1)) ≤
        (1 / 4 : ℝ) * J := by
    have hlow_coeff' :
        32 * C0 * (β ^ 2)⁻¹ * D2 ≤ 1 / 4 := by
      simpa [β, D2] using hlow_coeff
    have hscalar_theta : scalar * (θ - 1) ≤ 16 * J := by
      calc
        scalar * (θ - 1) ≤ 4 * (θ - 1) :=
          mul_le_mul_of_nonneg_right hscalar_le hθ_minus_nonneg
        _ ≤ 4 * (4 * J) :=
          mul_le_mul_of_nonneg_left hθ_minus_le_J (by norm_num)
        _ = 16 * J := by ring
    have hcoeff_nonneg : 0 ≤ 2 * C0 * (β ^ 2)⁻¹ * D2 := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hC0_nonneg)
          (inv_nonneg.mpr (sq_nonneg β))) hD2_nonneg
    calc
      2 * (C0 * (β ^ 2)⁻¹ * D2 * scalar * (θ - 1)) =
          (2 * C0 * (β ^ 2)⁻¹ * D2) * (scalar * (θ - 1)) := by ring
      _ ≤ (2 * C0 * (β ^ 2)⁻¹ * D2) * (16 * J) :=
          mul_le_mul_of_nonneg_left hscalar_theta hcoeff_nonneg
      _ = (32 * C0 * (β ^ 2)⁻¹ * D2) * J := by ring
      _ ≤ (1 / 4 : ℝ) * J :=
          mul_le_mul_of_nonneg_right hlow_coeff' hJ_nonneg
  let tauTerm1 : ℝ := 2 * C0 * (η + η⁻¹) * tau
  let thetaTerm : ℝ := 2 * C0 * ThetaSq
  let fluctTerm : ℝ := 4 * C0 * β⁻¹ * F
  let tauTerm2 : ℝ := 40 * C0 * (β ^ 3)⁻¹ * tau
  let tailTerm : ℝ := 32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1
  let reducedBound : ℝ :=
    fluctTerm + (tauTerm1 + tauTerm2) + tailTerm + thetaTerm
  have hJ_le_reduced : J ≤ 2 * reducedBound := by
    have hcenter :
        2 * (C0 * Center) ≤ 2 * C0 * ThetaSq := by
      calc
        2 * (C0 * Center) = (2 * C0) * Center := by ring
        _ ≤ (2 * C0) * ThetaSq :=
            mul_le_mul_of_nonneg_left hCenter_le_ThetaSq
              (mul_nonneg (by norm_num) hC0_nonneg)
        _ = 2 * C0 * ThetaSq := by ring
    have hT1 :
        2 *
            (C0 *
              (η *
                  Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
                    (specialPAtScale hP hStruct (m : ℤ) e)
                    (specialQAtScale hP hStruct (m : ℤ) e) +
                η⁻¹ *
                  tauAtScale P (m : ℤ) (k : ℤ)
                    (specialPAtScale hP hStruct (m : ℤ) e)
                    (specialQAtScale hP hStruct (m : ℤ) e))) ≤
          (1 / 4 : ℝ) * J + tauTerm1 := by
      change 2 * (C0 * (η * Jk + η⁻¹ * tau)) ≤
        (1 / 4 : ℝ) * J + 2 * C0 * (η + η⁻¹) * tau
      exact hfirst
    have hT2 :
        2 *
            (C0 *
              (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^
                (2 : ℕ)) ≤ thetaTerm := by
      change 2 * (C0 * Center) ≤ 2 * C0 * ThetaSq
      exact hcenter
    have hT3 :
        2 *
            (C0 * (section53CoarseFluctuationBeta hP4)⁻¹ *
              thetaAtScale hP hStruct (m : ℤ) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) ≤
          fluctTerm := by
      change 2 * (C0 * β⁻¹ * θ * F) ≤ 4 * C0 * β⁻¹ * F
      exact hfluct
    have hT4 :
        2 *
            (C0 * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
              coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) ≤
          tauTerm2 := by
      change 2 * (C0 * (β ^ 2)⁻¹ * scalar * tauSum) ≤
        40 * C0 * (β ^ 3)⁻¹ * tau
      exact htau_sum_term
    have hT5 :
        2 *
            (C0 * (hP4.xi : ℝ) *
              ((section53CoarseFluctuationBeta hP4) ^ 3)⁻¹ *
              Real.rpow (3 : ℝ)
                (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) ≤
          tailTerm := by
      change 2 * (C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 * U * Rm) ≤
        32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1
      exact hresponse_term
    have hT6 :
        2 *
            (C0 * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
              Real.rpow (3 : ℝ)
                (-2 * section53CoarseFluctuationBeta hP4 *
                  (((m - k : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
              (thetaAtScale hP hStruct (m : ℤ) - 1)) ≤
          (1 / 4 : ℝ) * J := by
      change 2 * (C0 * (β ^ 2)⁻¹ * D2 * scalar * (θ - 1)) ≤
        (1 / 4 : ℝ) * J
      exact hlow
    have hYsum :
        2 * coarseFluctuationYoungManuscriptRHSAtScale
            hP hStruct hP4 C0 1 η k m e ≤
          ((1 / 4 : ℝ) * J + tauTerm1) + thetaTerm + fluctTerm +
            tauTerm2 + tailTerm + (1 / 4 : ℝ) * J := by
      exact
        young_rhs_two_mul_le_sum_of_term_bounds hP hStruct hP4 C0 η k m e
          ((1 / 4 : ℝ) * J + tauTerm1) thetaTerm fluctTerm tauTerm2
          tailTerm ((1 / 4 : ℝ) * J) hT1 hT2 hT3 hT4 hT5 hT6
    change J ≤
      2 * (fluctTerm + (tauTerm1 + tauTerm2) + tailTerm + thetaTerm)
    exact absorb_quarter_terms (hraw_young.trans hYsum)
  change J ≤
    2 *
      (4 * C0 * β⁻¹ * F +
        (2 * C0 * (η + η⁻¹) * tau + 40 * C0 * (β ^ 3)⁻¹ * tau) +
          32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 +
            2 * C0 * ThetaSq)
  exact hJ_le_reduced

theorem two_smallContrastReducedRHSAtScale_le_smallContrastFinalRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C0 η C : ℝ) {k m : ℕ} (hkm : k ≤ m) (e : Vec d)
    (hKfluct :
      8 * C0 * (section53CoarseFluctuationBeta hP4)⁻¹ ≤ C)
    (hKtau :
      4 * C0 * (η + η⁻¹) +
          80 * C0 * ((section53CoarseFluctuationBeta hP4) ^ 3)⁻¹ ≤ C)
    (hKtail :
      64 * C0 * (hP4.xi : ℝ) *
          ((section53CoarseFluctuationBeta hP4) ^ 3)⁻¹ ≤ C)
    (hKtheta : 4 * C0 ≤ C) :
    2 * smallContrastReducedRHSAtScale hP hStruct hP4 C0 η k m e ≤
      smallContrastFinalRHSAtScale hP hStruct hP4 C k m e := by
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let tau := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  let F := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let D1 := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let ThetaSq := (thetaAtScale hP hStruct (m : ℤ) - 1) ^ (2 : ℕ)
  have hF_nonneg : 0 ≤ F := by
    simpa [F] using
      coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m
  have htau_nonneg : 0 ≤ tau := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
    have hBlockM :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
    have hBlockK :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
    have hDescBlock :
        ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
          Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
      intro R hR
      exact
        hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
          hstat hk_nonneg hkm_int hR hBlockK
    simpa [tau] using
      Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
        hP hstat hk_nonneg hkm_int p_e q_e hBlockM hDescBlock
  have hD1_nonneg : 0 ≤ D1 := by
    dsimp [D1]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hThetaSq_nonneg : 0 ≤ ThetaSq := by
    dsimp [ThetaSq]
    exact sq_nonneg _
  have hFterm :
      2 * (4 * C0 * β⁻¹ * F) ≤ C * F := by
    calc
      2 * (4 * C0 * β⁻¹ * F) = (8 * C0 * β⁻¹) * F := by ring
      _ ≤ C * F := mul_le_mul_of_nonneg_right (by simpa [β] using hKfluct) hF_nonneg
  have htterm :
      2 * (2 * C0 * (η + η⁻¹) * tau +
          40 * C0 * (β ^ 3)⁻¹ * tau) ≤ C * tau := by
    calc
      2 * (2 * C0 * (η + η⁻¹) * tau +
          40 * C0 * (β ^ 3)⁻¹ * tau) =
          (4 * C0 * (η + η⁻¹) + 80 * C0 * (β ^ 3)⁻¹) * tau := by ring
      _ ≤ C * tau :=
          mul_le_mul_of_nonneg_right (by simpa [β] using hKtau) htau_nonneg
  have hdterm :
      2 * (32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1) ≤ C * D1 := by
    calc
      2 * (32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1) =
          (64 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹) * D1 := by ring
      _ ≤ C * D1 :=
          mul_le_mul_of_nonneg_right (by simpa [β] using hKtail) hD1_nonneg
  have hqterm :
      2 * (2 * C0 * ThetaSq) ≤ C * ThetaSq := by
    calc
      2 * (2 * C0 * ThetaSq) = (4 * C0) * ThetaSq := by ring
      _ ≤ C * ThetaSq := mul_le_mul_of_nonneg_right hKtheta hThetaSq_nonneg
  change
    2 *
        (4 * C0 * β⁻¹ * F +
          (2 * C0 * (η + η⁻¹) * tau + 40 * C0 * (β ^ 3)⁻¹ * tau) +
            32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * D1 +
              2 * C0 * ThetaSq) ≤
      C * F + C * tau + C * D1 + C * ThetaSq
  nlinarith [hFterm, htterm, hdterm, hqterm]

theorem smallContrastJBound_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {k m : ℕ}, C ≤ ((m - k : ℕ) : ℝ) →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
          smallContrastFinalRHSAtScale hP hStruct hP4 C k m e := by
  rcases
      JUpperBoundCoarseFluctuations_young_homogenizationScale params with
    ⟨C0, hC0_nonneg, hC0⟩
  let βp := section53CoarseFluctuationBetaParams params
  let η : ℝ := (8 * (C0 + 1))⁻¹
  let Aabs : ℝ := 32 * C0 * (βp ^ 2)⁻¹
  have hβp_pos : 0 < βp := by
    simpa [βp] using section53CoarseFluctuationBetaParams_pos params
  have hAabs_nonneg : 0 ≤ Aabs := by
    dsimp [Aabs]
    exact mul_nonneg (mul_nonneg (by positivity) hC0_nonneg)
      (inv_nonneg.mpr (sq_nonneg βp))
  rcases exists_decay_absorption_const hβp_pos hAabs_nonneg with
    ⟨Cgap, hCgap_nonneg, hCgap⟩
  let Kfluct : ℝ := 8 * C0 * βp⁻¹
  let Ktau : ℝ := 4 * C0 * (η + η⁻¹) + 80 * C0 * (βp ^ 3)⁻¹
  let Ktail : ℝ := 64 * C0 * (params.xi : ℝ) * (βp ^ 3)⁻¹
  let Ktheta : ℝ := 4 * C0
  let C : ℝ := max 1 (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta))))
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hstat hStruct hP4 hparams hsmall e he k m hgap
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  have hβeq : β = βp := by
    simpa [β, βp, hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hxi_eq : hP4.xi = params.xi := by
    simpa using
      congrArg QuantitativeCoarseGrainedEllipticityParams.xi hparams
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hdiff_ge_one : (1 : ℝ) ≤ ((m - k : ℕ) : ℝ) :=
    hC_ge_one.trans hgap
  have hdiff_pos_real : 0 < ((m - k : ℕ) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hdiff_ge_one
  have hdiff_pos_nat : 0 < m - k := by exact_mod_cast hdiff_pos_real
  have hkm : k < m := by omega
  have hkm_le : k ≤ m := hkm.le
  have hcentered :=
    hC0 hP hstat hStruct hP4 hparams hkm e he
      (ε := 1) (η := η) (by norm_num) (by norm_num) hη_pos
  have hC0_eta_le_quarter : 2 * C0 * η ≤ 1 / 4 := by
    dsimp [η]
    have hden_pos : 0 < 8 * (C0 + 1) := by positivity
    field_simp [hden_pos.ne']
    nlinarith [hC0_nonneg]
  have hCgap_le_C : Cgap ≤ C := by
    dsimp [C]
    exact
      (le_max_left Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))).trans
        (le_max_right 1 (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))))
  have hgap_for_abs : Cgap ≤ ((m - k : ℕ) : ℝ) :=
    hCgap_le_C.trans hgap
  have hlow_coeff :
      32 * C0 * (section53CoarseFluctuationBeta hP4 ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * section53CoarseFluctuationBeta hP4 * (((m - k : ℕ) : ℝ))) ≤
        1 / 4 := by
    have h := hCgap (n := m - k) hgap_for_abs
    simpa [Aabs, βp, β, hβeq] using h
  have hC_ge_Kfluct : Kfluct ≤ C := by
    dsimp [C]
    exact
      (le_max_left Kfluct (max Ktau (max Ktail Ktheta))).trans
        ((le_max_right Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))).trans
          (le_max_right 1 (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta))))))
  have hC_ge_Ktau : Ktau ≤ C := by
    dsimp [C]
    exact
      (le_max_left Ktau (max Ktail Ktheta)).trans
        ((le_max_right Kfluct (max Ktau (max Ktail Ktheta))).trans
          ((le_max_right Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))).trans
            (le_max_right 1 (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))))))
  have hC_ge_Ktail : Ktail ≤ C := by
    dsimp [C]
    exact
      (le_max_left Ktail Ktheta).trans
        ((le_max_right Ktau (max Ktail Ktheta)).trans
          ((le_max_right Kfluct (max Ktau (max Ktail Ktheta))).trans
            ((le_max_right Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))).trans
              (le_max_right 1
                (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta))))))))
  have hC_ge_Ktheta : Ktheta ≤ C := by
    dsimp [C]
    exact
      (le_max_right Ktail Ktheta).trans
        ((le_max_right Ktau (max Ktail Ktheta)).trans
          ((le_max_right Kfluct (max Ktau (max Ktail Ktheta))).trans
            ((le_max_right Cgap (max Kfluct (max Ktau (max Ktail Ktheta)))).trans
              (le_max_right 1
                (max Cgap (max Kfluct (max Ktau (max Ktail Ktheta))))))))
  have hKfluct_law :
      8 * C0 * β⁻¹ ≤ C := by
    simpa [Kfluct, βp, β, hβeq] using hC_ge_Kfluct
  have hKtau_law :
      4 * C0 * (η + η⁻¹) + 80 * C0 * (β ^ 3)⁻¹ ≤ C := by
    simpa [Ktau, βp, β, hβeq] using hC_ge_Ktau
  have hKtail_law :
      64 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ ≤ C := by
    simpa [Ktail, βp, β, hβeq, hxi_eq] using hC_ge_Ktail
  have hKtheta_law :
      4 * C0 ≤ C := by
    simpa [Ktheta] using hC_ge_Ktheta
  have hreduced :
      Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ))
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) ≤
        2 * smallContrastReducedRHSAtScale hP hStruct hP4 C0 η k m e := by
    exact
      expectedResponseJCubeSet_special_le_two_smallContrastReducedRHSAtScale
        hP hstat hStruct hP4 hsmall C0 η hC0_nonneg
        hC0_eta_le_quarter hkm e he hcentered hlow_coeff
  calc
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ))
        (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e)
        ≤ 2 * smallContrastReducedRHSAtScale hP hStruct hP4 C0 η k m e :=
      hreduced
    _ ≤ smallContrastFinalRHSAtScale hP hStruct hP4 C k m e :=
      two_smallContrastReducedRHSAtScale_le_smallContrastFinalRHSAtScale
        hP hstat hStruct hP4 C0 η C hkm_le e
        hKfluct_law hKtau_law hKtail_law hKtheta_law
end

end Section56
end Ch05
end Book
end Homogenization
