/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.YoungRHS
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ResponseMoment
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.RHSCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.Final

/-! # Preliminaries -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

open Section53.JUpperBoundCoarseFluctuations

/-!
# Section 5.6: small-contrast coarse-fluctuation iteration

This file formalizes the manuscript estimate
`e.J.upper.bound.coarse.fluctuations.small.contrast.final`.
-/

/-- The four-term right side in
`e.J.upper.bound.coarse.fluctuations.small.contrast.final`. -/
noncomputable def smallContrastFinalRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C : ℝ) (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  C * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      C * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e +
      C * Real.rpow (3 : ℝ) (-β * (m : ℝ)) +
        C * (thetaAtScale hP hStruct (m : ℤ) - 1) ^ (2 : ℕ)

noncomputable def smallContrastReducedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C0 η : ℝ) (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let tau := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  let fluctuationSum := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let decay := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let thetaSq := (thetaAtScale hP hStruct (m : ℤ) - 1) ^ (2 : ℕ)
  4 * C0 * β⁻¹ * fluctuationSum +
    (2 * C0 * (η + η⁻¹) * tau + 40 * C0 * (β ^ 3)⁻¹ * tau) +
      32 * C0 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ * decay +
        2 * C0 * thetaSq

theorem vecNorm_eq_one_of_vecNormSq_eq_one
    {d : ℕ} {e : Vec d} (he : vecNormSq e = 1) :
    Ch02.vecNorm e = 1 := by
  have hsq : Ch02.vecNorm e ^ (2 : ℕ) = (1 : ℝ) := by
    simpa [he] using Ch02.vecNorm_sq_eq_vecNormSq e
  have hnonneg : 0 ≤ Ch02.vecNorm e := Ch02.vecNorm_nonneg e
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · linarith

theorem thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    thetaAtScale hP hStruct (0 : ℤ) ≤
      widetildeThetaAtScale P (0 : ℤ) hP4 :=
  Section54.OneStepContraction.thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
    hP hStruct hP4

theorem thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2) (m : ℕ) :
    thetaAtScale hP hStruct (m : ℤ) ≤ 2 := by
  have hmono :
      thetaAtScale hP hStruct (m : ℤ) ≤
        thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.thetaAtScale_mono_of_P4
        hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have htheta0 :
      thetaAtScale hP hStruct (0 : ℤ) ≤
        widetildeThetaAtScale P (0 : ℤ) hP4 :=
    thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4 hP hStruct hP4
  exact hmono.trans (htheta0.trans hsmall)

theorem thetaAtScale_sub_one_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ thetaAtScale hP hStruct (m : ℤ) - 1 := by
  have hθ_one :
      1 ≤ thetaAtScale hP hStruct (m : ℤ) :=
    one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  linarith

theorem sqrt_sub_one_sq_le_theta_sub_one_sq
    {θ : ℝ} (hθ_one : 1 ≤ θ) :
    (Real.sqrt θ - 1) ^ (2 : ℕ) ≤ (θ - 1) ^ (2 : ℕ) := by
  have hsqrt_one : 1 ≤ Real.sqrt θ := Real.one_le_sqrt.mpr hθ_one
  have hleft_nonneg : 0 ≤ Real.sqrt θ - 1 := by linarith
  have hright_nonneg : 0 ≤ θ - 1 := by linarith
  have hsqrt_le : Real.sqrt θ ≤ θ := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hle : Real.sqrt θ - 1 ≤ θ - 1 := by linarith
  exact pow_le_pow_left₀ hleft_nonneg hle 2

theorem quarter_theta_sub_one_le_sqrt_sub_one
    {θ : ℝ} (hθ_one : 1 ≤ θ) (hθ_two : θ ≤ 2) :
    (1 / 4 : ℝ) * (θ - 1) ≤ Real.sqrt θ - 1 := by
  have hθ_nonneg : 0 ≤ θ := le_trans zero_le_one hθ_one
  have hsqrt_one : 1 ≤ Real.sqrt θ := Real.one_le_sqrt.mpr hθ_one
  have hsqrt_nonneg : 0 ≤ Real.sqrt θ := Real.sqrt_nonneg θ
  have hsqrt_le_two : Real.sqrt θ ≤ 2 := by
    have hsqrt_le : Real.sqrt θ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hθ_two
    have hsqrt2_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    exact hsqrt_le.trans hsqrt2_le_two
  have hfactor : Real.sqrt θ + 1 ≤ 4 := by linarith
  have hgap_nonneg : 0 ≤ Real.sqrt θ - 1 := by linarith
  have hprod :
      θ - 1 = (Real.sqrt θ - 1) * (Real.sqrt θ + 1) := by
    rw [sub_eq_iff_eq_add]
    nlinarith [Real.sq_sqrt hθ_nonneg]
  calc
    (1 / 4 : ℝ) * (θ - 1)
        = (Real.sqrt θ - 1) * ((Real.sqrt θ + 1) / 4) := by
          rw [hprod]
          ring
    _ ≤ (Real.sqrt θ - 1) * 1 := by
          exact mul_le_mul_of_nonneg_left (by nlinarith) hgap_nonneg
    _ = Real.sqrt θ - 1 := by ring

theorem expectedResponseJCubeSet_special_ge_quarter_theta_sub_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    (1 / 4 : ℝ) * (thetaAtScale hP hStruct (m : ℤ) - 1) ≤
      Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e := by
  dsimp only
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_two : θ ≤ 2 := by
    simpa [θ] using
      thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
        hP hStruct hP4 hsmall m
  have hEq :=
    expectedResponseJCubeSet_special_eq_sqrtTheta_sub_one_mul_vecNormSq
      hP hStruct hP4 m e
  calc
    (1 / 4 : ℝ) * (θ - 1) ≤ Real.sqrt θ - 1 :=
      quarter_theta_sub_one_le_sqrt_sub_one hθ_one hθ_two
    _ = (Real.sqrt θ - 1) * vecNormSq e := by rw [he, mul_one]
    _ = Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e := by
      simpa [p_e, q_e, θ] using hEq.symm

theorem expectedResponseJCubeSet_special_le_two_expectedCenteredResponseJAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
      2 * expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hraw_le :
      Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
        thetaAtScale hP hStruct (m : ℤ) - 1 := by
    simpa [p_e, q_e] using
      expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  have htheta_eq :
      thetaAtScale hP hStruct (m : ℤ) - 1 =
        2 * expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e := by
    simpa [p_e, q_e] using
      Section54.OneStepContraction.thetaAtScale_sub_one_eq_two_centeredResponse_special
        hP hStruct hP4 m e (vecNorm_eq_one_of_vecNormSq_eq_one he)
  calc
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e
        ≤ thetaAtScale hP hStruct (m : ℤ) - 1 := hraw_le
    _ = 2 * expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e :=
      htheta_eq

theorem coarseFluctuationScalarWeightAtScale_le_four_of_smallContrast
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    (m : ℕ) :
    coarseFluctuationScalarWeightAtScale hP hStruct m ≤ 4 := by
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hb0_pos : 0 < b0 := by
    simpa [b0] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0_pos : 0 < c0 := by
    simpa [c0] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hbm_pos : 0 < bm := by
    simpa [bm] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ_pos : 0 < σ := by
    simpa [σ] using Section54.GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hchain := Section54.Pigeonhole.scalarChain_of_P4
    hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have hc0_le_cm : c0 ≤ cm := by simpa [c0, cm] using hchain.1
  have hbm_le_b0 : bm ≤ b0 := by simpa [bm, b0] using hchain.2.2
  have hθ0_two : b0 * c0⁻¹ ≤ 2 := by
    have hθ0 :
        thetaAtScale hP hStruct (0 : ℤ) ≤ 2 :=
      (thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4 hP hStruct hP4).trans hsmall
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, c0] using hθ0
  have hb0_le_two_c0 : b0 ≤ 2 * c0 := by
    have hmul := mul_le_mul_of_nonneg_right hθ0_two hc0_pos.le
    have hcancel : b0 * c0⁻¹ * c0 = b0 := by field_simp [ne_of_gt hc0_pos]
    nlinarith
  have hcm_le_bm : cm ≤ bm := by
    simpa [bm, cm] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hcm_le_two_c0 : cm ≤ 2 * c0 := hcm_le_bm.trans (hbm_le_b0.trans hb0_le_two_c0)
  have hσ_le_two_c0 : σ ≤ 2 * c0 := by
    calc
      σ = Real.sqrt (bm * cm) := rfl
      _ ≤ Real.sqrt ((2 * c0) * (2 * c0)) := by
        exact Real.sqrt_le_sqrt
          (mul_le_mul (hbm_le_b0.trans hb0_le_two_c0) hcm_le_two_c0 hcm_pos.le
            (mul_nonneg (by norm_num) hc0_pos.le))
      _ = 2 * c0 := by
        rw [show (2 * c0) * (2 * c0) = (2 * c0) ^ (2 : ℕ) by ring,
          Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (by norm_num) hc0_pos)]
  have hc0_le_σ : c0 ≤ σ := by
    calc
      c0 ≤ cm := hc0_le_cm
      _ = Real.sqrt (cm * cm) := by
        rw [show cm * cm = cm ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs,
          abs_of_pos hcm_pos]
      _ ≤ Real.sqrt (bm * cm) := by
        exact Real.sqrt_le_sqrt
          (by
            have hmul := mul_le_mul_of_nonneg_right hcm_le_bm hcm_pos.le
            simpa [mul_comm] using hmul)
      _ = σ := rfl
  have hterm1 : σ * c0⁻¹ ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hσ_le_two_c0 (inv_pos.mpr hc0_pos).le
    have hcancel : (2 * c0) * c0⁻¹ = 2 := by field_simp [ne_of_gt hc0_pos]
    simpa [hcancel, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hterm2 : σ⁻¹ * b0 ≤ 2 := by
    have hσ_inv_le : σ⁻¹ ≤ c0⁻¹ := (inv_le_inv₀ hσ_pos hc0_pos).2 hc0_le_σ
    calc
      σ⁻¹ * b0 ≤ c0⁻¹ * b0 :=
        mul_le_mul_of_nonneg_right hσ_inv_le hb0_pos.le
      _ = b0 * c0⁻¹ := by ring
      _ ≤ 2 := hθ0_two
  have hsum : σ * c0⁻¹ + σ⁻¹ * b0 ≤ 4 := by
    nlinarith
  simpa [coarseFluctuationScalarWeightAtScale, σ, b0, c0] using hsum

theorem coarseFluctuationResponseMomentAtScale_le_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k ≤ m) (e : Vec d) :
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e := by
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hζ_nonneg : 0 ≤ ζ := hζ_pos.le
  have hζ_inv_nonneg : 0 ≤ ζ⁻¹ := inv_nonneg.mpr hζ_nonneg
  have hk_nonneg_int : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  let unitAvg : RegCoeffField d → ℝ :=
    fun a =>
      descendantsAverage (originCube d (k : ℤ))
        (Int.toNat ((k : ℤ) - (0 : ℤ)))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  have hparent_le_unit :
      Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e ≤ᵐ[P]
        unitAvg := by
    simpa [unitAvg, p_e, q_e] using
      hP.restrictionResponseJObservableCubeSet_le_descendantsAverage_ae
        (n := (0 : ℤ)) (m := (k : ℤ)) hk_nonneg_int p_e q_e
  have hparent_rpow_le_unit :
      ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ ∂P
        ≤ ∫ a, Real.rpow (unitAvg a) ζ ∂P := by
    refine integral_mono_ae ?_ ?_ ?_
    · exact
        integrable_rpow_restrictionResponseJObservableCubeSet_originCube_from_P4
          hP hStruct hP4 k p_e q_e
    · have hmem :=
        memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
          hP hstat hStruct hP4 (by norm_num : (0 : ℤ) ≤ 0) hk_nonneg_int p_e q_e
      have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
      have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by simp
      have hint :
          Integrable (fun a : RegCoeffField d => ‖unitAvg a‖ ^ (ENNReal.ofReal ζ).toReal) P :=
        hmem.integrable_norm_rpow hζ_ne_zero hζ_ne_top
      refine hint.congr ?_
      filter_upwards with a
      have hnonneg : 0 ≤ unitAvg a := by
        dsimp [unitAvg]
        exact descendantsAverage_nonneg _ _
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
          (fun R _hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
      rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hnonneg,
        Real.rpow_eq_pow]
    · filter_upwards [hparent_le_unit] with a hle
      exact Real.rpow_le_rpow
        (Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a)
        hle hζ_nonneg
  have hunit_le_zero :
      ∫ a, Real.rpow (unitAvg a) ζ ∂P ≤
        ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (0 : ℤ)) p_e q_e a) ζ ∂P := by
    simpa [unitAvg, ζ, p_e, q_e] using
      integral_rpow_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_le_originCube_of_stationary
        hP hstat hStruct hP4 (k := (0 : ℤ)) (m := (k : ℤ))
        (by norm_num) (by exact_mod_cast Nat.zero_le k) p_e q_e
  have hintegral_nonneg :
      0 ≤
        ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ ∂P := by
    exact integral_nonneg fun a =>
      Real.rpow_nonneg
        (Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a) _
  calc
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e =
        Real.rpow
          (∫ a,
            Real.rpow
              (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ ∂P)
          ζ⁻¹ := by
          simp [coarseFluctuationResponseMomentAtScale, ζ, p_e, q_e]
    _ ≤
        Real.rpow
          (∫ a,
            Real.rpow
              (Ch04.restrictionResponseJObservableCubeSet (originCube d (0 : ℤ)) p_e q_e a) ζ ∂P)
          ζ⁻¹ := by
          exact Real.rpow_le_rpow hintegral_nonneg
            (hparent_rpow_le_unit.trans hunit_le_zero) hζ_inv_nonneg
    _ =
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e := by
          simp [coarseFluctuationResponseMomentAtScale, ζ, p_e, q_e]

theorem coarseFluctuationUnitMomentWeight_mul_responseMoment_le_sixteen_of_smallContrast
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) (he : vecNormSq e = 1) :
    coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤ 16 := by
  let U := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
  let Rk := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let R0 := coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
  have hU_nonneg : 0 ≤ U := by
    simpa [U] using coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m
  have hRk_le_R0 : Rk ≤ R0 := by
    simpa [Rk, R0] using
      coarseFluctuationResponseMomentAtScale_le_zero hP hstat hStruct hP4 hkm e
  have hUR0 :
      U * R0 ≤ U ^ (2 : ℕ) := by
    simpa [U, R0] using
      Section54.OneStepContraction.coarseFluctuationUnitMomentWeight_mul_responseMoment_zero_le_sq
        hP hStruct hP4 m e (vecNorm_eq_one_of_vecNormSq_eq_one he)
  have hU_le : U ≤ 4 := by
    have h :=
      Section54.OneStepContraction.coarseFluctuationUnitMomentWeightAtScale_le_two_widetildeTheta_zero
        hP hStruct hP4 m
    calc
      U ≤ 2 * widetildeThetaAtScale P (0 : ℤ) hP4 := by simpa [U] using h
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = 4 := by norm_num
  calc
    U * Rk ≤ U * R0 := mul_le_mul_of_nonneg_left hRk_le_R0 hU_nonneg
    _ ≤ U ^ (2 : ℕ) := hUR0
    _ ≤ 4 ^ (2 : ℕ) := pow_le_pow_left₀ hU_nonneg hU_le 2
    _ = 16 := by norm_num

theorem sum_range_to_Icc_descending {k m : ℤ} (hkm : k ≤ m)
    (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _hj => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hj_lt_nat : j < Int.toNat (m - k) := Finset.mem_range.mp hj
    have hj_lt : (j : ℤ) < m - k := by
      have hj_lt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by
        exact_mod_cast hj_lt_nat
      simpa [hL] using hj_lt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _hj₁ j₂ _hj₂ h
    have h' : m - (j₁ : ℤ) = m - (j₂ : ℤ) := by simpa using h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro n hn
    have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
      have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hmn_lt : m - n < m - k := by omega
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      apply Finset.mem_range.mpr
      have hcast : ((Int.toNat (m - n) : ℕ) : ℤ) <
          ((Int.toNat (m - k) : ℕ) : ℤ) := by
        simpa [hto, hL] using hmn_lt
      exact_mod_cast hcast
    · have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      omega
  · intro j _hj
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    exact congrArg F harg.symm

theorem sum_Icc_betaWeight_le_five_beta_inv
    {k m : ℤ} (hkm : k ≤ m) {β : ℝ} (hβ : 0 < β) (hβ_le : β ≤ 1) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) ≤
      5 * β⁻¹ := by
  let L : ℕ := Int.toNat (m - k)
  have hsum_eq :
      (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) =
        ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    simpa [L] using
      (sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j => Real.rpow (3 : ℝ) (-β * (j : ℝ)))).symm
  have hrange_le :
      (∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ))) ≤
        ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
          Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      simpa only [Finset.mem_filter, and_true] using
        Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    · intro j _hj _hj_not
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hgeom :=
    Homogenization.sum_filter_triadicDepthWeight_le_geometric_inv
      β L (fun _j => True) hβ
  have hgeom_five :
      (1 - Real.rpow (3 : ℝ) (-β))⁻¹ ≤ 5 * β⁻¹ :=
    Homogenization.Book.Ch02.inv_one_sub_rpow_three_neg_le_five_inv hβ hβ_le
  calc
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)))
        =
      ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hsum_eq
    _ ≤
      ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
        Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hrange_le
    _ ≤ (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := hgeom
    _ ≤ 5 * β⁻¹ := hgeom_five

theorem expectedResponseJCubeSet_origin_eq_annealedResponseJAtScale
    {d : ℕ} (P : Ch04.RestrictionCoeffLaw d) (n : ℤ) (p q : Vec d) :
    Ch04.expectedResponseJCubeSet P (originCube d n) p q =
      Ch04.annealedResponseJAtScale P n p q := by
  rfl

theorem expectedResponseJCubeSet_origin_eq_origin_add_tauAtScale
    {d : ℕ} (P : Ch04.RestrictionCoeffLaw d) (m k : ℤ) (p q : Vec d) :
    Ch04.expectedResponseJCubeSet P (originCube d k) p q =
      Ch04.expectedResponseJCubeSet P (originCube d m) p q +
        tauAtScale P m k p q := by
  simp [expectedResponseJCubeSet_origin_eq_annealedResponseJAtScale, tauAtScale]

theorem tauAtScale_le_tauAtScale_of_left_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k n m : ℤ} (hk_nonneg : 0 ≤ k) (hkn : k ≤ n)
    (p q : Vec d) :
    tauAtScale P m n p q ≤ tauAtScale P m k p q := by
  have hn_nonneg : 0 ≤ n := hk_nonneg.trans hkn
  have hBlockN :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P := by
    have hn_toNat : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
    simpa [hn_toNat] using
      Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 (Int.toNat n)
  have hBlockK :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d k)) P := by
    have hk_toNat : ((Int.toNat k : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
    simpa [hk_toNat] using
      Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 (Int.toNat k)
  have hDescBlock :
      ∀ R, R ∈ descendantsAtScale (originCube d n) k →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkn hR hBlockK
  have htau_nk :
      0 ≤ tauAtScale P n k p q :=
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hstat hk_nonneg hkn p q hBlockN hDescBlock
  have hdecomp :
      tauAtScale P m k p q =
        tauAtScale P m n p q + tauAtScale P n k p q := by
    simp [tauAtScale]
  nlinarith

theorem coarseFluctuationTauSumAtScale_le_five_beta_inv_tauAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    coarseFluctuationTauSumAtScale hP hStruct hP4 k m e ≤
      5 * β⁻¹ * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := section53CoarseFluctuationBeta_le_sUpper hP4
    linarith [hle, hP4.sUpper_lt_one]
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
  have hweights :
      (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) ≤
          5 * β⁻¹ :=
    sum_Icc_betaWeight_le_five_beta_inv hkm_int hβ_pos hβ_le_one
  have htau_mk_nonneg :
      0 ≤ tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
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
    exact
      Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
        hP hstat hk_nonneg hkm_int p_e q_e hBlockM hDescBlock
  have hsum_le :
      (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            tauAtScale P (m : ℤ) n p_e q_e) ≤
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) *
            tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
    calc
      (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            tauAtScale P (m : ℤ) n p_e q_e)
          ≤
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_low : (k : ℤ) ≤ n := by
            have h := (Finset.mem_Icc.mp hn).1
            omega
          have hn_high : n ≤ (m : ℤ) := (Finset.mem_Icc.mp hn).2
          have htau_le :
              tauAtScale P (m : ℤ) n p_e q_e ≤
            tauAtScale P (m : ℤ) (k : ℤ) p_e q_e :=
            tauAtScale_le_tauAtScale_of_left_le
              hP hstat hStruct hP4
              (by exact_mod_cast Nat.zero_le k) hn_low p_e q_e
          exact mul_le_mul_of_nonneg_left htau_le
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ =
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) *
            tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
          rw [Finset.sum_mul]
  calc
    coarseFluctuationTauSumAtScale hP hStruct hP4 k m e =
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            tauAtScale P (m : ℤ) n p_e q_e) := by
          simp [coarseFluctuationTauSumAtScale, β, p_e, q_e]
    _ ≤
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) *
            tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := hsum_le
    _ ≤ (5 * β⁻¹) * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e :=
        mul_le_mul_of_nonneg_right hweights htau_mk_nonneg
    _ = 5 * β⁻¹ * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by ring

theorem exists_decay_absorption_const
    {β A : ℝ} (hβ : 0 < β) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : ℕ}, C ≤ (n : ℝ) →
        A * Real.rpow (3 : ℝ) (-2 * β * (n : ℝ)) ≤ 1 / 4 := by
  let r : ℝ := Real.rpow (3 : ℝ) (-2 * β)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (by nlinarith)
  have hA_one_pos : 0 < A + 1 := by linarith
  have heps_pos : 0 < (1 / 4 : ℝ) / (A + 1) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one heps_pos hr_lt_one
  refine ⟨N, by exact_mod_cast Nat.zero_le N, ?_⟩
  intro n hn
  have hN_le_n_nat : N ≤ n := by exact_mod_cast hn
  have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN_le_n_nat
  have hpow_eq :
      Real.rpow (3 : ℝ) (-2 * β * (N : ℝ)) = r ^ N := by
    calc
      Real.rpow (3 : ℝ) (-2 * β * (N : ℝ)) =
          Real.rpow (3 : ℝ) ((-2 * β) * (N : ℝ)) := by ring
      _ = Real.rpow (Real.rpow (3 : ℝ) (-2 * β)) (N : ℝ) :=
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-2 * β) (N : ℝ)
      _ = r ^ N := by
          simp [r, Real.rpow_natCast]
  have hdecay_le :
      Real.rpow (3 : ℝ) (-2 * β * (n : ℝ)) ≤
        Real.rpow (3 : ℝ) (-2 * β * (N : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
    nlinarith
  have hA_pow_le :
      A * r ^ N ≤ 1 / 4 := by
    have hpow_le : r ^ N ≤ (1 / 4 : ℝ) / (A + 1) := le_of_lt hN
    calc
      A * r ^ N ≤ A * ((1 / 4 : ℝ) / (A + 1)) :=
        mul_le_mul_of_nonneg_left hpow_le hA
      _ ≤ 1 / 4 := by
        field_simp [hA_one_pos.ne']
        nlinarith
  calc
    A * Real.rpow (3 : ℝ) (-2 * β * (n : ℝ)) ≤
        A * Real.rpow (3 : ℝ) (-2 * β * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay_le hA
    _ = A * r ^ N := by rw [hpow_eq]
    _ ≤ 1 / 4 := hA_pow_le

theorem section53CoarseFluctuationBetaCoreParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaCoreParams params := by
  have hgap : 0 < 1 - params.sUpper - params.sLower := by
    linarith [params.sum_lt_one]
  have hupper : 0 < params.sUpper := params.sUpper_pos
  have hlower : 0 < params.sLower := params.sLower_pos
  have hupper_gain : 0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sUpper]
  have hlower_gain : 0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCoreParams
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

theorem section53CoarseFluctuationBetaParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams
  nlinarith [section53CoarseFluctuationBetaCoreParams_pos params]

theorem self_le_half_add_of_le
    {x R : ℝ} (h : x ≤ (1 / 2 : ℝ) * x + R) :
    x ≤ 2 * R := by
  nlinarith

theorem coarseFluctuationYoungManuscriptRHSAtScale_eq_decomp
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C ε η : ℝ) (k m : ℕ) (e : Vec d) :
    coarseFluctuationYoungManuscriptRHSAtScale hP hStruct hP4 C ε η k m e =
      let β := section53CoarseFluctuationBeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let θ := thetaAtScale hP hStruct (m : ℤ)
      let scalarWeight := coarseFluctuationScalarWeightAtScale hP hStruct m
      let fluctuationSum := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
      let tauSum := coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
      let unitMomentWeight := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
      let responseMoment := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
      C *
          (η * Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e +
            η⁻¹ * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) +
        C * ε * (Real.sqrt θ - 1) ^ 2 +
          C * ε⁻¹ * β⁻¹ * θ * fluctuationSum +
            C * ε⁻¹ * (β ^ 2)⁻¹ * scalarWeight * tauSum +
              C * (hP4.xi : ℝ) * ε⁻¹ * (β ^ 3)⁻¹ *
                  Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                  unitMomentWeight * responseMoment +
                C * ε⁻¹ * (β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ) (-2 * β * ((m - k : ℕ) : ℝ)) *
                  scalarWeight * (θ - 1) := by
  unfold coarseFluctuationYoungManuscriptRHSAtScale
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem two_mul_sum_six_le
    {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : 2 * a₁ ≤ b₁) (h₂ : 2 * a₂ ≤ b₂)
    (h₃ : 2 * a₃ ≤ b₃) (h₄ : 2 * a₄ ≤ b₄)
    (h₅ : 2 * a₅ ≤ b₅) (h₆ : 2 * a₆ ≤ b₆) :
    2 * (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) ≤
      b₁ + b₂ + b₃ + b₄ + b₅ + b₆ := by
  nlinarith

theorem young_rhs_two_mul_le_sum_of_term_bounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C η : ℝ) (k m : ℕ) (e : Vec d)
    (B₁ B₂ B₃ B₄ B₅ B₆ : ℝ)
    (h₁ :
      2 *
          (C *
            (η *
                Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
                  (specialPAtScale hP hStruct (m : ℤ) e)
                  (specialQAtScale hP hStruct (m : ℤ) e) +
              η⁻¹ *
                tauAtScale P (m : ℤ) (k : ℤ)
                  (specialPAtScale hP hStruct (m : ℤ) e)
                  (specialQAtScale hP hStruct (m : ℤ) e))) ≤ B₁)
    (h₂ :
      2 *
          (C *
            (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^
              (2 : ℕ)) ≤ B₂)
    (h₃ :
      2 *
          (C * (section53CoarseFluctuationBeta hP4)⁻¹ *
            thetaAtScale hP hStruct (m : ℤ) *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) ≤ B₃)
    (h₄ :
      2 *
          (C * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
            coarseFluctuationScalarWeightAtScale hP hStruct m *
            coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) ≤ B₄)
    (h₅ :
      2 *
          (C * (hP4.xi : ℝ) *
            ((section53CoarseFluctuationBeta hP4) ^ 3)⁻¹ *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBeta hP4) * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) ≤ B₅)
    (h₆ :
      2 *
          (C * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
            Real.rpow (3 : ℝ)
              (-2 * section53CoarseFluctuationBeta hP4 *
                (((m - k : ℕ) : ℝ))) *
            coarseFluctuationScalarWeightAtScale hP hStruct m *
            (thetaAtScale hP hStruct (m : ℤ) - 1)) ≤ B₆) :
    2 *
        coarseFluctuationYoungManuscriptRHSAtScale
          hP hStruct hP4 C 1 η k m e ≤
      B₁ + B₂ + B₃ + B₄ + B₅ + B₆ := by
  rw [coarseFluctuationYoungManuscriptRHSAtScale_eq_decomp]
  simpa only [inv_one, one_mul, mul_one] using
    (two_mul_sum_six_le h₁ h₂ h₃ h₄ h₅ h₆)

theorem small_contrast_rest_sum_eq
    (J tauCoeff₁ tauCoeff₂ tau thetaTerm fluctTerm tailTerm : ℝ) :
    ((1 / 4 : ℝ) * J + tauCoeff₁ * tau) +
          thetaTerm + fluctTerm + tauCoeff₂ * tau + tailTerm +
        (1 / 4 : ℝ) * J =
      (1 / 2 : ℝ) * J +
        (fluctTerm + (tauCoeff₁ + tauCoeff₂) * tau + tailTerm + thetaTerm) := by
  ring

theorem small_contrast_rest_sum_terms_eq
    (J tauTerm₁ tauTerm₂ thetaTerm fluctTerm tailTerm : ℝ) :
    ((1 / 4 : ℝ) * J + tauTerm₁) + thetaTerm + fluctTerm + tauTerm₂ +
        tailTerm + (1 / 4 : ℝ) * J =
      (1 / 2 : ℝ) * J +
        (fluctTerm + (tauTerm₁ + tauTerm₂) + tailTerm + thetaTerm) := by
  ring

theorem absorb_quarter_terms
    {J tauTerm₁ tauTerm₂ thetaTerm fluctTerm tailTerm : ℝ}
    (h :
      J ≤
        ((1 / 4 : ℝ) * J + tauTerm₁) + thetaTerm + fluctTerm + tauTerm₂ +
          tailTerm + (1 / 4 : ℝ) * J) :
    J ≤ 2 * (fluctTerm + (tauTerm₁ + tauTerm₂) + tailTerm + thetaTerm) := by
  nlinarith
end

end Section56
end Ch05
end Book
end Homogenization
