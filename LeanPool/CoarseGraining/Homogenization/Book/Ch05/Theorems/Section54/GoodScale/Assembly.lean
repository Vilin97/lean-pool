/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.GoodScale.ScalarBounds

/-! # Assembly -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace GoodScale

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Assembly of the good-scale parameter bounds

This file assembles the scalar monotonicity, `(P4)`-supplied integrability, and
special-vector algebra into the manuscript-facing good-scale lemma.
-/

private theorem abs_sqrt_theta_sub_one_le_sqrt_theta_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| ≤
      Real.sqrt (thetaAtScale hP hStruct 0) := by
  have htheta_m0 :
      thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct 0 := by
    simpa using
      thetaAtScale_mono_of_P4 hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have htheta_one : 1 ≤ thetaAtScale hP hStruct (m : ℤ) :=
    one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hsqrt_one :
      1 ≤ Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt htheta_one
  have hsqrt_m0 :
      Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) ≤
        Real.sqrt (thetaAtScale hP hStruct 0) :=
    Real.sqrt_le_sqrt htheta_m0
  have habs :
      |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| =
        Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1 :=
    abs_of_nonneg (sub_nonneg.mpr hsqrt_one)
  calc
    |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| =
        Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1 := habs
    _ ≤ Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) := by linarith
    _ ≤ Real.sqrt (thetaAtScale hP hStruct 0) := hsqrt_m0

private theorem sigmaHat_inv_mul_barSigma_zero_le_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ)) :
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        hP.barSigmaAtScale hStruct 0 ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  let theta_m := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_pos : 0 < sigma := by
    simpa [sigma] using sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma : sigma = Real.sqrt (b * c) := by rfl
  have htheta_m : theta_m = b * c⁻¹ := by rfl
  have hdiv :
      b * sigma⁻¹ = Real.sqrt theta_m :=
    barSigma_mul_inv_sigma_eq_sqrt_theta hb hc hsigma htheta_m
  have htheta_m0 :
      thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct 0 := by
    simpa using
      thetaAtScale_mono_of_P4 hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have hsqrt_m0 :
      Real.sqrt theta_m ≤ Real.sqrt (thetaAtScale hP hStruct 0) := by
    simpa [theta_m] using Real.sqrt_le_sqrt htheta_m0
  have hfactor_nonneg : 0 ≤ 1 + delta := by linarith
  have hscale :
      sigma⁻¹ * hP.barSigmaAtScale hStruct 0 ≤
        sigma⁻¹ * ((1 + delta) * b) := by
    exact mul_le_mul_of_nonneg_left (by simpa [b] using hgood_upper)
      (inv_pos.mpr hsigma_pos).le
  calc
    sigma⁻¹ * hP.barSigmaAtScale hStruct 0 ≤
        sigma⁻¹ * ((1 + delta) * b) := hscale
    _ = (1 + delta) * (b * sigma⁻¹) := by ring
    _ = (1 + delta) * Real.sqrt theta_m := by rw [hdiv]
    _ ≤ (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) :=
      mul_le_mul_of_nonneg_left hsqrt_m0 hfactor_nonneg

private theorem sigmaHat_mul_barSigmaStar_inv_zero_le_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (m : ℕ)
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    sigmaHatAtScale hP hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  let theta_m := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_pos : 0 < sigma := by
    simpa [sigma] using sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma : sigma = Real.sqrt (b * c) := by rfl
  have htheta_m : theta_m = b * c⁻¹ := by rfl
  have hdiv :
      sigma * c⁻¹ = Real.sqrt theta_m :=
    sigma_mul_inv_star_eq_sqrt_theta hb hc hsigma htheta_m
  have htheta_m0 :
      thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct 0 := by
    simpa using
      thetaAtScale_mono_of_P4 hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have hsqrt_m0 :
      Real.sqrt theta_m ≤ Real.sqrt (thetaAtScale hP hStruct 0) := by
    simpa [theta_m] using Real.sqrt_le_sqrt htheta_m0
  have hfactor_nonneg : 0 ≤ 1 + delta := by linarith
  have hscale :
      sigma * (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        sigma * ((1 + delta) * c⁻¹) := by
    exact mul_le_mul_of_nonneg_left (by simpa [c] using hgood_lower) hsigma_pos.le
  calc
    sigma * (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        sigma * ((1 + delta) * c⁻¹) := hscale
    _ = (1 + delta) * (sigma * c⁻¹) := by ring
    _ = (1 + delta) * Real.sqrt theta_m := by rw [hdiv]
    _ ≤ (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) :=
      mul_le_mul_of_nonneg_left hsqrt_m0 hfactor_nonneg

/-- Section 5.4 good-scale parameter bounds.  At a scale where both scalar
coefficient chains are nearly stationary, the special vectors have controlled
centering, response, and additivity defect bounds. -/
theorem goodScaleParameterBounds_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    Ch02.vecNorm
        (Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (1 / 2 : ℝ) • p0_e) =
      |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| ∧
    Ch02.vecNorm
        (Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (-(1 / 2 : ℝ)) • q0_e) =
      |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| ∧
    |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| ≤
      Real.sqrt (thetaAtScale hP hStruct 0) ∧
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        hP.barSigmaAtScale hStruct 0 ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) ∧
    sigmaHatAtScale hP hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) ∧
    (∀ k : ℕ, k ≤ m →
      Ch04.annealedResponseJAtScale P (k : ℤ) p_e q_e ≤
        (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) ∧
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e ≤
        delta * Real.sqrt (thetaAtScale hP hStruct 0)) := by
  classical
  dsimp only
  have hp_norm :=
    scaled_specialP_centering_vecNorm_eq_of_P4 hP hStruct hP4 m e he
  have hq_norm :=
    scaled_specialQ_centering_vecNorm_eq_of_P4 hP hStruct hP4 m e he
  have hcenter_bound :=
    abs_sqrt_theta_sub_one_le_sqrt_theta_zero_of_P4 hP hStruct hP4 m
  have hcompare_upper :=
    sigmaHat_inv_mul_barSigma_zero_le_of_good hP hStruct hP4 hdelta_pos m hgood_upper
  have hcompare_lower :=
    sigmaHat_mul_barSigmaStar_inv_zero_le_of_good hP hStruct hP4 hdelta_pos m hgood_lower
  refine ⟨hp_norm, hq_norm, hcenter_bound, hcompare_upper, hcompare_lower, ?_⟩
  intro k hk
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  let sqrtTheta0 := Real.sqrt (thetaAtScale hP hStruct 0)
  have heSq : vecNormSq e = 1 := vecNormSq_eq_one_of_vecNorm_eq_one he
  have hchain_k0 := Pigeonhole.scalarChain_of_P4 hP hStruct hP4 (Nat.zero_le k)
  have hchain_mk := Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hk
  have hsigma_pos : 0 < sigma := by
    simpa [sigma] using sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_inv_nonneg : 0 ≤ sigma⁻¹ := (inv_pos.mpr hsigma_pos).le
  have hsigma_nonneg : 0 ≤ sigma := hsigma_pos.le
  have hfactor_nonneg : 0 ≤ 1 + delta := by linarith
  have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
  have hsqrtTheta0_nonneg : 0 ≤ sqrtTheta0 := by
    dsimp [sqrtTheta0]
    exact Real.sqrt_nonneg _
  have hB_nonneg : 0 ≤ (1 + delta) * sqrtTheta0 :=
    mul_nonneg hfactor_nonneg hsqrtTheta0_nonneg
  have hbar_k_le_zero :
      hP.barSigmaAtScale hStruct (k : ℤ) ≤
        hP.barSigmaAtScale hStruct 0 := by
    simpa using hchain_k0.2.2
  have hstarInv_k_le_zero :
      (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ := by
    simpa using hchain_k0.2.1
  have hbar_m_le_k :
      hP.barSigmaAtScale hStruct (m : ℤ) ≤
        hP.barSigmaAtScale hStruct (k : ℤ) := by
    simpa using hchain_mk.2.2
  have hstarInv_m_le_k :
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ := by
    simpa using hchain_mk.2.1
  have hscaled_bar_k :
      sigma⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ) ≤
        (1 + delta) * sqrtTheta0 := by
    calc
      sigma⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ) ≤
          sigma⁻¹ * hP.barSigmaAtScale hStruct 0 :=
        mul_le_mul_of_nonneg_left hbar_k_le_zero hsigma_inv_nonneg
      _ ≤ (1 + delta) * sqrtTheta0 := by simpa [sigma, sqrtTheta0] using hcompare_upper
  have hscaled_star_k :
      sigma * (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
        (1 + delta) * sqrtTheta0 := by
    calc
      sigma * (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
          sigma * (hP.barSigmaStarAtScale hStruct 0)⁻¹ :=
        mul_le_mul_of_nonneg_left hstarInv_k_le_zero hsigma_nonneg
      _ ≤ (1 + delta) * sqrtTheta0 := by simpa [sigma, sqrtTheta0] using hcompare_lower
  have hJ_formula :
      Ch04.annealedResponseJAtScale P (k : ℤ) p_e q_e =
        (1 / 2 : ℝ) * sigma⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ) +
          (1 / 2 : ℝ) * sigma *
            (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ - 1 := by
    have hBlock_k :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
    calc
      Ch04.annealedResponseJAtScale P (k : ℤ) p_e q_e =
          expectedJScalarFormula hP hStruct (k : ℤ) p_e q_e := by
        rw [Section52.annealedResponseJAtScale_eq_expectedJScalarFormula
          hP hStruct (k : ℤ) p_e q_e hBlock_k]
      _ = (1 / 2 : ℝ) * sigma⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ) +
            (1 / 2 : ℝ) * sigma *
              (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ - 1 := by
        simpa [p_e, q_e, sigma] using
          expectedJScalarFormula_special_eq_of_P4 hP hStruct hP4 m k e heSq
  have hJ_bound :
      Ch04.annealedResponseJAtScale P (k : ℤ) p_e q_e ≤
        (1 + delta) * sqrtTheta0 := by
    rw [hJ_formula]
    nlinarith [hscaled_bar_k, hscaled_star_k, hB_nonneg]
  have hbar_diff_le :
      hP.barSigmaAtScale hStruct (k : ℤ) -
          hP.barSigmaAtScale hStruct (m : ℤ) ≤
        delta * hP.barSigmaAtScale hStruct (m : ℤ) := by
    have hkm :
        hP.barSigmaAtScale hStruct (k : ℤ) ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ) :=
      le_trans hbar_k_le_zero hgood_upper
    nlinarith
  have hstarInv_diff_le :
      (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤
        delta * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    have hkm :
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
          (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
      le_trans hstarInv_k_le_zero hgood_lower
    nlinarith
  have htheta_m0 :
      thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct 0 := by
    simpa using
      thetaAtScale_mono_of_P4 hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  let theta_m := thetaAtScale hP hStruct (m : ℤ)
  have hsqrt_m0 :
      Real.sqrt theta_m ≤ sqrtTheta0 := by
    simpa [theta_m, sqrtTheta0] using Real.sqrt_le_sqrt htheta_m0
  let b_m := hP.barSigmaAtScale hStruct (m : ℤ)
  let c_m := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hb_m : 0 < b_m := by
    simpa [b_m] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc_m : 0 < c_m := by
    simpa [c_m] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_eq : sigma = Real.sqrt (b_m * c_m) := by rfl
  have htheta_eq : theta_m = b_m * c_m⁻¹ := by rfl
  have hscaled_bar_m_eq :
      sigma⁻¹ * b_m = Real.sqrt theta_m := by
    rw [mul_comm]
    exact barSigma_mul_inv_sigma_eq_sqrt_theta hb_m hc_m hsigma_eq htheta_eq
  have hscaled_star_m_eq :
      sigma * c_m⁻¹ = Real.sqrt theta_m :=
    sigma_mul_inv_star_eq_sqrt_theta hb_m hc_m hsigma_eq htheta_eq
  have hscaled_bar_diff :
      sigma⁻¹ *
          (hP.barSigmaAtScale hStruct (k : ℤ) -
            hP.barSigmaAtScale hStruct (m : ℤ)) ≤
        delta * sqrtTheta0 := by
    calc
      sigma⁻¹ *
          (hP.barSigmaAtScale hStruct (k : ℤ) -
            hP.barSigmaAtScale hStruct (m : ℤ)) ≤
          sigma⁻¹ * (delta * hP.barSigmaAtScale hStruct (m : ℤ)) :=
        mul_le_mul_of_nonneg_left hbar_diff_le hsigma_inv_nonneg
      _ = delta * (sigma⁻¹ * b_m) := by ring
      _ = delta * Real.sqrt theta_m := by rw [hscaled_bar_m_eq]
      _ ≤ delta * sqrtTheta0 :=
        mul_le_mul_of_nonneg_left hsqrt_m0 hdelta_nonneg
  have hscaled_star_diff :
      sigma *
          ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) ≤
        delta * sqrtTheta0 := by
    calc
      sigma *
          ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) ≤
          sigma * (delta * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :=
        mul_le_mul_of_nonneg_left hstarInv_diff_le hsigma_nonneg
      _ = delta * (sigma * c_m⁻¹) := by ring
      _ = delta * Real.sqrt theta_m := by rw [hscaled_star_m_eq]
      _ ≤ delta * sqrtTheta0 :=
        mul_le_mul_of_nonneg_left hsqrt_m0 hdelta_nonneg
  have htau_formula :
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e =
        (1 / 2 : ℝ) * sigma⁻¹ *
            (hP.barSigmaAtScale hStruct (k : ℤ) -
              hP.barSigmaAtScale hStruct (m : ℤ)) +
          (1 / 2 : ℝ) * sigma *
            ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
    have hBlock_m :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
    have hBlock_k :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
    calc
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e =
          tauScalarFormula hP hStruct (m : ℤ) (k : ℤ) p_e q_e := by
        rw [Section52.tauAtScale_eq_tauScalarFormula
          hP hStruct (m : ℤ) (k : ℤ) p_e q_e hBlock_m hBlock_k]
      _ = (1 / 2 : ℝ) * sigma⁻¹ *
            (hP.barSigmaAtScale hStruct (k : ℤ) -
              hP.barSigmaAtScale hStruct (m : ℤ)) +
          (1 / 2 : ℝ) * sigma *
            ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
        simpa [p_e, q_e, sigma] using
          tauScalarFormula_special_eq_of_P4 hP hStruct hP4 m k e heSq
  have htau_bound :
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e ≤
        delta * sqrtTheta0 := by
    have hbar_half :
        (1 / 2 : ℝ) *
            (sigma⁻¹ *
              (hP.barSigmaAtScale hStruct (k : ℤ) -
                hP.barSigmaAtScale hStruct (m : ℤ))) ≤
          (1 / 2 : ℝ) * (delta * sqrtTheta0) :=
      mul_le_mul_of_nonneg_left hscaled_bar_diff (by norm_num)
    have hstar_half :
        (1 / 2 : ℝ) *
            (sigma *
              ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
                (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)) ≤
          (1 / 2 : ℝ) * (delta * sqrtTheta0) :=
      mul_le_mul_of_nonneg_left hscaled_star_diff (by norm_num)
    rw [htau_formula]
    calc
      (1 / 2 : ℝ) * sigma⁻¹ *
            (hP.barSigmaAtScale hStruct (k : ℤ) -
              hP.barSigmaAtScale hStruct (m : ℤ)) +
          (1 / 2 : ℝ) * sigma *
            ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) =
          (1 / 2 : ℝ) *
              (sigma⁻¹ *
                (hP.barSigmaAtScale hStruct (k : ℤ) -
                  hP.barSigmaAtScale hStruct (m : ℤ))) +
            (1 / 2 : ℝ) *
              (sigma *
                ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
                  (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)) := by
        ring
      _ ≤
          (1 / 2 : ℝ) * (delta * sqrtTheta0) +
            (1 / 2 : ℝ) * (delta * sqrtTheta0) :=
        add_le_add hbar_half hstar_half
      _ = delta * sqrtTheta0 := by ring
  exact ⟨hJ_bound, htau_bound⟩

end

end GoodScale
end Section54
end Ch05
end Book
end Homogenization
