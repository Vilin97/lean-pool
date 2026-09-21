/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CoarseFluctuationInput
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CoarseFullBlock
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ResponseMoment
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScaleCompression

/-! # RHSCompression -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Compressing the Section 5.3 RHS at a good scale

This file turns the public Section 5.3 coarse-fluctuation RHS, specialized to
`k = 0` and to the Section 5.4 special vectors, into the one-step scale
quantity `(\epsilon + \epsilon^{-1}\sqrt\delta) \Theta_0`.
-/

open Section53.JUpperBoundCoarseFluctuations

private theorem expectedResponseJCubeSet_nonneg
    {d : ℕ} (P : Ch04.RestrictionCoeffLaw d) (Q : TriadicCube d) (p q : Vec d) :
    0 ≤ Ch04.expectedResponseJCubeSet P Q p q := by
  dsimp [Ch04.expectedResponseJCubeSet]
  exact integral_nonneg fun a => by
    exact Ch04.restrictionResponseJObservableCubeSet_nonneg Q p q a

theorem thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    thetaAtScale hP hStruct (0 : ℤ) ≤
      widetildeThetaAtScale P (0 : ℤ) hP4 := by
  have hξ_one : 1 ≤ hP4.xi := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  exact
    Section52.thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
      hP hStruct hP4
      (fun n => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n)
      (fun n => Section52.upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 n)
      (fun n => Section52.lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 n)
      0

private theorem sigmaHatAtScale_le_LambdaMomentAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    sigmaHatAtScale hP hStruct (m : ℤ) ≤
      Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
  let b_m := hP.barSigmaAtScale hStruct (m : ℤ)
  let c_m := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  have hb_m_pos : 0 < b_m := by
    simpa [b_m] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc_m_le_b_m : c_m ≤ b_m := by
    simpa [b_m, c_m] using
      VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hσ_le_bm :
      sigmaHatAtScale hP hStruct (m : ℤ) ≤ b_m := by
    calc
      sigmaHatAtScale hP hStruct (m : ℤ) =
          Real.sqrt (b_m * c_m) := rfl
      _ ≤ Real.sqrt (b_m * b_m) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hc_m_le_b_m hb_m_pos.le)
      _ = b_m := by
          rw [show b_m * b_m = b_m ^ (2 : ℕ) by ring,
            Real.sqrt_sq_eq_abs, abs_of_pos hb_m_pos]
  have hbm_le_b0 : b_m ≤ b0 := by
    simpa [b_m, b0] using
      (Pigeonhole.scalarChain_of_P4 hP hStruct hP4 (n := 0) (m := m)
        (Nat.zero_le m)).2.2
  have hb0_le_L0 : b0 ≤ L0 := by
    have hξ_one : 1 ≤ hP4.xi := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
    simpa [b0, L0] using
      hP.barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
        hStruct hP4.sUpper_pos hP4.sLower_pos hξ_one
        (fun n => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n)
        (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (n : ℤ)) hP4.sUpper_pos)
        (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (n : ℤ)) hP4.sLower_pos)
        (fun n => Section52.upperFactorPowerIntegrableAtScale_from_P4
          hP hStruct hP4 n)
        (fun n => Section52.lowerFactorPowerIntegrableAtScale_from_P4
          hP hStruct hP4 n)
        0
  exact hσ_le_bm.trans (hbm_le_b0.trans hb0_le_L0)

private theorem inv_sigmaHatAtScale_le_lambdaInvMomentAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ ≤
      Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
  let b_m := hP.barSigmaAtScale hStruct (m : ℤ)
  let c_m := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  have hb_m_pos : 0 < b_m := by
    simpa [b_m] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc_m_pos : 0 < c_m := by
    simpa [c_m] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hc_m_le_b_m : c_m ≤ b_m := by
    simpa [b_m, c_m] using
      VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hc_m_le_σ :
      c_m ≤ sigmaHatAtScale hP hStruct (m : ℤ) := by
    calc
      c_m = Real.sqrt (c_m * c_m) := by
          rw [show c_m * c_m = c_m ^ (2 : ℕ) by ring,
            Real.sqrt_sq_eq_abs, abs_of_pos hc_m_pos]
      _ ≤ Real.sqrt (b_m * c_m) := by
          exact Real.sqrt_le_sqrt
            (by
              have hmul := mul_le_mul_of_nonneg_right hc_m_le_b_m hc_m_pos.le
              simpa [mul_comm] using hmul)
      _ = sigmaHatAtScale hP hStruct (m : ℤ) := rfl
  have hσ_pos : 0 < sigmaHatAtScale hP hStruct (m : ℤ) := by
    simpa using GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ_inv_le_cm_inv :
      (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ ≤ c_m⁻¹ :=
    (inv_le_inv₀ hσ_pos hc_m_pos).2 hc_m_le_σ
  have hcm_inv_le_c0_inv : c_m⁻¹ ≤ c0⁻¹ := by
    simpa [c_m, c0] using
      (Pigeonhole.scalarChain_of_P4 hP hStruct hP4 (n := 0) (m := m)
        (Nat.zero_le m)).2.1
  have hc0_inv_le_l0 : c0⁻¹ ≤ l0 := by
    have hξ_one : 1 ≤ hP4.xi := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
    simpa [c0, l0] using
      hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
        hStruct hP4.sUpper_pos hP4.sLower_pos hξ_one
        (fun n => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n)
        (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (n : ℤ)) hP4.sUpper_pos)
        (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (n : ℤ)) hP4.sLower_pos)
        (fun n => Section52.upperFactorPowerIntegrableAtScale_from_P4
          hP hStruct hP4 n)
        (fun n => Section52.lowerFactorPowerIntegrableAtScale_from_P4
          hP hStruct hP4 n)
        0
  exact hσ_inv_le_cm_inv.trans (hcm_inv_le_c0_inv.trans hc0_inv_le_l0)

theorem coarseFluctuationUnitMomentWeightAtScale_le_two_widetildeTheta_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m ≤
      2 * widetildeThetaAtScale P (0 : ℤ) hP4 := by
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  have hσ_le_L0 : σ ≤ L0 := by
    simpa [σ, L0] using
      sigmaHatAtScale_le_LambdaMomentAtScale_zero_of_P4 hP hStruct hP4 m
  have hσ_inv_le_l0 : σ⁻¹ ≤ l0 := by
    simpa [σ, l0] using
      inv_sigmaHatAtScale_le_lambdaInvMomentAtScale_zero_of_P4 hP hStruct hP4 m
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  calc
    coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m =
        σ * l0 + σ⁻¹ * L0 := by
          simp [coarseFluctuationUnitMomentWeightAtScale, σ, L0, l0]
    _ ≤ L0 * l0 + l0 * L0 :=
        add_le_add
          (mul_le_mul_of_nonneg_right hσ_le_L0 hl0_nonneg)
          (mul_le_mul_of_nonneg_right hσ_inv_le_l0 hL0_nonneg)
    _ = 2 * widetildeThetaAtScale P (0 : ℤ) hP4 := by
        simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]
        ring

theorem oneStepScaleSeparation_m_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta)
    (hsep :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ)) :
    0 < m := by
  have hC_pos : 0 < C :=
    lt_of_lt_of_le (oneStepScaleSeparationConst_pos hP4) hC
  have hxi_pos : 0 < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have htheta_tilde_nonneg :
      0 ≤ widetildeThetaAtScale P (0 : ℤ) hP4 := by
    simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
    exact mul_nonneg
      (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
      (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)
  have harg_gt_one :
      1 <
        2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4 := by
    have hprod_nonneg :
        0 ≤ delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4 :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hdelta_pos.le) hxi_pos.le)
        htheta_tilde_nonneg
    linarith
  have hlog_pos :
      0 <
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) :=
    Real.log_pos harg_gt_one
  have hleft_pos :
      0 <
        C * (hP4.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) :=
    mul_pos (mul_pos hC_pos hxi_pos) hlog_pos
  have hm_real : 0 < (m : ℝ) := lt_of_lt_of_le hleft_pos hsep
  exact_mod_cast hm_real

private theorem sqrt_mul_sqrt_le_two_sqrt_delta_mul_theta
    {delta theta A B : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (htheta_one : 1 ≤ theta)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hA_le : A ≤ delta * Real.sqrt theta)
    (hB_le : B ≤ (1 + delta) * Real.sqrt theta) :
    Real.sqrt A * Real.sqrt B ≤ 2 * Real.sqrt delta * theta := by
  have htheta_nonneg : 0 ≤ theta := le_trans zero_le_one htheta_one
  have hsqrttheta_nonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg theta
  have hB_le_two : B ≤ 2 * Real.sqrt theta := by
    have hcoeff : 1 + delta ≤ 2 := by linarith
    exact hB_le.trans (mul_le_mul_of_nonneg_right hcoeff hsqrttheta_nonneg)
  have hAB :
      A * B ≤ (delta * Real.sqrt theta) * (2 * Real.sqrt theta) :=
    mul_le_mul hA_le hB_le_two hB_nonneg
      (mul_nonneg hdelta_pos.le hsqrttheta_nonneg)
  have hsqrt_sq : (Real.sqrt theta) ^ (2 : ℕ) = theta :=
    Real.sq_sqrt htheta_nonneg
  have hleft_sq :
      (Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) = A * B := by
    rw [mul_pow, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
  have hright_nonneg : 0 ≤ 2 * Real.sqrt delta * theta := by
    positivity
  have hsq :
      (Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) ≤
        (2 * Real.sqrt delta * theta) ^ (2 : ℕ) := by
    rw [hleft_sq]
    have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
    have hsqrtdelta_sq : (Real.sqrt delta) ^ (2 : ℕ) = delta :=
      Real.sq_sqrt hdelta_nonneg
    calc
      A * B ≤ (delta * Real.sqrt theta) * (2 * Real.sqrt theta) := hAB
      _ = 2 * delta * (Real.sqrt theta) ^ (2 : ℕ) := by
          ring_nf
      _ = 2 * delta * theta := by
          rw [hsqrt_sq]
      _ ≤ 4 * delta * theta ^ (2 : ℕ) := by
          have hθ_le_θsq : theta ≤ theta ^ (2 : ℕ) := by
            nlinarith
          nlinarith
      _ = (2 * Real.sqrt delta * theta) ^ (2 : ℕ) := by
          rw [mul_pow, mul_pow, hsqrtdelta_sq]
          ring
  exact le_of_sq_le_sq hsq hright_nonneg

private theorem centerTerm_le_theta_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ (2 : ℕ) ≤
      thetaAtScale hP hStruct (0 : ℤ) := by
  have htheta_m0 :
      thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      GoodScale.thetaAtScale_mono_of_P4 hP hStruct hP4
        (n := 0) (m := m) (Nat.zero_le m)
  have htheta_m_one : 1 ≤ thetaAtScale hP hStruct (m : ℤ) :=
    GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have htheta0_nonneg :
      0 ≤ thetaAtScale hP hStruct (0 : ℤ) :=
    le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hsqrt_m_one :
      1 ≤ Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) :=
    Real.one_le_sqrt.mpr htheta_m_one
  have hsqrt_m0 :
      Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) ≤
        Real.sqrt (thetaAtScale hP hStruct (0 : ℤ)) :=
    Real.sqrt_le_sqrt htheta_m0
  have hterm_nonneg :
      0 ≤ Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1 := by
    linarith
  have hterm_le :
      Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1 ≤
        Real.sqrt (thetaAtScale hP hStruct (0 : ℤ)) := by
    linarith
  have hsqrt_sq :
      (Real.sqrt (thetaAtScale hP hStruct (0 : ℤ))) ^ (2 : ℕ) =
        thetaAtScale hP hStruct (0 : ℤ) :=
    Real.sq_sqrt htheta0_nonneg
  have hsquare :=
    pow_le_pow_left₀ hterm_nonneg hterm_le 2
  rw [hsqrt_sq] at hsquare
  exact hsquare

private theorem thetaAtScale_m_le_thetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    thetaAtScale hP hStruct (m : ℤ) ≤ thetaAtScale hP hStruct (0 : ℤ) := by
  simpa using
    GoodScale.thetaAtScale_mono_of_P4 hP hStruct hP4
      (n := 0) (m := m) (Nat.zero_le m)

private theorem thetaAtScale_m_sub_one_le_thetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    thetaAtScale hP hStruct (m : ℤ) - 1 ≤
      thetaAtScale hP hStruct (0 : ℤ) := by
  have hmono := thetaAtScale_m_le_thetaAtScale_zero_of_P4 hP hStruct hP4 m
  linarith

private theorem sqrt_thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    Real.sqrt (thetaAtScale hP hStruct (0 : ℤ)) ≤
      widetildeThetaAtScale P (0 : ℤ) hP4 :=
  (sqrt_thetaAtScale_zero_le_thetaAtScale_zero_of_P4 hP hStruct hP4).trans
    (thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4 hP hStruct hP4)

private theorem tauAtScale_zero_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ)
    (p q : Vec d) :
    0 ≤ tauAtScale P (m : ℤ) (0 : ℤ) p q := by
  have hParent :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hOrigin0 :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 0
  refine
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct.stationary (by norm_num) (by exact_mod_cast Nat.zero_le m)
      p q hParent ?_
  intro R hR
  exact
    hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
      hStruct.stationary (by norm_num)
      (by exact_mod_cast Nat.zero_le m) hR hOrigin0

private theorem firstCoarseRhsTerm_le_two_sqrt_delta_theta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Real.sqrt (tauAtScale P (m : ℤ) (0 : ℤ) p_e q_e) *
        Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (0 : ℤ)) p_e q_e) ≤
      2 * Real.sqrt delta * thetaAtScale hP hStruct (0 : ℤ) := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have htheta_one :
      1 ≤ thetaAtScale hP hStruct (0 : ℤ) :=
    one_le_thetaAtScale_zero_of_P4 hP hStruct hP4
  have htau_nonneg :
      0 ≤ tauAtScale P (m : ℤ) (0 : ℤ) p_e q_e :=
    tauAtScale_zero_nonneg_of_P4 hP hStruct hP4 m p_e q_e
  have hJ_nonneg :
      0 ≤ Ch04.expectedResponseJCubeSet P (originCube d (0 : ℤ)) p_e q_e :=
    expectedResponseJCubeSet_nonneg P (originCube d (0 : ℤ)) p_e q_e
  have htau_le :
      tauAtScale P (m : ℤ) (0 : ℤ) p_e q_e ≤
        delta * Real.sqrt (thetaAtScale hP hStruct 0) := by
    simpa [p_e, q_e] using
      goodScale_tau_le hP hStruct hP4 hdelta_pos hdelta_le
        (m := m) (j := 0) (Nat.zero_le m)
        hgood_upper hgood_lower e he
  have hJ_le :
      Ch04.expectedResponseJCubeSet P (originCube d (0 : ℤ)) p_e q_e ≤
        (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
    have h :=
      goodScale_J_zero_le hP hStruct hP4 hdelta_pos hdelta_le
        (m := m) hgood_upper hgood_lower e he
    simpa [p_e, q_e, Ch04.expectedResponseJCubeSet,
      Ch04.annealedResponseJAtScale, Ch04.responseJAtScale] using h
  exact
    sqrt_mul_sqrt_le_two_sqrt_delta_mul_theta
      hdelta_pos hdelta_le htheta_one htau_nonneg hJ_nonneg htau_le hJ_le

private theorem responseMomentTail_le_four_sqrt_delta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (hsep :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ))
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let D :=
      Real.rpow (3 : ℝ)
        (-(section53CoarseFluctuationBeta hP4) * (m : ℝ))
    D * coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e ≤
      4 * Real.sqrt delta := by
  dsimp only
  let D :=
    Real.rpow (3 : ℝ)
      (-(section53CoarseFluctuationBeta hP4) * (m : ℝ))
  let T := widetildeThetaAtScale P (0 : ℤ) hP4
  let U := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
  let R := coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hU_nonneg : 0 ≤ U := by
    simpa [U] using
      coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m
  have hU_le : U ≤ 2 * T := by
    simpa [U, T] using
      coarseFluctuationUnitMomentWeightAtScale_le_two_widetildeTheta_zero
        hP hStruct hP4 m
  have hUR_le_sq : U * R ≤ U ^ (2 : ℕ) := by
    simpa [U, R] using
      coarseFluctuationUnitMomentWeight_mul_responseMoment_zero_le_sq
        hP hStruct hP4 m e he
  have hU_sq_le : U ^ (2 : ℕ) ≤ (2 * T) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hU_nonneg hU_le 2
  have htail :
      D * T ^ (2 : ℕ) ≤ Real.sqrt delta := by
    simpa [D, T] using
      oneStepScaleSeparation_absorbs_section53Beta_widetildeThetaSq
        hP4 hC hdelta_pos hdelta_le hsep
  calc
    D * U * R = D * (U * R) := by ring
    _ ≤ D * U ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hUR_le_sq hD_nonneg
    _ ≤ D * (2 * T) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hU_sq_le hD_nonneg
    _ = 4 * (D * T ^ (2 : ℕ)) := by ring
    _ ≤ 4 * Real.sqrt delta :=
        mul_le_mul_of_nonneg_left htail (by norm_num)

private theorem lowScaleTail_le_three_sqrt_delta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (hsep :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ))
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let D :=
      Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ)))
    let θ := thetaAtScale hP hStruct (m : ℤ)
    D * coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1) ≤
      3 * Real.sqrt delta := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let D2 := Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ)))
  let D1 := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let T := widetildeThetaAtScale P (0 : ℤ) hP4
  let θ0 := thetaAtScale hP hStruct (0 : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let S := coarseFluctuationScalarWeightAtScale hP hStruct m
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hD2_nonneg : 0 ≤ D2 := by
    dsimp [D2]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hD2_le_D1 : D2 ≤ D1 := by
    dsimp [D1, D2, β]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hβ_pos' :
        0 < section53CoarseFluctuationBeta hP4 := by
      simpa [β] using hβ_pos
    nlinarith [hβ_pos', hm_nonneg]
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using
      coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hT_nonneg : 0 ≤ T := by
    simpa [T, widetildeThetaAtScale, Ch04.widetildeThetaAtScale] using
      mul_nonneg
        (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
        (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)
  have hθ0_nonneg : 0 ≤ θ0 := by
    dsimp [θ0]
    exact le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hsqrtθ0_le_T : Real.sqrt θ0 ≤ T := by
    simpa [θ0, T] using
      sqrt_thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
        hP hStruct hP4
  have hθ0_le_T : θ0 ≤ T := by
    simpa [θ0, T] using
      thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
        hP hStruct hP4
  have hS_le_T : S ≤ 3 * T := by
    have hS_le_sqrt :
        S ≤ 3 * Real.sqrt θ0 := by
      have h :=
        goodScale_oneStepScalarWeight_le hP hStruct hP4
          hdelta_pos hdelta_le hgood_upper hgood_lower e he
      simpa [S, θ0, coarseFluctuationScalarWeightAtScale_eq_oneStepScalarWeightAtScale]
        using h
    calc
      S ≤ 3 * Real.sqrt θ0 := hS_le_sqrt
      _ ≤ 3 * T := mul_le_mul_of_nonneg_left hsqrtθ0_le_T (by norm_num)
  have hθ_sub_nonneg : 0 ≤ θ - 1 := by
    have hθ_one : 1 ≤ θ := by
      simpa [θ] using GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m
    linarith
  have hθ_sub_le_T : θ - 1 ≤ T := by
    have hleθ0 :
        θ - 1 ≤ θ0 := by
      simpa [θ, θ0] using
        thetaAtScale_m_sub_one_le_thetaAtScale_zero_of_P4 hP hStruct hP4 m
    exact hleθ0.trans hθ0_le_T
  have htail :
      D1 * T ^ (2 : ℕ) ≤ Real.sqrt delta := by
    simpa [D1, T] using
      oneStepScaleSeparation_absorbs_section53Beta_widetildeThetaSq
        hP4 hC hdelta_pos hdelta_le hsep
  calc
    D2 * S * (θ - 1) = D2 * (S * (θ - 1)) := by ring
    _ ≤ D2 * ((3 * T) * T) := by
        refine mul_le_mul_of_nonneg_left ?_ hD2_nonneg
        exact mul_le_mul hS_le_T hθ_sub_le_T hθ_sub_nonneg
          (mul_nonneg (by norm_num) hT_nonneg)
    _ = 3 * (D2 * T ^ (2 : ℕ)) := by ring
    _ ≤ 3 * (D1 * T ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hD2_le_D1 (sq_nonneg T)) (by norm_num)
    _ ≤ 3 * Real.sqrt delta :=
        mul_le_mul_of_nonneg_left htail (by norm_num)

private theorem sqrt_delta_mul_theta_le_compressionTarget
    {delta epsilon theta : ℝ}
    (_hdelta_nonneg : 0 ≤ delta) (hepsilon_pos : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1) (htheta_nonneg : 0 ≤ theta) :
    Real.sqrt delta * theta ≤
      (epsilon + epsilon⁻¹ * Real.sqrt delta) * theta := by
  have hinv_ge_one : 1 ≤ epsilon⁻¹ := (one_le_inv₀ hepsilon_pos).2 hepsilon_le
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hmain : Real.sqrt delta ≤ epsilon + epsilon⁻¹ * Real.sqrt delta := by
    have hmul : Real.sqrt delta ≤ epsilon⁻¹ * Real.sqrt delta :=
      by simpa using mul_le_mul_of_nonneg_right hinv_ge_one hsqrt_nonneg
    nlinarith [hepsilon_pos]
  exact mul_le_mul_of_nonneg_right hmain htheta_nonneg

private theorem epsilon_mul_theta_le_compressionTarget
    {delta epsilon theta : ℝ}
    (_hdelta_nonneg : 0 ≤ delta) (hepsilon_pos : 0 < epsilon)
    (htheta_nonneg : 0 ≤ theta) :
    epsilon * theta ≤
      (epsilon + epsilon⁻¹ * Real.sqrt delta) * theta := by
  have hterm_nonneg :
      0 ≤ epsilon⁻¹ * Real.sqrt delta :=
    mul_nonneg (inv_nonneg.mpr hepsilon_pos.le) (Real.sqrt_nonneg delta)
  exact mul_le_mul_of_nonneg_right (by nlinarith) htheta_nonneg

private theorem epsilon_inv_mul_sqrt_delta_mul_theta_le_compressionTarget
    {delta epsilon theta : ℝ}
    (_hdelta_nonneg : 0 ≤ delta) (hepsilon_pos : 0 < epsilon)
    (htheta_nonneg : 0 ≤ theta) :
    epsilon⁻¹ * Real.sqrt delta * theta ≤
      (epsilon + epsilon⁻¹ * Real.sqrt delta) * theta := by
  have hmain :
      epsilon⁻¹ * Real.sqrt delta ≤
        epsilon + epsilon⁻¹ * Real.sqrt delta := by
    nlinarith [hepsilon_pos]
  exact mul_le_mul_of_nonneg_right hmain htheta_nonneg

private theorem epsilon_inv_mul_sqrt_delta_le_compressionTarget_of_one_le_theta
    {delta epsilon theta : ℝ}
    (hdelta_nonneg : 0 ≤ delta) (hepsilon_pos : 0 < epsilon)
    (htheta_one : 1 ≤ theta) :
    epsilon⁻¹ * Real.sqrt delta ≤
      (epsilon + epsilon⁻¹ * Real.sqrt delta) * theta := by
  have htheta_nonneg : 0 ≤ theta := le_trans zero_le_one htheta_one
  have hterm_nonneg :
      0 ≤ epsilon⁻¹ * Real.sqrt delta :=
    mul_nonneg (inv_nonneg.mpr hepsilon_pos.le) (Real.sqrt_nonneg delta)
  calc
    epsilon⁻¹ * Real.sqrt delta ≤
        epsilon⁻¹ * Real.sqrt delta * theta := by
        simpa [one_mul] using
          mul_le_mul_of_nonneg_left htheta_one hterm_nonneg
    _ ≤ (epsilon + epsilon⁻¹ * Real.sqrt delta) * theta :=
        epsilon_inv_mul_sqrt_delta_mul_theta_le_compressionTarget
          hdelta_nonneg hepsilon_pos htheta_nonneg

private theorem coarseFluctuationManuscriptRHSAtScale_zero_eq_decomp
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C ε : ℝ) (m : ℕ) (e : Vec d) :
    coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε 0 m e =
      let β := section53CoarseFluctuationBeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let θ := thetaAtScale hP hStruct (m : ℤ)
      let T :=
        Real.sqrt (tauAtScale P (m : ℤ) (0 : ℤ) p_e q_e) *
          Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (0 : ℤ)) p_e q_e)
      let Center := (Real.sqrt θ - 1) ^ 2
      let A :=
        β⁻¹ * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m
      let B :=
        (β ^ 2)⁻¹ * coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e
      let R :=
        (hP4.xi : ℝ) * (β ^ 3)⁻¹ * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
          coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
      let D :=
        (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ))) *
            coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
      let Ssum := A + B + R + D
      C * T + C * ε * Center + C * ε⁻¹ * Ssum := by
  unfold coarseFluctuationManuscriptRHSAtScale
  dsimp only
  ring_nf

theorem coarseFluctuationManuscriptRHSAtScale_zero_le_compressed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C0 Csep delta epsilon : ℝ} {m : ℕ}
    (hC0_nonneg : 0 ≤ C0)
    (hCsep : oneStepScaleSeparationConst hP4 ≤ Csep)
    (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (hsep :
      Csep * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ))
    (hepsilon_pos : 0 < epsilon) (hepsilon_le : epsilon ≤ 1)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let M :=
      3 +
        β⁻¹ * oneStepCoarseFullBlockConst hP4 +
          (β ^ 2)⁻¹ * oneStepCoarseTauSumConst hP4 +
            (hP4.xi : ℝ) * (β ^ 3)⁻¹ * 4 +
              (β ^ 2)⁻¹ * 3
    coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C0 epsilon 0 m e ≤
      C0 * M *
        ((epsilon + epsilon⁻¹ * Real.sqrt delta) *
          thetaAtScale hP hStruct (0 : ℤ)) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let θ0 := thetaAtScale hP hStruct (0 : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let target := (epsilon + epsilon⁻¹ * Real.sqrt delta) * θ0
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let Tfirst :=
    Real.sqrt (tauAtScale P (m : ℤ) (0 : ℤ) p_e q_e) *
      Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (0 : ℤ)) p_e q_e)
  let Center := (Real.sqrt θ - 1) ^ (2 : ℕ)
  let A := β⁻¹ * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m
  let B :=
    (β ^ 2)⁻¹ * coarseFluctuationScalarWeightAtScale hP hStruct m *
      coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e
  let R :=
    (hP4.xi : ℝ) * (β ^ 3)⁻¹ * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
  let D :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ))) *
        coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
  let Ssum := A + B + R + D
  let coefA := β⁻¹ * oneStepCoarseFullBlockConst hP4
  let coefB := (β ^ 2)⁻¹ * oneStepCoarseTauSumConst hP4
  let coefR := (hP4.xi : ℝ) * (β ^ 3)⁻¹ * 4
  let coefD := (β ^ 2)⁻¹ * 3
  let M := 3 + coefA + coefB + coefR + coefD
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβinv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ_pos.le
  have hβ2inv_nonneg : 0 ≤ (β ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg β)
  have hβ3inv_nonneg : 0 ≤ (β ^ 3)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg hβ_pos.le 3)
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hθ0_one : 1 ≤ θ0 := by
    simpa [θ0] using one_le_thetaAtScale_zero_of_P4 hP hStruct hP4
  have hθ0_nonneg : 0 ≤ θ0 := le_trans zero_le_one hθ0_one
  have hsqrtdelta_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    exact mul_nonneg
      (add_nonneg hepsilon_pos.le
        (mul_nonneg (inv_nonneg.mpr hepsilon_pos.le) hsqrtdelta_nonneg))
      hθ0_nonneg
  have hsqrt_delta_theta_le :
      Real.sqrt delta * θ0 ≤ target := by
    simpa [target, θ0] using
      sqrt_delta_mul_theta_le_compressionTarget hdelta_pos.le
        hepsilon_pos hepsilon_le hθ0_nonneg
  have hepsilon_theta_le :
      epsilon * θ0 ≤ target := by
    simpa [target, θ0] using
      epsilon_mul_theta_le_compressionTarget hdelta_pos.le
        hepsilon_pos hθ0_nonneg
  have hepsilon_inv_sqrt_theta_le :
      epsilon⁻¹ * Real.sqrt delta * θ0 ≤ target := by
    simpa [target, θ0] using
      epsilon_inv_mul_sqrt_delta_mul_theta_le_compressionTarget
        hdelta_pos.le hepsilon_pos hθ0_nonneg
  have hepsilon_inv_sqrt_le :
      epsilon⁻¹ * Real.sqrt delta ≤ target := by
    simpa [target, θ0] using
      epsilon_inv_mul_sqrt_delta_le_compressionTarget_of_one_le_theta
        hdelta_pos.le hepsilon_pos hθ0_one
  have hTfirst_le :
      Tfirst ≤ 2 * target := by
    have h :=
      firstCoarseRhsTerm_le_two_sqrt_delta_theta
        hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
    calc
      Tfirst ≤ 2 * Real.sqrt delta * θ0 := by
        simpa [Tfirst, p_e, q_e, θ0] using h
      _ = 2 * (Real.sqrt delta * θ0) := by ring
      _ ≤ 2 * target :=
        mul_le_mul_of_nonneg_left hsqrt_delta_theta_le (by norm_num)
  have hCenter_le :
      Center ≤ θ0 := by
    simpa [Center, θ, θ0] using
      centerTerm_le_theta_zero hP hStruct hP4 m
  have hCenterTerm_le :
      epsilon * Center ≤ target := by
    calc
      epsilon * Center ≤ epsilon * θ0 :=
        mul_le_mul_of_nonneg_left hCenter_le hepsilon_pos.le
      _ ≤ target := hepsilon_theta_le
  have hθ_le : θ ≤ θ0 := by
    simpa [θ, θ0] using
      thetaAtScale_m_le_thetaAtScale_zero_of_P4 hP hStruct hP4 m
  have hθ_nonneg : 0 ≤ θ := by
    have hθ_one : 1 ≤ θ := by
      simpa [θ] using GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m
    exact le_trans zero_le_one hθ_one
  have hfull_nonneg :
      0 ≤ coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m :=
    coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 0 m
  have hfull_le :
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m ≤
        oneStepCoarseFullBlockConst hP4 * Real.sqrt delta := by
    calc
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m =
          oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m := by
          exact
            coarseFluctuationFullBlockSumAtScale_zero_eq_oneStepCoarseFullBlockSumAtScale
              hP hStruct hP4 m
      _ ≤ oneStepCoarseFullBlockConst hP4 * Real.sqrt delta :=
          oneStepCoarseFullBlockSumAtScale_le_sqrt_delta
            hP hStruct hP4 hCsep hdelta_pos hdelta_le hsep
            hgood_upper hgood_lower
  have hfbConst_nonneg : 0 ≤ oneStepCoarseFullBlockConst hP4 :=
    oneStepCoarseFullBlockConst_nonneg hP4
  have hA_le :
      A ≤ coefA * (Real.sqrt delta * θ0) := by
    calc
      A = β⁻¹ * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m := rfl
      _ ≤ β⁻¹ * θ0 * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hθ_le hβinv_nonneg) hfull_nonneg
      _ ≤ β⁻¹ * θ0 * (oneStepCoarseFullBlockConst hP4 * Real.sqrt delta) := by
          exact mul_le_mul_of_nonneg_left hfull_le
            (mul_nonneg hβinv_nonneg hθ0_nonneg)
      _ = coefA * (Real.sqrt delta * θ0) := by
          simp [coefA]
          ring
  have hAterm_le :
      epsilon⁻¹ * A ≤ coefA * target := by
    have hcoef_nonneg : 0 ≤ coefA := by
      dsimp [coefA]
      positivity
    calc
      epsilon⁻¹ * A ≤ epsilon⁻¹ * (coefA * (Real.sqrt delta * θ0)) :=
          mul_le_mul_of_nonneg_left hA_le (inv_nonneg.mpr hepsilon_pos.le)
      _ = coefA * (epsilon⁻¹ * Real.sqrt delta * θ0) := by ring
      _ ≤ coefA * target :=
          mul_le_mul_of_nonneg_left hepsilon_inv_sqrt_theta_le hcoef_nonneg
  have htau_le :
      coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e ≤
        oneStepCoarseTauSumConst hP4 * Real.sqrt delta * θ0 := by
    simpa [θ0] using
      coarseFluctuationScalarWeight_mul_tauSum_zero_le_sqrt_delta_theta
        hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
  have htauConst_nonneg : 0 ≤ oneStepCoarseTauSumConst hP4 :=
    oneStepCoarseTauSumConst_nonneg hP4
  have hB_le :
      B ≤ coefB * (Real.sqrt delta * θ0) := by
    calc
      B =
          (β ^ 2)⁻¹ *
            (coarseFluctuationScalarWeightAtScale hP hStruct m *
              coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e) := by
          simp [B]
          ring
      _ ≤ (β ^ 2)⁻¹ *
          (oneStepCoarseTauSumConst hP4 * Real.sqrt delta * θ0) :=
          mul_le_mul_of_nonneg_left htau_le hβ2inv_nonneg
      _ = coefB * (Real.sqrt delta * θ0) := by
          simp [coefB]
          ring
  have hBterm_le :
      epsilon⁻¹ * B ≤ coefB * target := by
    have hcoef_nonneg : 0 ≤ coefB := by
      dsimp [coefB]
      positivity
    calc
      epsilon⁻¹ * B ≤ epsilon⁻¹ * (coefB * (Real.sqrt delta * θ0)) :=
          mul_le_mul_of_nonneg_left hB_le (inv_nonneg.mpr hepsilon_pos.le)
      _ = coefB * (epsilon⁻¹ * Real.sqrt delta * θ0) := by ring
      _ ≤ coefB * target :=
          mul_le_mul_of_nonneg_left hepsilon_inv_sqrt_theta_le hcoef_nonneg
  have hRtail :
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
          coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e ≤
        4 * Real.sqrt delta := by
    simpa [β] using
      responseMomentTail_le_four_sqrt_delta
        hP hStruct hP4 hCsep hdelta_pos hdelta_le hsep e he
  have hR_le :
      R ≤ coefR * Real.sqrt delta := by
    calc
      R =
          ((hP4.xi : ℝ) * (β ^ 3)⁻¹) *
            (Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e) := by
          simp [R]
          ring
      _ ≤ ((hP4.xi : ℝ) * (β ^ 3)⁻¹) * (4 * Real.sqrt delta) :=
          mul_le_mul_of_nonneg_left hRtail
            (mul_nonneg hxi_nonneg hβ3inv_nonneg)
      _ = coefR * Real.sqrt delta := by
          simp [coefR]
          ring
  have hRterm_le :
      epsilon⁻¹ * R ≤ coefR * target := by
    have hcoef_nonneg : 0 ≤ coefR := by
      dsimp [coefR]
      positivity
    calc
      epsilon⁻¹ * R ≤ epsilon⁻¹ * (coefR * Real.sqrt delta) :=
          mul_le_mul_of_nonneg_left hR_le (inv_nonneg.mpr hepsilon_pos.le)
      _ = coefR * (epsilon⁻¹ * Real.sqrt delta) := by ring
      _ ≤ coefR * target :=
          mul_le_mul_of_nonneg_left hepsilon_inv_sqrt_le hcoef_nonneg
  have hDtail :
      Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ))) *
          coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1) ≤
        3 * Real.sqrt delta := by
    simpa [β, θ] using
      lowScaleTail_le_three_sqrt_delta
        hP hStruct hP4 hCsep hdelta_pos hdelta_le hsep
        hgood_upper hgood_lower e he
  have hD_le :
      D ≤ coefD * Real.sqrt delta := by
    calc
      D =
          (β ^ 2)⁻¹ *
            (Real.rpow (3 : ℝ) (-2 * β * (((m - 0 : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) := by
          simp [D]
          ring
      _ ≤ (β ^ 2)⁻¹ * (3 * Real.sqrt delta) :=
          mul_le_mul_of_nonneg_left hDtail hβ2inv_nonneg
      _ = coefD * Real.sqrt delta := by
          simp [coefD]
          ring
  have hDterm_le :
      epsilon⁻¹ * D ≤ coefD * target := by
    have hcoef_nonneg : 0 ≤ coefD := by
      dsimp [coefD]
      positivity
    calc
      epsilon⁻¹ * D ≤ epsilon⁻¹ * (coefD * Real.sqrt delta) :=
          mul_le_mul_of_nonneg_left hD_le (inv_nonneg.mpr hepsilon_pos.le)
      _ = coefD * (epsilon⁻¹ * Real.sqrt delta) := by ring
      _ ≤ coefD * target :=
          mul_le_mul_of_nonneg_left hepsilon_inv_sqrt_le hcoef_nonneg
  have hSterm_le :
      epsilon⁻¹ * Ssum ≤ (coefA + coefB + coefR + coefD) * target := by
    calc
      epsilon⁻¹ * Ssum =
          epsilon⁻¹ * A + epsilon⁻¹ * B + epsilon⁻¹ * R + epsilon⁻¹ * D := by
          simp [Ssum]
          ring
      _ ≤ coefA * target + coefB * target + coefR * target + coefD * target :=
          add_le_add (add_le_add (add_le_add hAterm_le hBterm_le) hRterm_le)
            hDterm_le
      _ = (coefA + coefB + coefR + coefD) * target := by ring
  have hbase :
      Tfirst + epsilon * Center + epsilon⁻¹ * Ssum ≤ M * target := by
    calc
      Tfirst + epsilon * Center + epsilon⁻¹ * Ssum ≤
          2 * target + target + (coefA + coefB + coefR + coefD) * target :=
          add_le_add (add_le_add hTfirst_le hCenterTerm_le) hSterm_le
      _ = M * target := by
          simp [M]
          ring
  have hdecomp :=
    coarseFluctuationManuscriptRHSAtScale_zero_eq_decomp
      hP hStruct hP4 C0 epsilon m e
  rw [hdecomp]
  calc
    C0 * Tfirst + C0 * epsilon * Center + C0 * epsilon⁻¹ * Ssum =
        C0 * (Tfirst + epsilon * Center + epsilon⁻¹ * Ssum) := by ring
    _ ≤ C0 * (M * target) :=
        mul_le_mul_of_nonneg_left hbase hC0_nonneg
    _ = C0 * M * ((epsilon + epsilon⁻¹ * Real.sqrt delta) * θ0) := by
        simp [target]
        ring
end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
