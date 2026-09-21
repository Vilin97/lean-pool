/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.CenteredResponses

/-! # Special Vectors -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Special vectors for the third Section 5.3 lemma

This file contains the scalar algebra for the manuscript choices
`p_e = \widehat\sigma_m^{-1/2} e` and
`q_e = \widehat\sigma_m^{1/2} e`.
-/

/-- The centered-response expectation is the raw response expectation with the
manuscript scalar centering subtracted, specialized to the Section 5.3 special
vectors. -/
theorem expectedResponseJCubeSet_sub_half_vecDot_specialCentering_eq_expectedCenteredResponseJAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e -
        (1 / 2 : ℝ) * vecDot p0_e q0_e =
      expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e := by
  dsimp only
  let : IsProbabilityMeasure P := hP.isProbability
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hJ :
      Integrable
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (m : ℤ))
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e)) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d (m : ℤ))
      (specialPAtScale hP hStruct (m : ℤ) e)
      (specialQAtScale hP hStruct (m : ℤ) e) hBlock
  have hCentered :=
    Section52.expectedCenteredResponseJAtScale_eq_annealedResponseJAtScale_sub
      hP hStruct (m : ℤ)
      (specialPAtScale hP hStruct (m : ℤ) e)
      (specialQAtScale hP hStruct (m : ℤ) e) hJ
  rw [hCentered]
  simp [Ch04.expectedResponseJCubeSet, Ch04.annealedResponseJAtScale,
    Ch04.responseJAtScale, Ch04.restrictionResponseJObservableCubeSet,
    scalarizedResponseCenteringTerm]

private theorem sigma_mul_inv_star_eq_sqrt_theta {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    σ * c⁻¹ = Real.sqrt θ := by
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hθnonneg : 0 ≤ θ := by
    rw [hθ]
    exact mul_nonneg hb.le (inv_pos.mpr hc).le
  have hleft_nonneg : 0 ≤ σ * c⁻¹ := mul_nonneg hσpos.le (inv_pos.mpr hc).le
  have hsq : (σ * c⁻¹) * (σ * c⁻¹) = Real.sqrt θ * Real.sqrt θ := by
    calc
      (σ * c⁻¹) * (σ * c⁻¹) =
          (Real.sqrt (b * c) * Real.sqrt (b * c)) * (c⁻¹ * c⁻¹) := by
        rw [hσ]
        ring
      _ = (b * c) * (c⁻¹ * c⁻¹) := by
        rw [Real.mul_self_sqrt (mul_pos hb hc).le]
      _ = b * c⁻¹ := by
        have hcne : c ≠ 0 := ne_of_gt hc
        field_simp [hcne]
      _ = θ := by
        rw [hθ]
      _ = Real.sqrt θ * Real.sqrt θ :=
        (Real.mul_self_sqrt hθnonneg).symm
  exact (mul_self_inj_of_nonneg hleft_nonneg (Real.sqrt_nonneg θ)).1 hsq

private theorem barSigma_mul_inv_sigma_eq_sqrt_theta {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    b * σ⁻¹ = Real.sqrt θ := by
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hθnonneg : 0 ≤ θ := by
    rw [hθ]
    exact mul_nonneg hb.le (inv_pos.mpr hc).le
  have hleft_nonneg : 0 ≤ b * σ⁻¹ := mul_nonneg hb.le (inv_pos.mpr hσpos).le
  have hsq : (b * σ⁻¹) * (b * σ⁻¹) = Real.sqrt θ * Real.sqrt θ := by
    calc
      (b * σ⁻¹) * (b * σ⁻¹) =
          (b * b) * (Real.sqrt (b * c))⁻¹ * (Real.sqrt (b * c))⁻¹ := by
        rw [hσ]
        ring
      _ = b * c⁻¹ := by
        have hprod_pos : 0 < b * c := mul_pos hb hc
        have hprod_ne : b * c ≠ 0 := ne_of_gt hprod_pos
        have hsqrt_ne : Real.sqrt (b * c) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos_of_pos hprod_pos)
        field_simp [hsqrt_ne, hprod_ne]
        rw [Real.sq_sqrt hprod_pos.le]
      _ = θ := by
        rw [hθ]
      _ = Real.sqrt θ * Real.sqrt θ :=
        (Real.mul_self_sqrt hθnonneg).symm
  exact (mul_self_inj_of_nonneg hleft_nonneg (Real.sqrt_nonneg θ)).1 hsq

private theorem sigmaHat_mul_specialP_centering_coeff_sq_eq {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    σ * (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) ^ 2 =
      (Real.sqrt θ - 1) ^ 2 := by
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := sigma_mul_inv_star_eq_sqrt_theta hb hc hσ hθ
  have hhalf : σ ^ (1 / 2 : ℝ) = σ * σ ^ (-(1 / 2 : ℝ)) := by
    calc
      σ ^ (1 / 2 : ℝ) = σ ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
        norm_num
      _ = σ ^ (1 : ℝ) * σ ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_add hσpos 1 (-(1 / 2 : ℝ))
      _ = σ * σ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
  have hneg_sq : (σ ^ (-(1 / 2 : ℝ))) ^ 2 = σ⁻¹ := by
    calc
      (σ ^ (-(1 / 2 : ℝ))) ^ 2 =
          (σ ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (-(1 / 2 : ℝ))) 2).symm
      _ = σ ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = σ ^ (-1 : ℝ) := by
        norm_num
      _ = (σ ^ (1 : ℝ))⁻¹ :=
        Real.rpow_neg hσpos.le 1
      _ = σ⁻¹ := by
        rw [Real.rpow_one]
  calc
    σ * (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) ^ 2 =
        σ * (σ ^ (-(1 / 2 : ℝ)) * (Real.sqrt θ - 1)) ^ 2 := by
          rw [hhalf]
          rw [← hdiv]
          ring
    _ = (Real.sqrt θ - 1) ^ 2 := by
          rw [mul_pow, hneg_sq]
          field_simp [ne_of_gt hσpos]

private theorem inv_sigmaHat_mul_specialQ_centering_coeff_sq_eq {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    σ⁻¹ * (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) ^ 2 =
      (Real.sqrt θ - 1) ^ 2 := by
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hdiv := barSigma_mul_inv_sigma_eq_sqrt_theta hb hc hσ hθ
  have hhalf : σ ^ (1 / 2 : ℝ) = σ * σ ^ (-(1 / 2 : ℝ)) := by
    calc
      σ ^ (1 / 2 : ℝ) = σ ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
        norm_num
      _ = σ ^ (1 : ℝ) * σ ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_add hσpos 1 (-(1 / 2 : ℝ))
      _ = σ * σ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
  have hpos_sq : (σ ^ (1 / 2 : ℝ)) ^ 2 = σ := by
    calc
      (σ ^ (1 / 2 : ℝ)) ^ 2 =
          (σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (1 / 2 : ℝ)) 2).symm
      _ = σ ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = σ ^ (1 : ℝ) := by
        norm_num
      _ = σ := by
        rw [Real.rpow_one]
  calc
    σ⁻¹ * (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) ^ 2 =
        σ⁻¹ * (σ ^ (1 / 2 : ℝ) * (1 - Real.sqrt θ)) ^ 2 := by
          rw [hhalf]
          rw [← hdiv]
          field_simp [ne_of_gt hσpos]
    _ = (Real.sqrt θ - 1) ^ 2 := by
          rw [mul_pow, hpos_sq]
          field_simp [ne_of_gt hσpos]
          ring

private theorem barSigmaStarAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaStarAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (m : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (m : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (m : ℤ)]
  exact inv_pos.mpr hInv

private theorem barSigmaAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :=
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock
  have hstar_pos := barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hprod_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    exact lt_of_lt_of_le zero_lt_one (by
      simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using htheta)
  exact pos_of_mul_pos_left hprod_pos (inv_pos.mpr hstar_pos).le

/-- Under `(P4)`, the scalar condition number at every origin scale is at
least one. -/
theorem one_le_thetaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    1 ≤ thetaAtScale hP hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  exact
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock

/-- At the Section 5.3 special vectors, the raw annealed scalar response is
the scalar gap `sqrt(Theta_m) - 1`, times the Euclidean square of the chosen
direction. -/
theorem expectedResponseJCubeSet_special_eq_sqrtTheta_sub_one_mul_vecNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e =
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) * vecNormSq e := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hb : 0 < b := by
    simpa [b] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have hpos_sq : (σ ^ (1 / 2 : ℝ)) ^ 2 = σ := by
    calc
      (σ ^ (1 / 2 : ℝ)) ^ 2 =
          (σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
            exact (Real.rpow_natCast (σ ^ (1 / 2 : ℝ)) 2).symm
      _ = σ ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul hσpos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = σ ^ (1 : ℝ) := by
            norm_num
      _ = σ := by
            rw [Real.rpow_one]
  have hneg_sq : (σ ^ (-(1 / 2 : ℝ))) ^ 2 = σ⁻¹ := by
    calc
      (σ ^ (-(1 / 2 : ℝ))) ^ 2 =
          (σ ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
            exact (Real.rpow_natCast (σ ^ (-(1 / 2 : ℝ))) 2).symm
      _ = σ ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
            (Real.rpow_mul hσpos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = σ ^ (-1 : ℝ) := by
            norm_num
      _ = (σ ^ (1 : ℝ))⁻¹ :=
            Real.rpow_neg hσpos.le 1
      _ = σ⁻¹ := by
            rw [Real.rpow_one]
  have hhalf_mul :
      σ ^ (-(1 / 2 : ℝ)) * σ ^ (1 / 2 : ℝ) = 1 := by
    calc
      σ ^ (-(1 / 2 : ℝ)) * σ ^ (1 / 2 : ℝ) =
          σ ^ (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
            (Real.rpow_add hσpos (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).symm
      _ = 1 := by
            norm_num
  have hq :
      vecDot q_e (c⁻¹ • q_e) = Real.sqrt θ * vecNormSq e := by
    have hqnorm : vecDot q_e q_e = σ * vecNormSq e := by
      calc
        vecDot q_e q_e =
            vecDot (σ ^ (1 / 2 : ℝ) • e) (σ ^ (1 / 2 : ℝ) • e) := by
              simp [q_e, σ]
        _ = σ ^ (1 / 2 : ℝ) * (σ ^ (1 / 2 : ℝ) * vecDot e e) := by
              rw [vecDot_smul_left, vecDot_smul_right]
        _ = ((σ ^ (1 / 2 : ℝ)) ^ 2) * vecNormSq e := by
              simp [vecNormSq, pow_two, mul_assoc]
        _ = σ * vecNormSq e := by
              rw [hpos_sq]
    calc
      vecDot q_e (c⁻¹ • q_e) = c⁻¹ * vecDot q_e q_e := by
            rw [vecDot_smul_right]
      _ = c⁻¹ * (σ * vecNormSq e) := by
            rw [hqnorm]
      _ = (σ * c⁻¹) * vecNormSq e := by
            ring
      _ = Real.sqrt θ * vecNormSq e := by
            rw [sigma_mul_inv_star_eq_sqrt_theta hb hc hσ hθ]
  have hpq :
      vecDot p_e q_e = vecNormSq e := by
    calc
      vecDot p_e q_e =
          σ ^ (1 / 2 : ℝ) * (σ ^ (-(1 / 2 : ℝ)) * vecDot e e) := by
            simp [p_e, q_e, σ, vecDot_smul_left, vecDot_smul_right]
      _ = (σ ^ (-(1 / 2 : ℝ)) * σ ^ (1 / 2 : ℝ)) * vecNormSq e := by
            simp [vecNormSq, mul_left_comm, mul_comm]
      _ = vecNormSq e := by
            rw [hhalf_mul]
            ring
  have hp :
      vecDot p_e (b • p_e) = Real.sqrt θ * vecNormSq e := by
    have hpnorm : vecDot p_e p_e = σ⁻¹ * vecNormSq e := by
      calc
        vecDot p_e p_e =
            vecDot (σ ^ (-(1 / 2 : ℝ)) • e) (σ ^ (-(1 / 2 : ℝ)) • e) := by
              simp [p_e, σ]
        _ = σ ^ (-(1 / 2 : ℝ)) * (σ ^ (-(1 / 2 : ℝ)) * vecDot e e) := by
              rw [vecDot_smul_left, vecDot_smul_right]
        _ = ((σ ^ (-(1 / 2 : ℝ))) ^ 2) * vecNormSq e := by
              simp [vecNormSq, pow_two, mul_assoc]
        _ = σ⁻¹ * vecNormSq e := by
              rw [hneg_sq]
    calc
      vecDot p_e (b • p_e) = b * vecDot p_e p_e := by
            rw [vecDot_smul_right]
      _ = b * (σ⁻¹ * vecNormSq e) := by
            rw [hpnorm]
      _ = (b * σ⁻¹) * vecNormSq e := by
            ring
      _ = Real.sqrt θ * vecNormSq e := by
            rw [barSigma_mul_inv_sigma_eq_sqrt_theta hb hc hσ hθ]
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hScalar :=
    Section52.annealedResponseJAtScale_eq_expectedJScalarFormula
      hP hStruct (m : ℤ) p_e q_e hBlock
  calc
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e =
        expectedJScalarFormula hP hStruct (m : ℤ) p_e q_e := by
          simpa [Ch04.expectedResponseJCubeSet, Ch04.annealedResponseJAtScale,
            Ch04.responseJAtScale] using hScalar
    _ =
        (Real.sqrt θ - 1) * vecNormSq e := by
          simp [expectedJScalarFormula, b, c, θ, hq, hpq, hp]
          ring

/-- At the special vectors, the raw annealed scalar response is bounded by the
condition-number excess, with the Euclidean square of the chosen direction. -/
theorem expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_mul_vecNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
      (thetaAtScale hP hStruct (m : ℤ) - 1) * vecNormSq e := by
  dsimp only
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hsqrt_le : Real.sqrt θ ≤ θ := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [hθ_one]
  have hcoeff : Real.sqrt θ - 1 ≤ θ - 1 := by
    linarith
  have hEq :=
    expectedResponseJCubeSet_special_eq_sqrtTheta_sub_one_mul_vecNormSq
      hP hStruct hP4 m e
  calc
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e =
        (Real.sqrt θ - 1) * vecNormSq e := by
          simpa [p_e, q_e, θ] using hEq
    _ ≤ (θ - 1) * vecNormSq e :=
          mul_le_mul_of_nonneg_right hcoeff (vecNormSq_nonneg e)

/-- Euclidean-unit specialization of
`expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_mul_vecNormSq`. -/
theorem expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
      thetaAtScale hP hStruct (m : ℤ) - 1 := by
  dsimp only
  have h :=
    expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_mul_vecNormSq
      hP hStruct hP4 m e
  simpa [he] using h

/-- The manuscript special vector `p_e` has the exact centered size. -/
theorem sigmaHatAtScale_mul_norm_specialPCentering_sq_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : ‖e‖ = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    sigmaHatAtScale hP hStruct (m : ℤ) * ‖p0_e‖ ^ 2 =
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hp0 :
      c⁻¹ • (σ ^ (1 / 2 : ℝ) • e) - σ ^ (-(1 / 2 : ℝ)) • e =
        (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    σ * ‖c⁻¹ • (σ ^ (1 / 2 : ℝ) • e) -
          σ ^ (-(1 / 2 : ℝ)) • e‖ ^ 2 =
        σ * (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [hp0, norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
    _ = (Real.sqrt θ - 1) ^ 2 :=
      sigmaHat_mul_specialP_centering_coeff_sq_eq hb hc hσ hθ

/-- Euclidean-squared form of the manuscript special-vector centered size for
`p_e`.  This is the robust form used by the coarse-fluctuation argument; the
direction size is left explicit and can later be specialized by
`vecNormSq e = 1`. -/
theorem sigmaHatAtScale_mul_vecNormSq_specialPCentering_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    sigmaHatAtScale hP hStruct (m : ℤ) * vecNormSq p0_e =
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 * vecNormSq e := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hp0 :
      c⁻¹ • (σ ^ (1 / 2 : ℝ) • e) - σ ^ (-(1 / 2 : ℝ)) • e =
        (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    σ * vecNormSq (c⁻¹ • (σ ^ (1 / 2 : ℝ) • e) -
          σ ^ (-(1 / 2 : ℝ)) • e) =
        σ * (c⁻¹ * σ ^ (1 / 2 : ℝ) - σ ^ (-(1 / 2 : ℝ))) ^ 2 *
          vecNormSq e := by
          rw [hp0, vecNormSq_smul]
          ring
    _ = (Real.sqrt θ - 1) ^ 2 * vecNormSq e := by
          rw [sigmaHat_mul_specialP_centering_coeff_sq_eq hb hc hσ hθ]

/-- The manuscript special vector `q_e` has the exact centered size. -/
theorem inv_sigmaHatAtScale_mul_norm_specialQCentering_sq_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : ‖e‖ = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ * ‖q0_e‖ ^ 2 =
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hq0 :
      σ ^ (1 / 2 : ℝ) • e - b • (σ ^ (-(1 / 2 : ℝ)) • e) =
        (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    σ⁻¹ * ‖σ ^ (1 / 2 : ℝ) • e -
          b • (σ ^ (-(1 / 2 : ℝ)) • e)‖ ^ 2 =
        σ⁻¹ * (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [hq0, norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
    _ = (Real.sqrt θ - 1) ^ 2 :=
      inv_sigmaHat_mul_specialQ_centering_coeff_sq_eq hb hc hσ hθ

/-- Euclidean-squared form of the manuscript special-vector centered size for
`q_e`. -/
theorem inv_sigmaHatAtScale_mul_vecNormSq_specialQCentering_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ * vecNormSq q0_e =
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 * vecNormSq e := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ : σ = Real.sqrt (b * c) := by
    rfl
  have hθ : θ = b * c⁻¹ := by
    rfl
  have hq0 :
      σ ^ (1 / 2 : ℝ) • e - b • (σ ^ (-(1 / 2 : ℝ)) • e) =
        (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    σ⁻¹ * vecNormSq (σ ^ (1 / 2 : ℝ) • e -
          b • (σ ^ (-(1 / 2 : ℝ)) • e)) =
        σ⁻¹ * (σ ^ (1 / 2 : ℝ) - b * σ ^ (-(1 / 2 : ℝ))) ^ 2 *
          vecNormSq e := by
          rw [hq0, vecNormSq_smul]
          ring
    _ = (Real.sqrt θ - 1) ^ 2 * vecNormSq e := by
          rw [inv_sigmaHat_mul_specialQ_centering_coeff_sq_eq hb hc hσ hθ]

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
