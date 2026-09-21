/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.Uniform

/-! # Scalar Preliminaries -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open MeasureTheory
open Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem sUpper_add_beta_pos' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 :=
  add_pos hP4.sUpper_pos (section53CoarseFluctuationBeta_pos hP4)

private theorem sLower_add_beta_pos' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sLower + section53CoarseFluctuationBeta hP4 :=
  add_pos hP4.sLower_pos (section53CoarseFluctuationBeta_pos hP4)

private theorem sUpper_add_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hlower_beta_pos :
      0 < hP4.sLower + section53CoarseFluctuationBeta hP4 :=
    sLower_add_beta_pos' hP4
  nlinarith

private theorem sLower_add_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hupper_beta_pos :
      0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 :=
    sUpper_add_beta_pos' hP4
  nlinarith

theorem integrable_pow_of_nonneg_le_const_add_nonneg
    {d ξ : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {X E : RegCoeffField d → ℝ} {A : ℝ}
    (hξ : 1 ≤ ξ) (hA_nonneg : 0 ≤ A)
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hE_nonneg : ∀ a, 0 ≤ E a)
    (hX_le : ∀ a, X a ≤ A + E a)
    (hX_meas : AEMeasurable X P)
    (hE_meas : AEMeasurable E P)
    (hE_pow_int : Integrable (fun a => E a ^ ξ) P) :
    Integrable (fun a => X a ^ ξ) P := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hE_abs_pow_int : Integrable (fun a => |E a| ^ ξ) P := by
    refine hE_pow_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hE_nonneg a)]
  have hE_mem : MemLp E (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hE_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hE_abs_pow_int
  have hY_mem : MemLp (fun a => A + E a) (ξ : ENNReal) P :=
    (memLp_const A).add hE_mem
  have hY_abs_pow_int : Integrable (fun a => |A + E a| ^ ξ) P := by
    simpa [Real.norm_eq_abs] using hY_mem.integrable_norm_pow hξ_ne
  have hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P := by
    refine Integrable.mono' hY_abs_pow_int
      (hX_meas.norm.pow_const ξ).aestronglyMeasurable ?_
    filter_upwards with a
    have hY_nonneg : 0 ≤ A + E a := add_nonneg hA_nonneg (hE_nonneg a)
    have habs : |X a| ≤ |A + E a| := by
      simpa [abs_of_nonneg (hX_nonneg a), abs_of_nonneg hY_nonneg] using
        hX_le a
    have hpow : |X a| ^ ξ ≤ |A + E a| ^ ξ :=
      pow_le_pow_left₀ (abs_nonneg (X a)) habs ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (X a)) ξ)]
      using hpow
  refine hX_abs_pow_int.congr ?_
  filter_upwards with a
  simp [abs_of_nonneg (hX_nonneg a)]

theorem upperShiftedFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField (originCube d (m : ℤ))
          (hP4.sUpper + section53CoarseFluctuationBeta hP4) (.finite 1) a) ^
          hP4.xi) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let rUpper := hP4.sUpper + section53CoarseFluctuationBeta hP4
  let X : RegCoeffField d → ℝ := fun a =>
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) rUpper (.finite 1) a
  let E : RegCoeffField d → ℝ := fun a =>
    max (X a - hP.barSigmaAtScale hStruct 0) 0
  have hBarSigma_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0 := by
    rw [hP.barSigmaAtScale_eq_barBAtScale hStruct (0 : ℤ)]
    simpa [Ch04.RestrictionLawCarrier.barBAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (0 : ℤ))
        (Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 0)
  have hX_meas : AEMeasurable X P := by
    simpa [X, rUpper] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (m : ℤ)) (sUpper_add_beta_pos' hP4)
  have hE_meas : AEMeasurable E P :=
    (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ hP4.xi) P := by
    simpa [E, X, rUpper] using
      Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 (sUpper_lt_sUpper_add_beta hP4)
        (sUpper_add_beta_lt_one' hP4) m
  simpa [X, rUpper] using
    integrable_pow_of_nonneg_le_const_add_nonneg
      (P := P) (ξ := hP4.xi) (X := X) (E := E)
      (A := hP.barSigmaAtScale hStruct 0)
      (Nat.succ_le_of_lt hP4.xi_pos) hBarSigma_nonneg
      (fun a =>
        Ch04.LambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a
          (sUpper_add_beta_pos' hP4) (by norm_num : (1 : ℝ) ≤ 1))
      (fun a => le_max_right (X a - hP.barSigmaAtScale hStruct 0) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) (hP.barSigmaAtScale hStruct 0))
      hX_meas hE_meas hE_pow_int

theorem lowerShiftedFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ))
          (hP4.sLower + section53CoarseFluctuationBeta hP4) (.finite 1) a)⁻¹) ^
          hP4.xi) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let rLower := hP4.sLower + section53CoarseFluctuationBeta hP4
  let X : RegCoeffField d → ℝ := fun a =>
    (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹
  let E : RegCoeffField d → ℝ := fun a =>
    max (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0
  have hStarInv_nonneg : 0 ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹ := by
    have hstar := hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (0 : ℤ)
    rw [hstar, inv_inv]
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      (Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (0 : ℤ))
        (Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 0)).le
  have hX_meas : AEMeasurable X P := by
    simpa [X, rLower] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (m : ℤ)) (sLower_add_beta_pos' hP4)
  have hE_meas : AEMeasurable E P :=
    (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ hP4.xi) P := by
    simpa [E, X, rLower] using
      Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 (sLower_lt_sLower_add_beta hP4)
        (sLower_add_beta_lt_one' hP4) m
  simpa [X, rLower] using
    integrable_pow_of_nonneg_le_const_add_nonneg
      (P := P) (ξ := hP4.xi) (X := X) (E := E)
      (A := (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      (Nat.succ_le_of_lt hP4.xi_pos) hStarInv_nonneg
      (fun a =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a
            (sLower_add_beta_pos' hP4) (by norm_num : (1 : ℝ) ≤ 1)))
      (fun a => le_max_right (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) ((hP.barSigmaStarAtScale hStruct 0)⁻¹))
      hX_meas hE_meas hE_pow_int

/-- The quantitative ellipticity input with the Section 5.5 source exponents
shifted by one `β`. -/
def betaShiftedP4 {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    QuantitativeCoarseGrainedEllipticity P where
  sUpper := hP4.sUpper + section53CoarseFluctuationBeta hP4
  sLower := hP4.sLower + section53CoarseFluctuationBeta hP4
  xi := hP4.xi
  two_le_dim := hP4.two_le_dim
  sUpper_nonneg :=
    add_nonneg hP4.sUpper_nonneg (section53CoarseFluctuationBeta_nonneg hP4)
  sUpper_lt_one := sUpper_add_beta_lt_one' hP4
  sLower_nonneg :=
    add_nonneg hP4.sLower_nonneg (section53CoarseFluctuationBeta_nonneg hP4)
  sLower_lt_one := sLower_add_beta_lt_one' hP4
  xi_gt_two_mul_dim := hP4.xi_gt_two_mul_dim
  sum_lt_one := by
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    have hbeta := section53CoarseFluctuationBeta_pos hP4
    nlinarith
  dim_div_xi_lt_min := by
    rw [lt_min_iff]
    constructor
    · linarith [hP4.dim_div_xi_lt_sUpper,
        section53CoarseFluctuationBeta_pos hP4]
    · linarith [hP4.dim_div_xi_lt_sLower,
        section53CoarseFluctuationBeta_pos hP4]
  upper_moment_integrable :=
    upperShiftedFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 0
  lower_inv_moment_integrable :=
    lowerShiftedFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 0

/-- Shifted scalar preliminary for Section 5.5:
`\Theta_n <= \widetilde\Theta_n^{(\beta)}`. -/
theorem thetaAtScale_le_betaShiftedWidetildeThetaAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    thetaAtScale hP hStruct (n : ℤ) ≤
      betaShiftedWidetildeThetaAtScale P (n : ℤ) hP4 := by
  have hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P :=
    fun l => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ))
              (hP4.sUpper + section53CoarseFluctuationBeta hP4) (.finite 1) a) ^
              hP4.xi) P :=
    fun l => upperShiftedFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ))
              (hP4.sLower + section53CoarseFluctuationBeta hP4) (.finite 1) a)⁻¹) ^
              hP4.xi) P :=
    fun l => lowerShiftedFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have h :=
    hP.thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
      hStruct (sUpper_add_beta_pos' hP4) (sLower_add_beta_pos' hP4)
      (Nat.succ_le_of_lt hP4.xi_pos) hBlock
      (fun l =>
        hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (l : ℤ)) (sUpper_add_beta_pos' hP4))
      (fun l =>
        hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (l : ℤ)) (sLower_add_beta_pos' hP4))
      hUpperPowInt hLowerPowInt n
  simpa [thetaAtScale, betaShiftedWidetildeThetaAtScale,
    shiftedWidetildeThetaAtScale] using h

end

end Section55
end Ch05
end Book
end Homogenization
