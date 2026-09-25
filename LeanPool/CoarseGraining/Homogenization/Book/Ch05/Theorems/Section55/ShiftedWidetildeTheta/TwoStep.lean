/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.ScalarPreliminaries
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ScalarLoss

/-! # Two Step -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem sUpper_add_two_beta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4 := by
  have hβ := section53CoarseFluctuationBeta_pos hP4
  linarith [hP4.sUpper_pos]

private theorem sLower_add_two_beta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sLower + 2 * section53CoarseFluctuationBeta hP4 := by
  have hβ := section53CoarseFluctuationBeta_pos hP4
  linarith [hP4.sLower_pos]

private theorem sUpper_add_two_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hlower_nonneg := hP4.sLower_nonneg
  have hβ := section53CoarseFluctuationBeta_pos hP4
  nlinarith

private theorem sLower_add_two_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + 2 * section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hupper_nonneg := hP4.sUpper_nonneg
  have hβ := section53CoarseFluctuationBeta_pos hP4
  nlinarith

private theorem twoBetaUpperDecay_le_betaDecay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    Real.rpow (3 : ℝ)
        (-((hP4.sUpper + 2 * β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hβ_le : β ≤ hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
    simpa [β] using section53CoarseFluctuationBeta_le_sUpper_sub_dim_div_xi hP4
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  nlinarith

private theorem twoBetaLowerDecay_le_betaDecay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    Real.rpow (3 : ℝ)
        (-((hP4.sLower + 2 * β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hβ_le : β ≤ hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
    simpa [β] using section53CoarseFluctuationBeta_le_sLower_sub_dim_div_xi hP4
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  nlinarith

theorem upperTwoBetaFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField (originCube d (m : ℤ))
          (hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4) (.finite 1) a) ^
          hP4.xi) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let rUpper := hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4
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
        (originCube d (m : ℤ)) (sUpper_add_two_beta_pos hP4)
  have hE_meas : AEMeasurable E P :=
    (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ hP4.xi) P := by
    have hlt : hP4.sUpper < rUpper := by
      dsimp [rUpper]
      have hβ := section53CoarseFluctuationBeta_pos hP4
      nlinarith
    simpa [E, X, rUpper] using
      Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hlt (sUpper_add_two_beta_lt_one' hP4) m
  simpa [X, rUpper] using
    integrable_pow_of_nonneg_le_const_add_nonneg
      (P := P) (ξ := hP4.xi) (X := X) (E := E)
      (A := hP.barSigmaAtScale hStruct 0)
      (Nat.succ_le_of_lt hP4.xi_pos) hBarSigma_nonneg
      (fun a =>
        Ch04.LambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a
          (sUpper_add_two_beta_pos hP4) (by norm_num : (1 : ℝ) ≤ 1))
      (fun a => le_max_right (X a - hP.barSigmaAtScale hStruct 0) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) (hP.barSigmaAtScale hStruct 0))
      hX_meas hE_meas hE_pow_int

theorem lowerTwoBetaFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ))
          (hP4.sLower + 2 * section53CoarseFluctuationBeta hP4) (.finite 1) a)⁻¹) ^
          hP4.xi) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let rLower := hP4.sLower + 2 * section53CoarseFluctuationBeta hP4
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
        (originCube d (m : ℤ)) (sLower_add_two_beta_pos hP4)
  have hE_meas : AEMeasurable E P :=
    (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ hP4.xi) P := by
    have hlt : hP4.sLower < rLower := by
      dsimp [rLower]
      have hβ := section53CoarseFluctuationBeta_pos hP4
      nlinarith
    simpa [E, X, rLower] using
      Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hlt (sLower_add_two_beta_lt_one' hP4) m
  simpa [X, rLower] using
    integrable_pow_of_nonneg_le_const_add_nonneg
      (P := P) (ξ := hP4.xi) (X := X) (E := E)
      (A := (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      (Nat.succ_le_of_lt hP4.xi_pos) hStarInv_nonneg
      (fun a =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a
            (sLower_add_two_beta_pos hP4) (by norm_num : (1 : ℝ) ≤ 1)))
      (fun a => le_max_right (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) ((hP.barSigmaStarAtScale hStruct 0)⁻¹))
      hX_meas hE_meas hE_pow_int

theorem thetaAtScale_le_twoBetaShiftedWidetildeThetaAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    thetaAtScale hP hStruct (n : ℤ) ≤
      shiftedWidetildeThetaAtScale P (n : ℤ) hP4
        (2 * section53CoarseFluctuationBeta hP4) := by
  have hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P :=
    fun l => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ))
              (hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4) (.finite 1) a) ^
              hP4.xi) P :=
    fun l => upperTwoBetaFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ))
              (hP4.sLower + 2 * section53CoarseFluctuationBeta hP4) (.finite 1) a)⁻¹) ^
              hP4.xi) P :=
    fun l => lowerTwoBetaFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have h :=
    hP.thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
      hStruct (sUpper_add_two_beta_pos hP4) (sLower_add_two_beta_pos hP4)
      (Nat.succ_le_of_lt hP4.xi_pos) hBlock
      (fun l =>
        hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (l : ℤ)) (sUpper_add_two_beta_pos hP4))
      (fun l =>
        hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (l : ℤ)) (sLower_add_two_beta_pos hP4))
      hUpperPowInt hLowerPowInt n
  simpa [thetaAtScale, shiftedWidetildeThetaAtScale, mul_assoc] using h

/-- One-window shifted localization with the source exponents already shifted
by one `β`, hence with target exponents shifted by `2β`. -/
theorem twoBetaShiftedWidetildeThetaAtScale_zero_bound_homogenizationScale
    {d : ℕ} [NeZero d] (xi : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P),
        hP4.xi = xi →
        section53CoarseFluctuationBeta hP4 = β →
        ∀ m : ℕ,
          shiftedWidetildeThetaAtScale P (m : ℤ) hP4 (2 * β) ≤
            thetaAtScale hP hStruct 0 +
              C * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                shiftedWidetildeThetaAtScale P 0 hP4 β := by
  obtain ⟨C52, hC52_nonneg, hC52⟩ :=
    Section52.multiscaleEllipticityMomentBounds_homogenizationScale (d := d)
  let D : ℝ := 2 * C52 * (xi : ℝ) * (β ^ 3)⁻¹
  let C : ℝ := D + D + D * D
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hD_nonneg hD_nonneg]
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 hxi hβeq m
  let β0 := section53CoarseFluctuationBeta hP4
  let hP4β := betaShiftedP4 hP hStruct hP4
  let decay : ℝ := Real.rpow (3 : ℝ) (-β0 * (m : ℝ))
  let upperCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 (hP4.sUpper + β0)
      (hP4.sUpper + 2 * β0) m
  let lowerCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C52 (hP4.sLower + β0)
      (hP4.sLower + 2 * β0) m
  let upperLoss : ℝ :=
    section52MomentLossCoeff d hP4.xi (hP4.sUpper + β0)
      (hP4.sUpper + 2 * β0)
  let lowerLoss : ℝ :=
    section52MomentLossCoeff d hP4.xi (hP4.sLower + β0)
      (hP4.sLower + 2 * β0)
  have hBounds :=
    hC52 hP hStruct hP4β
      (hP4.sUpper + 2 * β0) (hP4.sLower + 2 * β0) m
      (by dsimp [hP4β, betaShiftedP4, β0]; linarith [section53CoarseFluctuationBeta_pos hP4])
      (by simpa [β0] using sUpper_add_two_beta_lt_one' hP4)
      (by dsimp [hP4β, betaShiftedP4, β0]; linarith [section53CoarseFluctuationBeta_pos hP4])
      (by simpa [β0] using sLower_add_two_beta_lt_one' hP4)
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hdecay_le_one : decay ≤ 1 := by
    dsimp [decay, β0]
    exact rpow_three_neg_beta_nat_le_one
      (section53CoarseFluctuationBeta_nonneg hP4) m
  have hupperLoss_le : upperLoss ≤ 2 * (xi : ℝ) * (β ^ 3)⁻¹ := by
    dsimp [upperLoss]
    simpa [β0, hxi, hβeq] using
      section52MomentLossCoeff_upper_two_beta_shift_le_xi_beta_cubed hP4
  have hlowerLoss_le : lowerLoss ≤ 2 * (xi : ℝ) * (β ^ 3)⁻¹ := by
    dsimp [lowerLoss]
    simpa [β0, hxi, hβeq] using
      section52MomentLossCoeff_lower_two_beta_shift_le_xi_beta_cubed hP4
  have hupperCoeff_loss : upperCoeff ≤ (C52 * upperLoss) * decay := by
    have hdecay := twoBetaUpperDecay_le_betaDecay hP4 m
    have hloss_nonneg : 0 ≤ upperLoss := by
      dsimp [upperLoss]
      exact section52MomentLossCoeff_nonneg_at_shift hP4
        (by dsimp [β0]; linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4])
        (by dsimp [β0]; linarith [section53CoarseFluctuationBeta_pos hP4])
        (by simpa [β0] using sUpper_add_two_beta_lt_one' hP4)
    have hpref_nonneg : 0 ≤ C52 * upperLoss := mul_nonneg hC52_nonneg hloss_nonneg
    simpa [upperCoeff, upperLoss, decay, section52TwoExponentMomentBoundCoeff,
      β0, mul_assoc] using mul_le_mul_of_nonneg_left hdecay hpref_nonneg
  have hlowerCoeff_loss : lowerCoeff ≤ (C52 * lowerLoss) * decay := by
    have hdecay := twoBetaLowerDecay_le_betaDecay hP4 m
    have hloss_nonneg : 0 ≤ lowerLoss := by
      dsimp [lowerLoss]
      exact section52MomentLossCoeff_nonneg_at_shift hP4
        (by dsimp [β0]; linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4])
        (by dsimp [β0]; linarith [section53CoarseFluctuationBeta_pos hP4])
        (by simpa [β0] using sLower_add_two_beta_lt_one' hP4)
    have hpref_nonneg : 0 ≤ C52 * lowerLoss := mul_nonneg hC52_nonneg hloss_nonneg
    simpa [lowerCoeff, lowerLoss, decay, section52TwoExponentMomentBoundCoeff,
      β0, mul_assoc] using mul_le_mul_of_nonneg_left hdecay hpref_nonneg
  have hupperCoeff_le : upperCoeff ≤ D * decay := by
    calc
      upperCoeff ≤ (C52 * upperLoss) * decay := hupperCoeff_loss
      _ ≤ (C52 * (2 * (xi : ℝ) * (β ^ 3)⁻¹)) * decay := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hupperLoss_le hC52_nonneg) hdecay_nonneg
      _ = D * decay := by ring
  have hlowerCoeff_le : lowerCoeff ≤ D * decay := by
    calc
      lowerCoeff ≤ (C52 * lowerLoss) * decay := hlowerCoeff_loss
      _ ≤ (C52 * (2 * (xi : ℝ) * (β ^ 3)⁻¹)) * decay := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlowerLoss_le hC52_nonneg) hdecay_nonneg
      _ = D * decay := by ring
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4.xi) (m := m) (C := C52)
      (s := hP4.sUpper + β0) (r := hP4.sUpper + 2 * β0)
      hC52_nonneg
      (by dsimp [β0]; linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4])
      (by simpa [β0] using sUpper_add_two_beta_lt_one' hP4) hP4.two_le_dim
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4.xi) (m := m) (C := C52)
      (s := hP4.sLower + β0) (r := hP4.sLower + 2 * β0)
      hC52_nonneg
      (by dsimp [β0]; linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4])
      (by simpa [β0] using sLower_add_two_beta_lt_one' hP4) hP4.two_le_dim
  have hProd_le : upperCoeff * lowerCoeff ≤ D * D * decay := by
    have hUpper_rhs_nonneg : 0 ≤ D * decay := mul_nonneg hD_nonneg hdecay_nonneg
    have hprod_step :
        upperCoeff * lowerCoeff ≤ (D * decay) * (D * decay) :=
      mul_le_mul hupperCoeff_le hlowerCoeff_le hlowerCoeff_nonneg hUpper_rhs_nonneg
    have hdecay_sq_le : decay * decay ≤ decay := by
      calc
        decay * decay ≤ decay * 1 :=
          mul_le_mul_of_nonneg_left hdecay_le_one hdecay_nonneg
        _ = decay := by ring
    have hDD_nonneg : 0 ≤ D * D := mul_nonneg hD_nonneg hD_nonneg
    calc
      upperCoeff * lowerCoeff ≤ (D * decay) * (D * decay) := hprod_step
      _ = (D * D) * (decay * decay) := by ring
      _ ≤ (D * D) * decay := mul_le_mul_of_nonneg_left hdecay_sq_le hDD_nonneg
      _ = D * D * decay := by ring
  have hCoeff_le :
      upperCoeff + lowerCoeff + upperCoeff * lowerCoeff ≤ C * decay := by
    dsimp [C]
    nlinarith
  have hupper_gt : hP4β.sUpper < hP4.sUpper + 2 * β0 := by
    change hP4.sUpper + section53CoarseFluctuationBeta hP4 <
      hP4.sUpper + 2 * β0
    dsimp [β0]
    linarith [section53CoarseFluctuationBeta_pos hP4]
  have hlower_gt : hP4β.sLower < hP4.sLower + 2 * β0 := by
    change hP4.sLower + section53CoarseFluctuationBeta hP4 <
      hP4.sLower + 2 * β0
    dsimp [β0]
    linarith [section53CoarseFluctuationBeta_pos hP4]
  have hShifted :=
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_P4_positiveExcess_bounds
      hP hStruct hP4β
      hupper_gt
      (by simpa [β0] using sUpper_add_two_beta_lt_one' hP4)
      hlower_gt
      (by simpa [β0] using sLower_add_two_beta_lt_one' hP4)
      m hupperCoeff_nonneg hlowerCoeff_nonneg
      (by simpa [hP4β, betaShiftedP4, β0, upperCoeff] using hBounds.1)
      (by simpa [hP4β, betaShiftedP4, β0, lowerCoeff] using hBounds.2)
      hCoeff_le
  simpa [shiftedWidetildeThetaAtScale, hP4β, betaShiftedP4, β0, hβeq,
    decay] using hShifted

theorem shiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {η : ℝ} (hUpper : 0 < hP4.sUpper + η)
    (hLower : 0 < hP4.sLower + η) (k m : ℕ) :
    shiftedWidetildeThetaAtScale (Ch04.restrictionScaleNormalizedLaw k P) (m : ℤ)
        (hP4.scaleNormalized hP hStruct k) η =
      shiftedWidetildeThetaAtScale P ((k + m : ℕ) : ℤ) hP4 η := by
  have h :=
    Ch04.widetildeThetaAtScale_restrictionScaleNormalizedLaw hP k m
      hUpper hLower hP4.xi
  simpa [shiftedWidetildeThetaAtScale,
    QuantitativeCoarseGrainedEllipticity.scaleNormalized] using h

theorem twoBetaShiftedWidetildeThetaAtScale_shifted_bound_homogenizationScale
    {d : ℕ} [NeZero d] (xi : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P),
        hP4.xi = xi →
        section53CoarseFluctuationBeta hP4 = β →
        ∀ {k n : ℕ}, k ≤ n →
          shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β) ≤
            thetaAtScale hP hStruct (k : ℤ) +
              C * Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ)) *
                shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    twoBetaShiftedWidetildeThetaAtScale_zero_bound_homogenizationScale
      (d := d) xi β hβ
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 hxi hβeq k n hkn
  let Pk := Ch04.restrictionScaleNormalizedLaw k P
  let hPk := hP.scaleNormalized k
  let hStructPk := hStruct.scaleNormalized k
  let hP4k := hP4.scaleNormalized hP hStruct k
  let m : ℕ := n - k
  have hxi_k : hP4k.xi = xi := by
    simpa [hP4k, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using hxi
  have hβ_k : section53CoarseFluctuationBeta hP4k = β := by
    simpa [hP4k, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using! hβeq
  have hbound := hC hPk hStructPk hP4k hxi_k hβ_k m
  have htwo :
      shiftedWidetildeThetaAtScale Pk (m : ℤ) hP4k (2 * β) =
        shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β) := by
    have h :=
      shiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw hP hStruct hP4
        (η := 2 * β)
        (by linarith [hP4.sUpper_pos, hβ])
        (by linarith [hP4.sLower_pos, hβ]) k m
    simpa [Pk, hP4k, m, Nat.add_sub_of_le hkn] using h
  have hone :
      shiftedWidetildeThetaAtScale Pk 0 hP4k β =
        shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β := by
    have h :=
      shiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw hP hStruct hP4
        (η := β)
        (by linarith [hP4.sUpper_pos, hβ])
        (by linarith [hP4.sLower_pos, hβ]) k 0
    simpa [Pk, hP4k] using h
  have htheta := thetaAtScale_zero_restrictionScaleNormalizedLaw hP hStruct k
  calc
    shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β)
        = shiftedWidetildeThetaAtScale Pk (m : ℤ) hP4k (2 * β) := htwo.symm
    _ ≤ thetaAtScale hPk hStructPk 0 +
          C * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            shiftedWidetildeThetaAtScale Pk 0 hP4k β := hbound
    _ = thetaAtScale hP hStruct (k : ℤ) +
          C * Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ)) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β := by
      simp [Pk, hP4k, m, htheta, hone]

end

end Section55
end Ch05
end Book
end Homogenization
