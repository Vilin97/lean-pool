/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ScalarLoss

/-! # Uniform -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open Section53.JUpperBoundCoarseFluctuations

noncomputable section

private theorem sUpper_add_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hlower_beta_pos :
      0 < hP4.sLower + section53CoarseFluctuationBeta hP4 :=
    add_pos hP4.sLower_pos (section53CoarseFluctuationBeta_pos hP4)
  nlinarith

private theorem sLower_add_beta_lt_one' {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hupper_beta_pos :
      0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 :=
    add_pos hP4.sUpper_pos (section53CoarseFluctuationBeta_pos hP4)
  nlinarith

/-- Uniform shifted-window version of the Section 5.5 shifted `widetildeTheta`
bound.

The constant is chosen after the explicit parameters `xi` and `β`, and before
the law and all scale parameters. -/
theorem shiftedWidetildeThetaAtScale_shifted_bound_homogenizationScale
    {d : ℕ} [NeZero d] (xi : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P),
        hP4.xi = xi →
        section53CoarseFluctuationBeta hP4 = β →
        ∀ {k n : ℕ}, k ≤ n →
          shiftedWidetildeThetaAtScale P (n : ℤ) hP4 β ≤
            thetaAtScale hP hStruct (k : ℤ) +
              C * Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ)) *
                widetildeThetaAtScale P (k : ℤ) hP4 := by
  obtain ⟨C52, hC52_nonneg, hC52⟩ :=
    betaShiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_section52TwoExponent_error
      (d := d)
  let D : ℝ := 2 * C52 * (xi : ℝ) * (β ^ 3)⁻¹
  let C : ℝ := D + D + D * D
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hD_nonneg hD_nonneg]
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 hxi hβeq k n hkn
  let Pk := Ch04.restrictionScaleNormalizedLaw k P
  let hPk := hP.scaleNormalized k
  let hStructPk := hStruct.scaleNormalized k
  let hP4k := hP4.scaleNormalized hP hStruct k
  have hxi_k : hP4k.xi = xi := by
    simpa [hP4k, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using hxi
  have hβ_k : section53CoarseFluctuationBeta hP4k = β := by
    simpa [hP4k, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using! hβeq
  let m : ℕ := n - k
  let decay : ℝ := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let upperCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4k.xi C52 hP4k.sUpper
      (hP4k.sUpper + section53CoarseFluctuationBeta hP4k) m
  let lowerCoeff : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4k.xi C52 hP4k.sLower
      (hP4k.sLower + section53CoarseFluctuationBeta hP4k) m
  let upperLoss : ℝ :=
    section52MomentLossCoeff d hP4k.xi hP4k.sUpper
      (hP4k.sUpper + section53CoarseFluctuationBeta hP4k)
  let lowerLoss : ℝ :=
    section52MomentLossCoeff d hP4k.xi hP4k.sLower
      (hP4k.sLower + section53CoarseFluctuationBeta hP4k)
  have hbase := hC52 hPk hStructPk hP4k m
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hdecay_le_one : decay ≤ 1 := by
    dsimp [decay]
    exact rpow_three_neg_beta_nat_le_one hβ.le m
  have hupperLoss_le : upperLoss ≤ 2 * (xi : ℝ) * (β ^ 3)⁻¹ := by
    dsimp [upperLoss]
    simpa [hxi_k, hβ_k] using
      section52MomentLossCoeff_upper_beta_shift_le_xi_beta_cubed hP4k
  have hlowerLoss_le : lowerLoss ≤ 2 * (xi : ℝ) * (β ^ 3)⁻¹ := by
    dsimp [lowerLoss]
    simpa [hxi_k, hβ_k] using
      section52MomentLossCoeff_lower_beta_shift_le_xi_beta_cubed hP4k
  have hupperCoeff_loss :
      upperCoeff ≤ (C52 * upperLoss) * decay := by
    dsimp [upperCoeff, upperLoss, decay]
    simpa [hβ_k] using
      section52TwoExponentMomentBoundCoeff_upper_beta_shift_le_loss_beta_decay
        hP4k hC52_nonneg m
  have hlowerCoeff_loss :
      lowerCoeff ≤ (C52 * lowerLoss) * decay := by
    dsimp [lowerCoeff, lowerLoss, decay]
    simpa [hβ_k] using
      section52TwoExponentMomentBoundCoeff_lower_beta_shift_le_loss_beta_decay
        hP4k hC52_nonneg m
  have hupperCoeff_le : upperCoeff ≤ D * decay := by
    calc
      upperCoeff ≤ (C52 * upperLoss) * decay := hupperCoeff_loss
      _ ≤ (C52 * (2 * (xi : ℝ) * (β ^ 3)⁻¹)) * decay := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hupperLoss_le hC52_nonneg) hdecay_nonneg
      _ = D * decay := by
        dsimp [D]
        ring
  have hlowerCoeff_le : lowerCoeff ≤ D * decay := by
    calc
      lowerCoeff ≤ (C52 * lowerLoss) * decay := hlowerCoeff_loss
      _ ≤ (C52 * (2 * (xi : ℝ) * (β ^ 3)⁻¹)) * decay := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlowerLoss_le hC52_nonneg) hdecay_nonneg
      _ = D * decay := by
        dsimp [D]
        ring
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4k.xi) (m := m) (C := C52)
      (s := hP4k.sUpper)
      (r := hP4k.sUpper + section53CoarseFluctuationBeta hP4k)
      hC52_nonneg hP4k.sUpper_pos
      (by simpa using sUpper_add_beta_lt_one' hP4k) hP4k.two_le_dim
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4k.xi) (m := m) (C := C52)
      (s := hP4k.sLower)
      (r := hP4k.sLower + section53CoarseFluctuationBeta hP4k)
      hC52_nonneg hP4k.sLower_pos
      (by simpa using sLower_add_beta_lt_one' hP4k) hP4k.two_le_dim
  have hprod_le : upperCoeff * lowerCoeff ≤ D * D * decay := by
    have hDdecay_nonneg : 0 ≤ D * decay := mul_nonneg hD_nonneg hdecay_nonneg
    have hstep : upperCoeff * lowerCoeff ≤ (D * decay) * (D * decay) :=
      mul_le_mul hupperCoeff_le hlowerCoeff_le hlowerCoeff_nonneg hDdecay_nonneg
    have hdecay_sq_le : decay * decay ≤ decay := by
      calc
        decay * decay ≤ decay * 1 :=
          mul_le_mul_of_nonneg_left hdecay_le_one hdecay_nonneg
        _ = decay := by ring
    have hDD_nonneg : 0 ≤ D * D := mul_nonneg hD_nonneg hD_nonneg
    calc
      upperCoeff * lowerCoeff ≤ (D * decay) * (D * decay) := hstep
      _ = (D * D) * (decay * decay) := by ring
      _ ≤ (D * D) * decay :=
        mul_le_mul_of_nonneg_left hdecay_sq_le hDD_nonneg
      _ = D * D * decay := by ring
  have hCoeff_le :
      upperCoeff + lowerCoeff + upperCoeff * lowerCoeff ≤ C * decay := by
    dsimp [C]
    nlinarith
  have hW0_nonneg : 0 ≤ widetildeThetaAtScale Pk 0 hP4k := by
    unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
    exact mul_nonneg
      (Ch04.LambdaMomentAtScale_nonneg Pk 0 hP4k.xi hP4k.sUpper_pos)
      (Ch04.lambdaInvMomentAtScale_nonneg Pk 0 hP4k.xi hP4k.sLower_pos)
  have hbound_pk :
      betaShiftedWidetildeThetaAtScale Pk (m : ℤ) hP4k ≤
        thetaAtScale hPk hStructPk 0 +
          C * decay * widetildeThetaAtScale Pk 0 hP4k := by
    calc
      betaShiftedWidetildeThetaAtScale Pk (m : ℤ) hP4k
          ≤ thetaAtScale hPk hStructPk 0 +
            (upperCoeff + lowerCoeff + upperCoeff * lowerCoeff) *
              widetildeThetaAtScale Pk 0 hP4k := by
            simpa [upperCoeff, lowerCoeff, m] using hbase
      _ ≤ thetaAtScale hPk hStructPk 0 +
            (C * decay) * widetildeThetaAtScale Pk 0 hP4k := by
            have hmul := mul_le_mul_of_nonneg_right hCoeff_le hW0_nonneg
            nlinarith
      _ = thetaAtScale hPk hStructPk 0 +
            C * decay * widetildeThetaAtScale Pk 0 hP4k := by ring
  have hshift :=
    betaShiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw_of_le hP hStruct hP4 hkn
  have htheta := thetaAtScale_zero_restrictionScaleNormalizedLaw hP hStruct k
  have hw0 := widetildeThetaAtScale_zero_restrictionScaleNormalizedLaw hP hStruct hP4 k
  have hbound := hbound_pk
  rw [hshift] at hbound
  rw [hw0] at hbound
  simpa [Pk, hPk, hStructPk, hP4k, m, decay, thetaAtScale,
    widetildeThetaAtScale, shiftedWidetildeThetaAtScale,
    betaShiftedWidetildeThetaAtScale, htheta, hβeq] using hbound

end

end Section55
end Ch05
end Book
end Homogenization
