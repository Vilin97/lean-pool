/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BasePacketUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales

@[expose] public section

/-! The manuscript's literal first-packet scales have a fixed monomial
frequency cost. The exponent and coefficient do not depend on J or X. -/

noncomputable section

namespace EulerBaseDatum

open Real Filter EulerPacketBaseGuardScales EulerPacketUniformSource EulerPacketSourceFrequency

theorem firstParameterSize_literal (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) :
    firstParameterSize (baseHorizon J X) (X^(-1010 : ℝ)) (X^1000) ≤
      (7+solutionLabelConstant)*X^1010 := by
  have hX0 := zero_le_one.trans hX
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hden : 1 ≤ 6*(J : ℝ)^2 := by nlinarith
  have hi : (6*(J : ℝ)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  have hT : (baseHorizon J X)⁻¹ ≤ X^498 := by
    unfold baseHorizon
    rw [mul_inv_rev,Real.rpow_neg hX0,inv_inv]
    norm_num only [Real.rpow_ofNat]
    exact (mul_le_mul_of_nonneg_left hi (pow_nonneg hX0 498)).trans_eq (mul_one _)
  have hd : (X^(-1010 : ℝ))⁻¹=X^1010 := by
    rw [Real.rpow_neg hX0,inv_inv]
    norm_num only [Real.rpow_ofNat]
  have ht : X^498 ≤ X^1010 := pow_le_pow_right₀ hX (by norm_num)
  have hh : X^1000 ≤ X^1010 := pow_le_pow_right₀ hX (by norm_num)
  have hK := solutionLabelConstant_one
  have hone : (1 : ℝ) ≤ X^1010 := one_le_pow₀ hX
  have hc : 4+solutionLabelConstant ≤ (4+solutionLabelConstant)*X^1010 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (by linarith : 0 ≤
      4+solutionLabelConstant)
  unfold firstParameterSize
  rw [hd]
  nlinarith only [hT.trans ht,hh,hc]

def firstFrequencyConstant : ℝ := frequencyConstant*(7+solutionLabelConstant)^frequencyPower
def firstFrequencyPower : ℕ := 1010*frequencyPower

theorem firstFrequencyConstant_pos : 0 < firstFrequencyConstant := by
  have hK := solutionLabelConstant_one
  unfold firstFrequencyConstant
  exact mul_pos frequencyConstant_pos (pow_pos (by linarith) _)

theorem first_frequency_cost_bound (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) :
    EulerPacketInitializedOutputCost.uniformConstant*
      (profileEnvelope (firstParameterSize (baseHorizon J X) (X^(-1010 : ℝ)) (X^1000)))^
        EulerPacketInitializedOutputCost.uniformPower ≤
          firstFrequencyConstant*X^firstFrequencyPower := by
  have hXpos := zero_lt_one.trans_le hX
  have hp := (firstParameterSize_bounds (baseHorizon J X) (X^(-1010 : ℝ)) (X^1000)
    (baseHorizon_pos J hJ hXpos) (Real.rpow_pos_of_pos hXpos _) (pow_nonneg hXpos.le _)).1
  apply (frequency_bound _ hp).trans
  calc
    _ ≤ frequencyConstant*((7+solutionLabelConstant)*X^1010)^frequencyPower := by
      apply mul_le_mul_of_nonneg_left _ frequencyConstant_pos.le
      exact pow_le_pow_left₀ (zero_le_one.trans hp) (firstParameterSize_literal J hJ X hX) _
    _ = _ := by
      unfold firstFrequencyConstant firstFrequencyPower
      rw [mul_pow,← pow_mul]
      ring

/-- This remaining threshold depends only on the fixed base exponent,
not on a parent or on a stage of the subsequent induction. -/
theorem first_frequency_guard_eventually (J : ℕ) (hJ : 1 ≤ J) (D : ℕ)
    (hD : (firstFrequencyPower : ℝ) < (D : ℝ)*(theta/100)) :
    ∀ᶠ X : ℝ in atTop,
      EulerPacketInitializedOutputCost.uniformConstant*
        (profileEnvelope (firstParameterSize (baseHorizon J X) (X^(-1010 : ℝ)) (X^1000)))^
          EulerPacketInitializedOutputCost.uniformPower ≤ smallPower (X^D) := by
  have hgap : 0 < (D : ℝ)*(theta/100)-(firstFrequencyPower : ℝ) := sub_pos.mpr hD
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (_root_.tendsto_rpow_atTop hgap).eventually_ge_atTop firstFrequencyConstant] with X hX hC
  have hXp := zero_lt_one.trans_le hX
  apply (first_frequency_cost_bound J hJ X hX).trans
  calc
    _ ≤ X^((D : ℝ)*(theta/100)-(firstFrequencyPower : ℝ))*X^firstFrequencyPower :=
      mul_le_mul_of_nonneg_right hC (pow_nonneg hXp.le _)
    _ = X^((D : ℝ)*(theta/100)) := by
      rw [← Real.rpow_natCast X firstFrequencyPower,← Real.rpow_add hXp]
      congr 1
      ring
    _ = smallPower (X^D) := by
      unfold smallPower
      rw [Real.rpow_mul hXp.le,Real.rpow_natCast]

end EulerBaseDatum
