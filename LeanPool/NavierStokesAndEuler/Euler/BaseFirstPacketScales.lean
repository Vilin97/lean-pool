/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketUniversalFrequency
public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstLowBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import LeanPool.NavierStokesAndEuler.Euler.PacketLowBoundPropagation
import LeanPool.NavierStokesAndEuler.Euler.PacketLowConstants
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales

/-! The literal polynomial first-packet scales satisfy every local,
frequency and localized lower-bound guard after the final base choice. -/

section

/-! The manuscript's literal first-packet scales have a fixed monomial
frequency cost. The exponent and coefficient do not depend on J or X. -/

@[expose] public section

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
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (by
        linarith : 0 ≤ 4+solutionLabelConstant)
  unfold firstParameterSize
  rw [hd]
  nlinarith only [hT.trans ht,hh,hc]

/-- First frequency constant, given by
`frequencyConstant*(7+solutionLabelConstant)^frequencyPower`. -/
def firstFrequencyConstant : ℝ := frequencyConstant*(7+solutionLabelConstant)^frequencyPower
/-- First frequency power, given by `1010*frequencyPower`. -/
def firstFrequencyPower : ℕ := 1010*frequencyPower

theorem firstFrequencyConstant_pos : 0 < firstFrequencyConstant := by
  have hK := solutionLabelConstant_one
  unfold firstFrequencyConstant
  exact mul_pos frequencyConstant_pos (pow_pos (by linarith) _)

theorem first_frequency_cost_bound (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) :
    EulerPacketInitializedOutputCost.uniformConstant *
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
    (hD : (firstFrequencyPower : ℝ) < (D : ℝ) * (theta / 100)) :
    ∀ᶠ X : ℝ in atTop,
      EulerPacketInitializedOutputCost.uniformConstant *
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Real Filter EulerPacketBaseScales EulerPacketBaseGuardScales EulerPacketSourceFrequency
  EulerPacketUniformSource EulerPacketLowConstants EulerPacketLowBoundPropagation
  EulerPacketFirstLowBounds EulerMeanHarmonic
open scoped Topology

/-- Literal initial error, given by `(X^D)^(-(1/4 : ℝ))`. -/
def literalInitialError (D : ℕ) (X : ℝ) : ℝ := (X^D)^(-(1/4 : ℝ))

/-- Literal initial pressure cost, given by `2*initialCoefficientCost*X^(-1010 :
ℝ)*(X^1000*firstRatio)+literalInitialError D X`. -/
def literalInitialPressureCost (D : ℕ) (X : ℝ) : ℝ :=
  2*initialCoefficientCost*X^(-1010 : ℝ)*(X^1000*firstRatio)+literalInitialError D X

theorem literalInitialError_nonneg (D : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    0 ≤ literalInitialError D X := rpow_nonneg (pow_nonneg hX D) _

theorem literalInitialError_tendsto_zero (D : ℕ) (hD : 0 < D) :
    Tendsto (literalInitialError D) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_pow_atTop (Nat.ne_of_gt hD))

theorem literalInitialPressureCost_tendsto_zero (D : ℕ) (hD : 0 < D) :
    Tendsto (literalInitialPressureCost D) atTop (𝓝 0) := by
  have hp : Tendsto (fun X : ℝ => X^(-1010 : ℝ)*X^1000) atTop (𝓝 0) := by
    simpa only [pow_zero,mul_one] using base_power_decay 1 (-1010) 0 1000 (by norm_num)
  have h := (hp.const_mul (2*initialCoefficientCost*firstRatio)).add
    (literalInitialError_tendsto_zero D hD)
  simp only [mul_zero,zero_add] at h
  convert! h using 1
  funext X
  unfold literalInitialPressureCost
  ring

theorem literal_radius_frequency_bound (D : ℕ) (hD : 2000 ≤ D) (X : ℝ) (hX : 1 ≤ X) :
    (baseRadius X)⁻¹ ≤ (X^D)^(3/4 : ℝ) := by
  have hX0 := zero_le_one.trans hX
  have hDr : (2000 : ℝ) ≤ D := by exact_mod_cast hD
  unfold baseRadius
  rw [rpow_neg hX0,inv_inv]
  calc
    _ ≤ X^((D : ℝ)*(3/4 : ℝ)) := rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = _ := by rw [rpow_mul hX0,rpow_natCast]

/-- First scale guards data, collecting `x_one`, `radius_small`, `local_time`, `frequency`,
`label_frequency`, `radius_frequency` and their compatibility conditions. -/
structure FirstScaleGuards (J D : ℕ) (X : ℝ) : Prop where
  x_one : 1 ≤ X
  radius_small : baseRadius X ≤ 1/4
  local_time : baseHorizon J X ≤ initialTime
  frequency : UniversalFrequency (X^D)
  label_frequency : solutionLabelConstant ≤ X^D
  radius_frequency : (baseRadius X)⁻¹ ≤ (X^D)^(3/4 : ℝ)
  source_frequency : EulerPacketInitializedOutputCost.uniformConstant *
    (profileEnvelope (firstParameterSize (baseHorizon J X) (X^(-1010 : ℝ)) (X^1000)))^
      EulerPacketInitializedOutputCost.uniformPower ≤ smallPower (X^D)
  error_small : literalInitialError D X ≤ 1
  pressure_small : literalInitialPressureCost D X ≤ 1/4
  localized : (initialCoefficientCost+literalInitialPressureCost D X)*((baseHorizon J X)^2/2) +
    initialCoefficientCost*baseHorizon J X +
    boundaryLocalizationC2*(initialCoefficientCost+X^1000*firstRatio+literalInitialError D X) *
      (baseRadius X)^3*baseHorizon J X ≤ 1/2

theorem eventually_firstScaleGuards (J : ℕ) (hJ : 1 ≤ J) (D : ℕ) (hD : 2000 ≤ D)
    (hDfreq : (firstFrequencyPower : ℝ) < (D : ℝ) * (theta / 100)) :
    ∀ᶠ X : ℝ in atTop, FirstScaleGuards J D X := by
  have hDpos : 0 < D := by omega
  have hp : Tendsto (fun X : ℝ => X^D) atTop atTop := tendsto_pow_atTop (Nat.ne_of_gt hDpos)
  filter_upwards [eventually_base_guards J hJ (initialCoefficientCost+1) (initialCoefficientCost+1)
      gradientConstant boundaryLocalizationC2 initialTime initialTime_pos,
    hp.eventually universal_frequency_eventually,
    hp.eventually (eventually_ge_atTop solutionLabelConstant),
    first_frequency_guard_eventually J hJ D hDfreq,
    (literalInitialError_tendsto_zero D hDpos).eventually_le_const zero_lt_one,
    (literalInitialPressureCost_tendsto_zero D hDpos).eventually_le_const (by
        norm_num : (0 : ℝ) < 1/4)]
    with X hb hfreq hlabel hsource herr hpressure
  have hX : 1 ≤ X := hb.1.le
  have hX0 := zero_le_one.trans hX
  have hC0 := initialCoefficientCost_nonneg
  have he0 := literalInitialError_nonneg D X hX0
  have hc0 : 0 ≤ initialCoefficientCost+X^1000*firstRatio+literalInitialError D X := by
    positivity [firstRatio_pos]
  have hp0 : 0 ≤ literalInitialPressureCost D X := by
    unfold literalInitialPressureCost
    positivity [firstRatio_pos]
  have hcore := (initial_bounds (X^1000) (literalInitialError D X) (one_le_pow₀ hX) herr).1
  refine ⟨hX,hb.2.2.2.2.1,hb.2.2.1,hfreq,hlabel,literal_radius_frequency_bound D hD X hX,
    hsource,herr,hpressure,?_⟩
  apply localized_guard J X (initialCoefficientCost+literalInitialPressureCost D X)
    initialCoefficientCost (initialCoefficientCost+X^1000*firstRatio+literalInitialError D X)
    (initialCoefficientCost+1) (initialCoefficientCost+1) gradientConstant boundaryLocalizationC2
    (baseHorizon J X) (add_nonneg hC0 hp0) hC0 hc0 hb.2.1.le
    boundaryLocalizationC2_nonneg hb.2.2.2.1.le
  · linarith only [hpressure]
  · linarith
  · linarith only [hcore]
  · exact le_rfl
  · exact hb.2.2.2.2.2

end EulerBaseDatum
