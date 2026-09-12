/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalPacketParameters
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialScaleSummability
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin

/-! The same normal-stage frequency comparison also supplies the
parent-label and physical support-scale inequalities for the child flow. -/

@[expose] public section


noncomputable section

namespace EulerNormalPacketParameters

open Real EulerPacketLowConstants EulerParentPacketParameterCaps EulerPacketUniformSource
  EulerPacketSourceFrequency EulerPacketSourceParameterScales EulerPacketUniformFrequencyScales
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence

theorem sourceConstant_one (C : ℝ) : 1 ≤ sourceConstant C := by
  have hb := boundaryConstant_pos gradientConstant gradient_nonneg
  have ht := terminalCap_one
  have hp : 0 ≤ (2*C)^10 := by positivity
  unfold sourceConstant EulerPacketParameterEnvelope.boundConstant
  linarith only [hb,ht,hp]

theorem exponential_le_envelope (J : ℕ) (hJ : 1 ≤ J) (C X c : ℝ)
    (hX : 1 ≤ X) (hc : c ≤ 320) (n : ℕ) :
    exp (c*predecessorExponent J X n) ≤ envelope J C X n := by
  have hz := predecessorExponent_nonneg J hJ X hX n
  have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hz)
  have hp := one_le_mul_of_one_le_of_one_le (sourceConstant_one C)
    (polynomialFactor_one J hJ X hX n)
  apply he.trans
  have h := le_mul_of_one_le_left (exp_pos (320*predecessorExponent J X n)).le hp
  convert h using 1
  unfold envelope parameterEnvelope polynomialFactor predecessorExponent
  ring

theorem envelope_one (J : ℕ) (hJ : 1 ≤ J) (C X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    1 ≤ envelope J C X n := by
  have h := exponential_le_envelope J hJ C X 0 hX (by norm_num) n
  simpa only [zero_mul,exp_zero] using h

theorem envelope_le_smallPower (J : ℕ) (hJ : 1 ≤ J) (C X : ℝ) (hX : 1 ≤ X) (n : ℕ)
    (hcost : (frequencySpec C).cost J (scaleSequence J X) n ≤ 1) :
    envelope J C X n ≤ smallPower (frequency J X n) := by
  have hE := envelope_one J hJ C X hX n
  have hguard := guard_of_cost_le J (1+frequencyConstant) (sourceConstant C) 320
    (add_pos_of_pos_of_nonneg zero_lt_one frequencyConstant_pos.le) (sourceConstant_pos C)
    20 1000 (frequencyPower+1) (theta/100) (by norm_num [theta]) X n hcost
  have hpow : envelope J C X n ≤ (envelope J C X n)^(frequencyPower+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hE (Nat.le_add_left 1 frequencyPower)
  have hC : 1 ≤ 1+frequencyConstant := le_add_of_nonneg_right frequencyConstant_pos.le
  exact (hpow.trans (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hE) _) hC)).trans hguard

theorem support_inverse_le_envelope (J : ℕ) (hJ : 2 ≤ J) (C X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    (supportScale J X n)⁻¹ ≤ envelope J C X n := by
  calc
    _ = exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ)) := by
      unfold supportScale
      rw [← exp_neg]
      congr 1
      ring
    _ ≤ exp (predecessorExponent J X n) := exp_le_exp.mpr
      (EulerPacketInitialScale.current_real_power_le_previous J hJ X hX n 3 (7/2) (by norm_num))
    _ ≤ _ := by
      simpa only [one_mul] using exponential_le_envelope J (by omega) C X 1 hX (by norm_num) n

theorem secondary_frequency_guards (J D : ℕ) (hJ : 2 ≤ J) (C X K : ℝ)
    (hX : 1 ≤ X) (n : ℕ)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (hK : K ≤ previousFrequency J D X n ^ 80)
    (hcost : (frequencySpec C).cost J (scaleSequence J X) n ≤ 1)
    (hk : 1 ≤ frequency J X n) :
    K ≤ frequency J X n ∧ (supportScale J X n)⁻¹ ≤ (frequency J X n)^(3/4 : ℝ) := by
  have henv := envelope_le_smallPower J (by omega) C X hX n hcost
  have hKE : K ≤ envelope J C X n := by
    have hp := previousFrequency_power_le J D hJ X 80 hX (by norm_num) hbase n
    have hK' : K ≤ previousFrequency J D X n^(80 : ℝ) := by simpa only [rpow_ofNat] using hK
    exact (hK'.trans hp).trans (exponential_le_envelope J (by omega) C X 80 hX (by norm_num) n)
  constructor
  · have hb := smallPower_le_power (frequency J X n) 1 hk (by norm_num [theta])
    simpa only [rpow_one] using (hKE.trans henv).trans hb
  · exact ((support_inverse_le_envelope J hJ C X hX n).trans henv).trans
      (smallPower_le_power (frequency J X n) (3/4) hk (by norm_num [theta]))

end EulerNormalPacketParameters
