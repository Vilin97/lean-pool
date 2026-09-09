/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleSequence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! The literal base horizon and core radius satisfy the local-existence
and localized coercivity guards after the final choice of the base scale. -/

@[expose] public section


noncomputable section

namespace EulerPacketBaseGuardScales

open Filter Real EulerPacketBaseScales EulerPacketSourceScaleSequence
  EulerPacketSourceScaleChoice EulerPacketSourceScales
open scoped Topology

/-- Base horizon, given by `6*(J : ℝ)^2*X^(-498 : ℝ)`. -/
def baseHorizon (J : ℕ) (X : ℝ) : ℝ := 6*(J : ℝ)^2*X^(-498 : ℝ)

/-- Base radius, given by `X^(-1000 : ℝ)`. -/
def baseRadius (X : ℝ) : ℝ := X^(-1000 : ℝ)

/-- Base guard cost, given by `K*(baseHorizon J X^2/2)+Be*baseHorizon J X +
Cboundary*(CM*X^1000+2)*baseRadius X^3*baseHorizon J X`. -/
def baseGuardCost (J : ℕ) (K Be CM Cboundary X : ℝ) : ℝ :=
  K*(baseHorizon J X^2/2)+Be*baseHorizon J X +
    Cboundary*(CM*X^1000+2)*baseRadius X^3*baseHorizon J X

theorem baseHorizon_pos (J : ℕ) (hJ : 1 ≤ J) {X : ℝ} (hX : 0 < X) :
    0 < baseHorizon J X := by
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  unfold baseHorizon
  positivity

theorem baseRadius_pos {X : ℝ} (hX : 0 < X) : 0 < baseRadius X := rpow_pos_of_pos hX _

theorem baseHorizon_eq_timeWidth (J : ℕ) {X : ℝ} (hX : 0 < X) :
    baseHorizon J X=2*timeWidth J X 0 := by
  have hp : X^(1000 : ℕ)=(X^(500 : ℕ))^2 := by rw [← pow_mul]
  have hs : Real.sqrt (X^(1000 : ℕ))=X^(500 : ℕ) := by
    rw [hp,Real.sqrt_sq (pow_nonneg hX.le 500)]
  unfold baseHorizon timeWidth
  simp only [scaleSequence_succ,scaleSequence_zero,Nat.add_zero,previousShear,hs]
  rw [rpow_neg hX.le]
  norm_num only [rpow_ofNat]
  field_simp [hX.ne']
  ring

theorem baseHorizon_tendsto_zero (J : ℕ) : Tendsto (baseHorizon J) atTop (𝓝 0) := by
  have h := base_horizon_tendsto_zero (J : ℝ)
  norm_num only [show (2-1000/2 : ℝ)= -498 by norm_num] at h
  exact h

theorem baseRadius_tendsto_zero : Tendsto baseRadius atTop (𝓝 0) := by
  exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1000)

theorem baseGuardCost_tendsto_zero (J : ℕ) (K Be CM Cboundary : ℝ) :
    Tendsto (baseGuardCost J K Be CM Cboundary) atTop (𝓝 0) := by
  have hS := baseHorizon_tendsto_zero J
  have hr := baseRadius_tendsto_zero
  have hcore := base_core_volume_cost_tendsto_zero (J : ℝ)
  have hsmall := (hr.pow 3).mul hS
  have h := ((((hS.pow 2).div_const 2).const_mul K).add (hS.const_mul Be)).add
    ((hcore.const_mul (Cboundary*CM)).add (hsmall.const_mul (2*Cboundary)))
  norm_num only [zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,add_zero,
    zero_pow (by decide : 3 ≠ 0),zero_mul] at h
  convert! h using 1
  funext X
  unfold baseGuardCost baseRadius baseHorizon
  ring

theorem eventually_base_guards (J : ℕ) (hJ : 1 ≤ J)
    (K Be CM Cboundary T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 0 < baseHorizon J X ∧ baseHorizon J X ≤ T₀ ∧
      0 < baseRadius X ∧ baseRadius X ≤ 1/4 ∧
      baseGuardCost J K Be CM Cboundary X ≤ 1/2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (baseHorizon_tendsto_zero J).eventually_le_const hT₀,
    baseRadius_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1/4),
    (baseGuardCost_tendsto_zero J K Be CM Cboundary).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/2)] with X hX htime hr hguard
  have hXp : 0 < X := zero_lt_one.trans hX
  exact ⟨hX,baseHorizon_pos J hJ hXp,htime,baseRadius_pos hXp,hr,hguard⟩

end EulerPacketBaseGuardScales
