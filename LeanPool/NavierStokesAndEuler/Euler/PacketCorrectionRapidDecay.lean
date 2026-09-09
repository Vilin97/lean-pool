/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! The actual correction target absorbs every fixed power of the frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceFrequency

open Real Filter EulerPacketCorrectionScalar
open scoped Topology

theorem sqrt_expansion_eq (k : ℝ) (hk : 0 ≤ k) :
    Real.sqrt (expansion k) = k^(theta/2) := by
  rw [expansion, Real.sqrt_eq_rpow, ← Real.rpow_mul hk]
  congr 1
  ring

/-- The target from the actual scalar construction decays faster than
every fixed inverse power; no rate is assumed as a separate hypothesis. -/
theorem delta_mul_rpow_tendsto_zero (p : ℝ) :
    Tendsto (fun k : ℝ => k^p*delta (expansion k)) atTop (𝓝 0) := by
  have h := (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (p/(theta/2)) 1 (by norm_num)).comp
      (_root_.tendsto_rpow_atTop (by norm_num [theta] : 0 < theta/2))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
  dsimp [Function.comp_def, delta]
  rw [sqrt_expansion_eq k hk.le, ← Real.rpow_mul hk.le]
  have hp : theta/2*(p/(theta/2))=p := by field_simp [theta]
  rw [hp]
  simp

/-- Any fixed source multiplier is eventually smaller than an arbitrary
fixed inverse power of the frequency. -/
theorem correction_eventually_lt_inverse_power (C p : ℝ) :
    ∀ᶠ k : ℝ in atTop, C*delta (expansion k) < k^(-p) := by
  have h := (delta_mul_rpow_tendsto_zero p).const_mul C
  have hsmall : ∀ᶠ k : ℝ in atTop, C*(k^p*delta (expansion k)) < 1 :=
    h.eventually (Iio_mem_nhds (by simp : C*0 < (1 : ℝ)))
  filter_upwards [hsmall,eventually_gt_atTop (0 : ℝ)] with k he hk
  rw [Real.rpow_neg hk.le]
  rw [← one_div]
  apply (lt_div_iff₀ (Real.rpow_pos_of_pos hk p)).mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he

/-- Fixed polynomial losses from physical differentiation or graph
restriction are absorbed by the same actual correction target. -/
theorem correction_with_power_loss_eventually (C loss p : ℝ) :
    ∀ᶠ k : ℝ in atTop, C*k^loss*delta (expansion k) < k^(-p) := by
  filter_upwards [correction_eventually_lt_inverse_power C (p+loss),
    eventually_gt_atTop (0 : ℝ)] with k he hk
  have hm := mul_lt_mul_of_pos_right he (Real.rpow_pos_of_pos hk loss)
  have hp : k^(-(p+loss))*k^loss=k^(-p) := by
    rw [← Real.rpow_add hk]
    congr 1
    ring
  rw [hp] at hm
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

end EulerPacketSourceFrequency
