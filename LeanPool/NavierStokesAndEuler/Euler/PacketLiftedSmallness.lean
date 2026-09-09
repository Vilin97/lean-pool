/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionRapidDecay

@[expose] public section

/-! The literal correction target and a fixed inverse-frequency packet
amplitude give the small lifted velocity required by the finite flow
bootstrap. All source constants remain fixed as frequency increases. -/

noncomputable section

namespace EulerPacketSourceFrequency

open Real Filter EulerPacketCorrectionScalar
open scoped Topology

def liftedAmplitude (C E k : ℝ) : ℝ := C/k + E*delta (expansion k)

theorem fixed_div_eventually_le_inverse_half (C : ℝ) :
    ∀ᶠ k : ℝ in atTop, C/k ≤ k^(-(1/2 : ℝ)) := by
  filter_upwards [(_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually_ge_atTop C,
    eventually_gt_atTop (0 : ℝ)] with k hC hk
  apply (div_le_iff₀ hk).mpr
  have he : k^(-(1/2 : ℝ))*k = k^(1/2 : ℝ) := by
    calc
      _ = k^(-(1/2 : ℝ))*k^(1 : ℝ) := by rw [Real.rpow_one]
      _ = k^(-(1/2 : ℝ)+1) := (Real.rpow_add hk _ _).symm
      _ = _ := by norm_num
  rwa [he]

theorem liftedAmplitude_nonneg (C E k : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hk : 0 ≤ k) :
    0 ≤ liftedAmplitude C E k := by
  unfold liftedAmplitude
  exact add_nonneg (div_nonneg hC hk) (mul_nonneg hE (delta_pos (expansion k)).le)

theorem liftedAmplitude_eventually_le_inverse_half (C E : ℝ) :
    ∀ᶠ k : ℝ in atTop, liftedAmplitude C E k ≤ 2*k^(-(1/2 : ℝ)) := by
  filter_upwards [fixed_div_eventually_le_inverse_half C,
    correction_eventually_lt_inverse_power E (1/2)] with k hC hE
  have h := add_le_add hC hE.le
  simpa only [liftedAmplitude, two_mul] using h

theorem liftedAmplitude_small_eventually (C E R T : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∀ᶠ k : ℝ in atTop, 4 ≤ k ∧ 0 ≤ liftedAmplitude C E k ∧
      liftedAmplitude C E k ≤ 2*k^(-(1/2 : ℝ)) ∧
      liftedAmplitude C E k*R*T ≤ 1/8 := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    liftedAmplitude_eventually_le_inverse_half C E,
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually_ge_atTop (16*R*T)]
    with k hk hb hroot
  have hk0 : 0 < k := by linarith
  have hp : 0 < k^(1/2 : ℝ) := Real.rpow_pos_of_pos hk0 _
  refine ⟨hk, liftedAmplitude_nonneg C E k hC hE hk0.le, hb, ?_⟩
  calc
    _ ≤ (2*k^(-(1/2 : ℝ)))*R*T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hR) hT
    _ = (2*R*T)/k^(1/2 : ℝ) := by rw [Real.rpow_neg hk0.le]; ring
    _ ≤ 1/8 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith

end EulerPacketSourceFrequency
