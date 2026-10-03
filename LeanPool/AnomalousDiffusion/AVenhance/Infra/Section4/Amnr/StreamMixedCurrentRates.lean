/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TransportedGradientInduction

/-! Actual mixed stream rates on the current material-amplitude scale. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- One source constant absorbs every fine cutoff time derivative. -/
def amnrStreamMixedCurrentConstant {β : ℝ} (I : AVenhance.Ingredients β) : ℝ :=
  amnrFastSpatialConstant I * (2 * max 1 (amnrFineMaterialConstant β)) ^ AVenhance.Nstar β

theorem amnrStreamMixedCurrentConstant_pos {β : ℝ} (I : AVenhance.Ingredients β) :
    0 < amnrStreamMixedCurrentConstant I := by
  have := amnrFastSpatialConstant_pos I
  have : 0 < max 1 (amnrFineMaterialConstant β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold amnrStreamMixedCurrentConstant
  positivity

/-- Every fine-time power is controlled by the actual current amplitude. -/
theorem amnr_fine_time_power_le_current {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {r N : ℕ} (hr : r ≤ N) :
    (2 : ℝ) ^ r * (AVenhance.tau β I.Λ m)⁻¹ ^ r ≤
      (2 * max 1 (amnrFineMaterialConstant β)) ^ N * AVenhance.a β I.Λ m ^ r := by
  let K := max 1 (amnrFineMaterialConstant β)
  have hK : 1 ≤ K := le_max_left _ _
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hτ := I.tau_pos' m
  have hbase : 2 * (AVenhance.tau β I.Λ m)⁻¹ ≤ (2 * K) * AVenhance.a β I.Λ m := by
    have hh := (amnr_inverse_tau_le_current_amplitude I hm).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 _) hA.le)
    convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2) using 1
    ring
  have hh := pow_le_pow_left₀ (show 0 ≤ 2 * (AVenhance.tau β I.Λ m)⁻¹ by positivity) hbase r
  rw [mul_pow, mul_pow] at hh
  refine hh.trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith : 1 ≤ 2 * K) hr)
    (pow_nonneg hA.le r)

/-- Actual canonical mixed stream jets use only the construction and the stream-regularity
    estimates.
The fine cutoff rate is absorbed into the current material amplitude. -/
theorem amnr_streamIncrement_mixed_current_abs_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (α : List (Fin 2)) (r : ℕ)
    (hbudget : α.length + 2 * r ≤ AVenhance.Nstar β) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord α r)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      (amnrStreamMixedCurrentConstant I * AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r := by
  have hh := amnr_streamIncrement_mixed_abs_le_of_A3 I hΦ hreg hm α r hbudget z
  have hp := amnr_fine_time_power_le_current I hm (N := AVenhance.Nstar β) (by omega : r ≤
      AVenhance.Nstar β)
  have hK := amnrFastSpatialConstant_pos I
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hd := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ amnrFastSpatialConstant I * AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 *
      (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length by positivity)
  refine hh.trans ?_
  convert hd using 1 <;> dsimp [amnrFastSpatialConstant, amnrStreamMixedCurrentConstant] <;> ring

end AVenhance.Infra.Section4
