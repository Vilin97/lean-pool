/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.MaterialPowerChange

/-! All spatial orders in the first material fast-velocity estimate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The previous spatial radius is no larger than the current one. -/
theorem amnr_epsilon_inverse_prev_le_current {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ≤ (AVenhance.epsilon β I.Λ m)⁻¹ := by
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hs := AVenhance.Infra.Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  rw [Nat.sub_add_cancel hm] at hs
  have hL : 1 ≤ (I.Λ : ℝ) := by exact_mod_cast (show 1 ≤ I.Λ by have := I.two_pow_seven_le; omega)
  exact inv_anti₀ hE ((le_mul_of_one_le_left hE.le hL).trans hs)

/-- Uniform transported spatial amplitude through the finite source budget. -/
def amnrFastSpatialConstant {β : ℝ} (I : AVenhance.Ingredients β) : ℝ :=
  3 * I.Chat * I.Czeta * amnrTransportSpatialConstant (AVenhance.Nstar β)

theorem amnrFastSpatialConstant_pos {β : ℝ} (I : AVenhance.Ingredients β) :
    0 < amnrFastSpatialConstant I := by
  have := I.one_le_Chat
  have := I.one_le_Czeta
  have := amnrTransportSpatialConstant_pos (AVenhance.Nstar β)
  unfold amnrFastSpatialConstant
  positivity

/-- Abstract radius cancellation converts the stream amplitude into the
actual fast-velocity amplitude without changing its spatial derivative order. -/
theorem amnr_stream_amplitude_spatial_cancel {E A β : ℝ} (hE : 0 < E)
    (hA : A * E = E ^ (β - 1)) (n : ℕ) :
    A * E ^ 2 * E⁻¹ ^ (n + 1) = E ^ (β - 1) * E⁻¹ ^ n := by
  rw [pow_succ]
  calc
    _ = (A * E) * (E * E⁻¹) * E⁻¹ ^ n := by ring
    _ = _ := by rw [mul_inv_cancel₀ hE.ne', mul_one, hA]

end AVenhance.Infra.Section4
