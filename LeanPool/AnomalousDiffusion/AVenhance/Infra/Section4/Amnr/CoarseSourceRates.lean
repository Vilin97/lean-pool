/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.GradientScaleChange

/-! Actual lower source levels expressed at the current fine scale. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem amnrSourceJetLevels_coarse_gradient {β K : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ} {cut m : ℕ}
    (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 0 ≤ K) (hm : 1 ≤ m)
    (η : List (Fin 2)) (r : ℕ) (hr : r ≤ cut)
    (hbudget : η.length + 2 * r + 2 ≤ AVenhance.Nstar β) (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord η r)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) i p) z| ≤
        K * AVenhance.a β I.Λ m * (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length *
          AVenhance.a β I.Λ m ^ r := by
  have hh := hlevels.gradient (m - 1) η r hr hbudget i p z
  have hp := amnr_gradient_material_scale_antitone
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m))
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1))
    (amnr_epsilon_current_le_prev I hm) I.beta_lt η.length r
  have hs := mul_le_mul_of_nonneg_left hp hK
  apply hh.trans
  convert hs using 1 <;> dsimp [AVenhance.a] <;> ring

theorem amnrSourceJetLevels_coarse_velocity {β K : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ} {cut m : ℕ}
    (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 0 ≤ K) (hm : 1 ≤ m)
    (η : List (Fin 2)) (r : ℕ) (hr : r ≤ cut) (hne : amnrMixedWord η r ≠ [])
    (hbudget : η.length + 2 * r + 1 ≤ AVenhance.Nstar β) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord η r)
      (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i) z| ≤
        K * AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length * AVenhance.a β I.Λ m ^ r := by
  have hh := hlevels.velocity (m - 1) η r hr hne hbudget i z
  have hkr : 1 ≤ η.length + r := by
    by_contra hh
    have hη : η = [] := List.length_eq_zero_iff.mp (by omega)
    have hr0 : r = 0 := by omega
    apply hne
    simp [hη, hr0, amnrMixedWord]
  have hp := amnr_higher_velocity_scale_antitone
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m))
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1))
    (amnr_epsilon_current_le_prev I hm) I.beta_lt η.length r hkr
  have hs := mul_le_mul_of_nonneg_left hp hK
  apply hh.trans
  convert hs using 1 <;> dsimp [AVenhance.a] <;> ring

end AVenhance.Infra.Section4
