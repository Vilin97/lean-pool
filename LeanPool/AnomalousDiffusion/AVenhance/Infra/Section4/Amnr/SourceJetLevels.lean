/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherGradientStep

/-! Actual finite-level source jets and their proved spatial base case. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Induction invariant for the actual velocity and its actual gradient.
The velocity drift is excluded and each field pays its stream derivative cost. -/
structure AmnrSourceJetLevels {β : ℝ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (K : ℝ) (cut : ℕ) : Prop where
  velocity : ∀ m α r, r ≤ cut → amnrMixedWord α r ≠ [] →
    α.length + 2 * r + 1 ≤ AVenhance.Nstar β → ∀ i z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
        K * AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r
  gradient : ∀ m α r, r ≤ cut → α.length + 2 * r + 2 ≤ AVenhance.Nstar β → ∀ i p z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z| ≤
        K * AVenhance.a β I.Λ m * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
          AVenhance.a β I.Λ m ^ r

theorem amnrSourceJetLevels_spatial {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    AmnrSourceJetLevels I Φ (max 1 (amnrSpatialVelocityConstant (AVenhance.Nstar β))) 0 := by
  have hK : amnrSpatialVelocityConstant (AVenhance.Nstar β) ≤
      max 1 (amnrSpatialVelocityConstant (AVenhance.Nstar β)) := le_max_right _ _
  constructor
  · intro m α r hr hne hbudget i z
    have hr0 : r = 0 := by omega
    subst r
    have hα : α ≠ [] := by
      intro hh
      apply hne
      simp [hh, amnrMixedWord]
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil, pow_zero, mul_one,
      Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [amnr_streamVelocity_zero_word I hΦ]
      simp only [Pi.zero_apply, abs_zero]
      positivity
    · have hh := amnr_velocity_nonempty_spatial_abs_le_of_A3 I hΦ hreg (m := m)
        (by omega) α hα hbudget i z
      exact hh.trans (by gcongr)
  · intro m α r hr hbudget i p z
    have hr0 : r = 0 := by omega
    subst r
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil, pow_zero, mul_one,
      Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [amnr_streamGradient_zero_word I hΦ]
      simp only [Pi.zero_apply, abs_zero]
      positivity
    · have hh := amnr_velocityGradient_spatial_le_of_A3 I hΦ hreg (m := m)
        (by omega) α hbudget i p z
      exact hh.trans (by gcongr)

end AVenhance.Infra.Section4
