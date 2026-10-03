/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityRadiusExtension
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalBudgetScales

/-! # Iterates Velocity Physical Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- The stream-regularity estimates supply the actual velocity-gradient scale. -/
theorem iterate_velocity_gradMatrix_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ t x j k, |gradMatrix (streamVel (Φ (m - 1)) t) x j k| ≤
      (2 : ℝ) ^ 21 * a β I.Λ (m - 1) := by
  intro t x j k
  have hb := iterate_velocity_analytic_profile_of_A3 I hΦ hm hA3 t [j] (by simp) x k
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
    pow_one, mul_one, iterateSpatialWord] at hb
  rw [iterate_velocity_first_jet_scale he.ne'] at hb
  exact hb

/-- Positive-order stream-regularity jets extend to the common inflated flow radius while keeping
 the physical first-jet product fixed. -/
theorem iterate_velocity_extended_profile_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {r : ℝ} (hr : 0 < r) (hle : 256 * (epsilon β I.Λ (m - 1))⁻¹ ≤ r) :
    ∀ t x p, 1 ≤ p.length → ∀ j,
      |iterateSpatialWord p (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
        (((2 : ℝ) ^ 21 * a β I.Λ (m - 1)) / r) * (p.length.factorial : ℝ) * r ^ p.length := by
  intro t x p hp j
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hb := iterate_positive_profile_radius_extension (by positivity :
      0 ≤ 8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1))
    (by positivity : 0 < 256 * (epsilon β I.Λ (m - 1))⁻¹) hr hle hp
    (iterate_velocity_analytic_profile_of_A3 I hΦ hm hA3 t p hp x j)
  rw [iterate_velocity_first_jet_scale he.ne'] at hb
  exact hb

end AVenhance.Infra.Section4
