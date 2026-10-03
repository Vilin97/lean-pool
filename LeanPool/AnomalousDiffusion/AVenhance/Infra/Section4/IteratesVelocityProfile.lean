/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPhysical

/-! Stream-regularity velocity jets in the factorial profile of the linear recurrence. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- The extra velocity factorial is absorbed by the printed denominator. -/
theorem iterate_velocity_factorial_profile {a e : ℝ} (ha : 0 ≤ a) (he : 0 < e) (n : ℕ) :
    32 * a * e ^ 2 * ((n + 1).factorial : ℝ) * (256 * e⁻¹) ^ (n + 1) /
      ((n : ℝ) + 2) ^ 2 ≤
      8192 * a * e * (n.factorial : ℝ) * (256 * e⁻¹) ^ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hf : ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2 ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < ((n : ℝ) + 2) ^ 2)).mpr
    nlinarith only [hn, sq_nonneg (n : ℝ)]
  have heq : 32 * a * e ^ 2 * ((n + 1).factorial : ℝ) * (256 * e⁻¹) ^ (n + 1) /
      ((n : ℝ) + 2) ^ 2 =
      (8192 * a * e * (n.factorial : ℝ) * (256 * e⁻¹) ^ n) *
        (((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp [he.ne']
    rw [pow_succ]
    field_simp
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans_eq (mul_one _)

/-- Every positive-order actual velocity jet has the source factorial-radius
profile needed in the binomially grouped material error estimate. -/
theorem iterate_velocity_analytic_profile_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (t : ℝ) (w : List (Fin 2)) (hw : 1 ≤ w.length) (x : Vec 2) (j : Fin 2) :
    |iterateSpatialWord w (fun y => streamVel (Φ (m - 1)) t y j) x| ≤
      8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) * (w.length.factorial : ℝ) *
        (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length := by
  have h := iterate_velocity_word_bound_of_A3 I hΦ hm hA3 t w hw x j
  norm_num only [show (2 : ℝ) ^ 5 = 32 by norm_num,
    show (2 : ℝ) ^ 8 = 256 by norm_num] at h
  exact h.trans (iterate_velocity_factorial_profile
    (AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) w.length)

end AVenhance.Infra.Section4
