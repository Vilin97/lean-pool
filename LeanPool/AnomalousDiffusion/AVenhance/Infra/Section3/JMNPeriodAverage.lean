/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic

/-! The unit-time average is also the average over an integer number of `4τ_m` periods. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance

/-- The reciprocal of `4τ_m` is a positive integer. -/
theorem four_tau_reciprocal_nat {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ N : ℕ, (N : ℝ) * (4 * tau β I.Λ m) = 1 := by
  obtain ⟨_, ⟨N, hN⟩⟩ := Infra.Ingredients.tauPP_ratio_and_tau_reciprocal
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hrecip : 1 / tau β I.Λ m = (4 * (N : ℝ)) := by
    exact_mod_cast hN
  have hmul : 1 = (4 * (N : ℝ)) * tau β I.Λ m :=
    (div_eq_iff (ne_of_gt hτ)).mp hrecip
  refine ⟨N, ?_⟩
  nlinarith [hmul]

/-- Integrating a continuous periodic function over an integer number of periods. -/
theorem intervalIntegral_unit_eq_period_mul {f : ℝ → ℝ} {P : ℝ} {N : ℕ}
    (hperiodic : Function.Periodic f P) (hcont : Continuous f)
    (hunit : (N : ℝ) * P = 1) :
    (∫ t in (0 : ℝ)..1, f t) =
      (N : ℝ) * (∫ t in (0 : ℝ)..P, f t) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hcont.intervalIntegrable a b
  have h := hperiodic.intervalIntegral_add_zsmul_eq (N : ℤ) 0 hint
  have hend : (N : ℤ) • P = 1 := by
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact hunit
  rw [hend] at h
  simpa [zsmul_eq_mul, Int.cast_natCast] using h

/-- The entries of `j_{m,n}` have the same average over a single `4τ_m` cell as on `[0,1]`.
The equality uses the exact integer subdivision encoded in `tau_m`. -/
theorem jMN_average_eq_period_average {β : ℝ} (I : Ingredients β)
    {m n : ℕ} (hm : 1 ≤ m) (κ : ℝ) (i j : Fin 2) :
    (∫ t in (0 : ℝ)..1, I.jMN κ m n t i j) =
      (4 * tau β I.Λ m)⁻¹ *
        (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), I.jMN κ m n t i j) := by
  obtain ⟨N, hN⟩ := four_tau_reciprocal_nat I hm
  have hper := jMN_period_four_tau I (m := m) κ n
  have hentry : Function.Periodic (fun t => I.jMN κ m n t i j)
      (4 * tau β I.Λ m) := by
    intro t
    exact congrFun (congrFun (hper t) i) j
  have heval : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hcont : Continuous (fun t => I.jMN κ m n t i j) :=
    heval.comp (jMN_continuous I m n κ)
  have hint := intervalIntegral_unit_eq_period_mul hentry hcont hN
  have hN0 : N ≠ 0 := by
    intro hzero
    subst N
    norm_num at hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  rw [hint]
  have hP : 0 < 4 * tau β I.Λ m :=
    mul_pos (by norm_num) (Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  have hNinv : (N : ℝ) = (4 * tau β I.Λ m)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hN
  rw [hNinv]

end AVenhance.Infra.Section3

end
