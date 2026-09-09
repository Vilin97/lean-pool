/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Real.Sqrt
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Packet Scale Activation
-/

@[expose] public section

noncomputable section

namespace EulerPacketScaleActivation

open Real EulerPacketScaleGeometry

/-- The actual quadratic target and frame invariant imply every basic
small-beta and target-time guard used in the scalar ODE estimates. -/
theorem source_activation_ode_guards {j x β : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    0 < β ∧ β ≤ 1 / 16 ∧ 0 < sqrt β ∧ sqrt β ≤ 1 / 4 ∧
    1 / sqrt β ≤ (j ^ 2 * x) / sqrt β ∧
    (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 ∧
    0 < 1 / (j ^ 2 * x) ∧ 1 / (j ^ 2 * x) ≤ 1 / 2 := by
  have hxp : 0 < x := by linarith
  have hjp : 0 < j := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hx64 : 64 ≤ x ^ 2 := by nlinarith only [hx]
  have hm := mul_le_mul_of_nonneg_left hx64 hβ.le
  have hβsmall : β ≤ 1 / 16 := by nlinarith only [hm, hβx₂]
  have hσ : 0 < sqrt β := sqrt_pos.mpr hβ
  have hσsmall : sqrt β ≤ 1 / 4 := (sqrt_le_iff).2 ⟨by norm_num, by nlinarith only [hβsmall]⟩
  have hj2 : 9 ≤ j ^ 2 := by nlinarith only [hj]
  have hX : 2 ≤ j ^ 2 * x := by
    have hh := mul_le_mul hj2 hx (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg j)
    nlinarith only [hh]
  have htLow : 1 / sqrt β ≤ (j ^ 2 * x) / sqrt β :=
    div_le_div_of_nonneg_right (by linarith only [hX]) hσ.le
  have htime := activation_time_bounds (a := 1) (H := 1) (β := β) (x := x) (X := j ^ 2 * x)
    (by norm_num) (by norm_num) (by norm_num) hxp (by positivity) hβx hβx₂
  norm_num only [mul_one, sqrt_one, div_one] at htime
  have htUp : (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 := by nlinarith only [htime.2]
  have hy : 0 < 1 / (j ^ 2 * x) := by positivity
  have hy₂ : 1 / (j ^ 2 * x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < j ^ 2 * x)).2
    nlinarith only [hX]
  exact ⟨hβ, hβsmall, hσ, hσsmall, htLow, htUp, hy, hy₂⟩

/-- The source polynomial horizon contains the target activation time. -/
theorem source_activation_within_horizon {j x β C : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x) (hC : 2 ≤ C)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    1 ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      (j ^ 2 * x) / sqrt β ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      β * ((j ^ 2 * x) / sqrt β) ^ 2 = (j ^ 2 * x) ^ 2 := by
  obtain ⟨hβ, _, _, _, _, ht, _, _⟩ := source_activation_ode_guards hj hx hβx hβx₂
  have hn : 0 ≤ j ^ 2 * x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hC (by nlinarith only [hn] : 0 ≤ 1 + j ^ 2 * x ^ 2)
  refine ⟨by nlinarith only [hh, hn], by nlinarith only [ht, hh], ?_⟩
  rw [div_pow, sq_sqrt hβ.le]
  field_simp

end EulerPacketScaleActivation
