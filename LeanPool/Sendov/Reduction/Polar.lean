/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Reduction.Setup

/-!
# From the raw polar inequality to its `α`, `β(1)` form

This is `(1Q) ⟹ (lt)` of the blog post: the raw polar inequality

  `1 ≤ ∫₀¹ (a² + 2atx(1-a²) + t²(1-a²)²)^((n-1)/2) dt`

implies

  `1 ≤ ∫₀¹ exp(α(-1 + (2-β(1))t)) dt`.

The step is pointwise, and it is remarkably tight.  Writing `β(1) = 1 - 2ax + a²` and
`α = (n-1)(1-a²)/2`, one has the *identity*

  `1 + (1-a²)(-1 + (2-β(1))t) - P(t) = (1-a²)² (t - t²)`,

so the only inequality used in the whole implication is `t² ≤ t` on `[0,1]` — with equality at
both endpoints — followed by `1 + y ≤ exp y`.  Raising to the power `(n-1)/2` then turns
`(1-a²)/2 · (n-1)` into `α`.

The blog post states `(lt)` with a strict inequality.  Nothing downstream needs that: every
later use of `(beta-bound)` is non-strict, so this file proves the non-strict form and avoids
having to argue that the integrand is strictly smaller on a set of positive measure.

## Main statements

* `Sendov.Ppolar_le_lin`: the pointwise identity-with-`t² ≤ t`;
* `Sendov.polar_exp`: `(1Q) ⟹ (lt)`.
-/

public section

namespace Sendov

open MeasureTheory

variable {n : ℕ} {a x t α : ℝ}

/-- The pointwise bound `(at)`.  An identity apart from `t² ≤ t`. -/
lemma Ppolar_le_lin (a x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) := by
  have hid : 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) - Ppolar a x t
      = (1 - a ^ 2) ^ 2 * (t - t ^ 2) := by
    simp only [Ppolar, QQ]; ring
  nlinarith [mul_nonneg (sq_nonneg (1 - a ^ 2)) (mul_nonneg ht0 (sub_nonneg.2 ht1))]

/-- The pointwise bound after raising to the power `(n-1)/2`. -/
lemma Ppolar_rpow_le (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ^ (((n : ℝ) - 1) / 2)
      ≤ Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  set y : ℝ := (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) with hy
  have h1 : Ppolar a x t ≤ Real.exp y := by
    refine le_trans (Ppolar_le_lin a x ht0 ht1) ?_
    have := Real.add_one_le_exp y
    linarith
  have h2 : Ppolar a x t ^ (((n : ℝ) - 1) / 2) ≤ Real.exp y ^ (((n : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow (Ppolar_nonneg hx a t) h1 he
  refine h2.trans_eq ?_
  rw [← Real.exp_mul]
  congr 1
  simp only [M] at hα
  rw [hy, hα]
  ring

/-- **`(1Q) ⟹ (lt)`.** -/
theorem polar_exp (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  have hc1 : Continuous fun t : ℝ => Ppolar a x t ^ (((n : ℝ) - 1) / 2) :=
    (continuous_rpow_const he).comp (continuous_Ppolar a x)
  have hc2 : Continuous fun t : ℝ =>
      Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by fun_prop
  refine hpolar.trans (intervalIntegral.integral_mono_on (by norm_num)
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _) ?_)
  intro u hu
  exact Ppolar_rpow_le hn hx hα hu.1 hu.2

end Sendov
