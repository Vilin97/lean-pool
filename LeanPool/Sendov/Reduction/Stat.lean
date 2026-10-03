/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Reduction.BetaBound

/-!
# From `(1le)` to `stat`

This is `(1le) + (beta-bound) ⟹ stat`.  The right-hand side of `(1le)`,

  `β(1)/(2α(1-β(1))) + β(1)/(4α) + 1/(2(n-1)) + β(1)/(4α(n-1))`
      `+ a⁴ n(n-1)(n-2) β(1)/(4α) ∫₀¹ t³ β(t)^((n-4)/2) dt`,

is monotone increasing in `β(1)`, so `(beta-bound)` lets `β(1)` be replaced throughout by
`α/(3+α)`.  Under that substitution every term becomes the corresponding term of `Sendov.R`:
`β(1)/(2α(1-β(1)))` becomes `1/6`, `β(1)/(4α)` becomes `1/(4(3+α))`, and `ax`, which is
`1 - β(1)/2 - α/(n-1)`, becomes exactly `Sendov.c n α`.

Monotonicity of the integral term is the only part that is not immediate.  `ax` *decreases* as
`β(1)` grows, and `Sendov.QQ` decreases in its first argument on `[0,1]`, so the integrand
grows — `Sendov.integral_QQ_anti`.  Nonnegativity of `β(t)` is needed only at the actual value
`ax`, where it is `(ax)² ≤ a²`, i.e. `x² ≤ 1`; at the substituted value it comes free from the
pointwise comparison, the same way `Sendov.integral_anti` gets it in the batching argument.

## Main statements

* `Sendov.mul_eq_c`: `ax = 1 - β(1)/2 - α/(n-1)`, and hence `c n α ≤ ax` under `(beta-bound)`;
* `Sendov.stat_of_one_le`: `(1le) + (beta-bound) ⟹ 1 ≤ R n α`.
-/

public section

namespace Sendov

open MeasureTheory

variable {n : ℕ} {a x α : ℝ}

/-- `ax = 1 - β(1)/2 - α/(n-1)`: the blog post's rearrangement of `β(1) = 1 - 2ax + a²`. -/
lemma mul_eq_c (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [QQ, hα]
  field_simp
  ring

/-- Under `(beta-bound)`, `Sendov.c n α ≤ ax`: the substitution only ever lowers `ax`. -/
lemma c_le_mul (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ≤ a * x := by
  rw [mul_eq_c hn hα]
  simp only [c]
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have : α / (2 * (3 + α)) = (α / (3 + α)) / 2 := by field_simp
  rw [this]
  linarith

/-- `(beta-bound)` supplies the feasibility constraint `c² ≤ A` that `Sendov.stat_lt_one`
requires.  It is `c ≤ ax` squared, together with `x² ≤ 1`: the substitution can only lower
`ax`, and `ax` is already at most `a`. -/
lemma feasible_of_beta (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ^ 2 ≤ A n α := by
  have hcpos : 0 < c n α := c_pos_of_le_half_M hn hα0.le (alpha_le_half hn hα)
  have hcle : c n α ≤ a * x := c_le_mul hn hα hα0 hbeta
  rw [A_eq_sq hn hα]
  nlinarith [hcpos, hcle, sq_nonneg a, sq_nonneg x]

/-- **`(1le) + (beta-bound) ⟹ stat`.** -/
theorem stat_of_one_le (hn : 5 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ R n α := by
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hA : A n α = a ^ 2 := A_eq_sq hn2 hα
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1
  -- the standing facts about `β(1)`
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have hkey : B1 * (3 + α) ≤ α := by
    rw [← le_div_iff₀ h3]; exact hbeta
  have hB1lt : B1 < 1 := by nlinarith [hα0, hB0]
  -- the four elementary terms
  have t1 : B1 / (2 * α * (1 - B1)) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hkey, hB0, hα0]
  have t2 : B1 / (4 * α) ≤ 1 / (4 * (3 + α)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hkey]
  have t4 : B1 / (4 * α * M n) ≤ 1 / (4 * M n * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hM]
  -- the integral term
  have hcle : c n α ≤ a * x := c_le_mul hn2 hα hα0 hbeta
  have hr : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hI : (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (c n α) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) :=
    integral_QQ_anti hcle hfeas hr 3
  have hInn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfeas u) _)
  have hpre : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  have t5 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    have hcoef : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hkey, hpre]
    have hstep1 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
      mul_le_mul_of_nonneg_right hcoef hInn
    refine hstep1.trans ?_
    have hcnn : (0 : ℝ) ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA]; positivity
    refine mul_le_mul_of_nonneg_left ?_ hcnn
    simpa only [Q_eq_QQ, hA] using hI
  rw [R]
  linarith

end Sendov
