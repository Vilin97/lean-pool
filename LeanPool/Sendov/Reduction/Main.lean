/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Reduction.Alpha17
public import LeanPool.Sendov.Main

/-!
# The polar and origin inequalities are incompatible

This is the top of the development.  The blog post's argument, after the complex-analytic part
that is not formalized here, produces two inequalities about a degree `n`, a zero `0 < a < 1`
and the real part `x` of the mean of the reciprocal critical-point data:

* the **raw polar inequality** `(1Q)`, `1 ≤ ∫₀¹ P(t)^((n-1)/2) dt`;
* the **raw origin inequality** `(origin-exact)`.

`Sendov.polar_origin_incompatible` says they cannot both hold for `n ≥ 5`.  Neither statement
mentions a polynomial or a complex number, so the theorem is a self-contained assertion about
two real numbers.

## The chain

```
                      polar_exp            beta_le
   (1Q)  ─────────────────────▶  (lt)  ─────────────────▶  β(1) ≤ α/(3+α)
                                   │                            │
                                   │ log_le_alpha_mul           │
                                   ▼                            │
                          log α ≤ α(1-β(1))                     │
                                   │                            │
   (origin-exact) ────────────────────────────────────▶  α ≤ 17 │
          │              alpha_le_seventeen                     │
          │ one_le_of_origin                                    │
          ▼                                                     ▼
        (1le) ───────────────────────────────────────────▶  1 ≤ R n α
                          stat_of_one_le                        │
                                                                │ stat_lt_one
                                                                ▼
                                                              False
```

Both halves of `(beta-bound)` are needed, and each is used exactly once: the rational half
`β(1) ≤ α/(3+α)` by `Sendov.stat_of_one_le`, to substitute for `β(1)` in `(1le)`, and the
logarithmic half by `Sendov.alpha_le_seventeen`, to bound `1/x²`.

## Main statements

* `Sendov.polar_origin_incompatible`: the two raw inequalities have no common solution.
-/

public section

namespace Sendov

open MeasureTheory

/-- **The polar and origin inequalities are incompatible.**  For `n ≥ 5` there is no
`0 < a < 1` and `|x| ≤ 1` satisfying both the raw polar inequality `(1Q)` and the raw origin
inequality `(origin-exact)`. -/
theorem polar_origin_incompatible {n : ℕ} (hn : 5 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    False := by
  have hn2 : 2 ≤ n := by omega
  have hα0 : 0 < α := alpha_pos hn2 ha1 ha.le hα
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ QQ (a * x) (a ^ 2) 1 := QQ_nonneg hfeas 1
  -- `(1Q) ⟹ (lt) ⟹ (beta-bound)`, both halves
  have hlt := polar_exp hn2 hx hα hpolar
  have hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α) := beta_le hα0 hB0 hlt
  have hB1lt : QQ (a * x) (a ^ 2) 1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1) :=
    log_le_alpha_mul hα0 hB1lt.le hlt
  -- `α ≤ 17`
  have h17 : α ≤ 17 := alpha_le_seventeen hn ha ha1 hx hα hbeta hlogb horigin
  -- `(origin-exact) ⟹ (1le) ⟹ stat`
  have h1le := one_le_of_origin hn ha ha1 hx hα hα0 hB1lt horigin
  have hstat : 1 ≤ R n α := stat_of_one_le hn hx hα hα0 hbeta h1le
  -- but `stat` is false
  exact absurd hstat
    (not_le.2 (stat_lt_one hn hα0.le h17 (feasible_of_beta hn2 hx hα hα0 hbeta)))

end Sendov
