/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Chord

/-!
# The raw inequalities, and the dictionary between them and `Sendov.R`

`Sendov.stat_lt_one` refutes equation `stat` of the blog post.  `stat` is itself deduced there
from two inequalities that come out of the complex-analytic part of the argument:

* the **raw polar inequality** `(1Q)`, `1 ≤ ∫₀¹ P(t)^((n-1)/2) dt` with
  `P(t) = a² + 2atx(1-a²) + t²(1-a²)²`;
* the **raw origin inequality** `(origin-exact)`,
  `2α + ax ≤ (1-x²)/(2(n-1)) + a²n(n-1) ∫₀¹ t β(t)^((n-2)/2) dt`.

Both are statements about two real numbers `a ∈ (0,1)` and `x ∈ [-1,1]` and a degree `n`; no
polynomial, no complex number and no `q_j` survives into them.  That is what makes the next
target — that the two are not simultaneously satisfiable for `n ≥ 5` — a self-contained
real-variable statement.

This file fixes `P` and records the dictionary.  The key entry is that `α` and `a` determine
each other: with `α = (n-1)(1-a²)/2` one has `A n α = a²` *exactly*, so the `A` of
`Sendov.Defs` and the `a²` of the blog post are the same thing, and `β(t)` is
`Sendov.QQ (a*x) (a^2) t` while `Q n α t` is `Sendov.QQ (c n α) (A n α) t`.

## Main statements

* `Sendov.Ppolar_eq`: `P` as a sum of squares, hence nonnegative for `|x| ≤ 1`;
* `Sendov.A_eq_sq`: `A n α = a²`;
* `Sendov.alpha_pos`, `Sendov.alpha_le_half`: the range of `α`.
-/

public section

namespace Sendov

/-- The integrand of the raw polar inequality `(1Q)`. -/
@[expose]
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2

variable {n : ℕ} {a x t α : ℝ}

/-- `P` is a sum of squares once `|x| ≤ 1`; this is the same computation that makes
`Sendov.QQ_nonneg` work. -/
lemma Ppolar_eq (a x t : ℝ) :
    Ppolar a x t = (a + t * (1 - a ^ 2) * x) ^ 2 + t ^ 2 * (1 - a ^ 2) ^ 2 * (1 - x ^ 2) := by
  simp only [Ppolar]; ring

lemma Ppolar_nonneg (hx : x ^ 2 ≤ 1) (a t : ℝ) : 0 ≤ Ppolar a x t := by
  rw [Ppolar_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))

lemma continuous_Ppolar (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by
  simp only [Ppolar]; fun_prop

/-- With `α = (n-1)(1-a²)/2`, the `A` of `Sendov.Defs` is exactly `a²`. -/
lemma A_eq_sq (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [A, hα]
  field_simp
  ring

lemma alpha_pos (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  have : 0 < 1 - a ^ 2 := by nlinarith
  positivity

lemma alpha_le_half (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  nlinarith [sq_nonneg a]

end Sendov
