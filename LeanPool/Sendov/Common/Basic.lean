/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Defs

/-!
# Basic properties of the quantities in the finite-range claim

Elementary facts about `Sendov.M`, `Sendov.A`, `Sendov.c` and `Sendov.Q`, used by every
degree-specific argument.  The two facts that matter are:

* `Sendov.Q_nonneg`: the feasibility constraint `c ^ 2 ≤ A` says exactly that `Q` is a sum
  of squares, hence nonnegative.  This is what makes the real power `Q ^ ((n-4)/2)`
  appearing in `Sendov.R` behave, and in particular avoids the junk values of `Real.rpow`
  at negative bases.
* `Sendov.Q_one`: `Q n α 1 = α / (3 + α)`, the value `B` prescribed by the simplified polar
  inequality of the blog post.  Since `Q n α 1 = 1 - 2 * c n α + A n α`, this pins down
  `A - 2 * c = B - 1 < 0`, which is what gives `Sendov.Q_le_one`.
-/

public section

namespace Sendov

variable {n : ℕ} {α t : ℝ}

lemma M_pos (hn : 2 ≤ n) : 0 < M n := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [M]
  linarith

lemma three_add_pos (hα : 0 ≤ α) : (0 : ℝ) < 3 + α := by linarith

/-- `Q` written as a sum of squares.  Compare `β(t) = (1 - a x t) ^ 2 + a² t² (1 - x²)`
in the blog post. -/
lemma Q_eq (n : ℕ) (α t : ℝ) :
    Q n α t = (1 - c n α * t) ^ 2 + (A n α - c n α ^ 2) * t ^ 2 := by
  simp only [Q]
  ring

/-- Feasibility forces `a² ≥ 0`. -/
lemma A_nonneg (hfeas : c n α ^ 2 ≤ A n α) : 0 ≤ A n α :=
  le_trans (sq_nonneg _) hfeas

/-- Feasibility bounds `α` by `(n-1)/2`, simply because it forces `A = 1 - 2α/(n-1) ≥ 0`.

This crude consequence is all that the *numerical* step of any degree needs: on
`0 ≤ α ≤ min 17 ((n-1)/2)` the upper bounds for `R n α` used in this development stay below
`0.856` for every `5 ≤ n ≤ 97`.  The exact shape of the feasible region, which is cut out
by a quartic in `α`, is therefore never required by the polynomial certificates.

This must not be read as saying that `A ≥ 0` replaces feasibility everywhere.  It does not:
the odd-degree bound needs `0 ≤ Q n α t` on `[0,1]`, which is `Sendov.Q_nonneg` and uses the
full constraint `c ^ 2 ≤ A` — it does not follow from `A ≥ 0`.  Accordingly
`Sendov.integral_rpow_le` takes `hfeas` itself, and only the passage from the resulting
rational function to a polynomial positivity statement is weakened to `α ≤ M n / 2`.  For
even degrees the moment identity `Sendov.integral_moment` needs no hypothesis at all. -/
lemma alpha_le_half_M (hn : 2 ≤ n) (hfeas : c n α ^ 2 ≤ A n α) : α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  have hA : 0 ≤ A n α := A_nonneg hfeas
  rw [A] at hA
  have h : 2 * α / M n ≤ 1 := by linarith
  rw [div_le_one hM] at h
  linarith

lemma Q_nonneg (hfeas : c n α ^ 2 ≤ A n α) (t : ℝ) : 0 ≤ Q n α t := by
  rw [Q_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))

/-- `Q n α 1 = B = α / (3 + α)`: the substituted quadratic takes at `t = 1` the value that
the simplified polar inequality `β(1) < α / (3 + α)` prescribes. -/
lemma Q_one (hn : 2 ≤ n) (hα : 0 ≤ α) : Q n α 1 = α / (3 + α) := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [Q, c, A]
  field_simp
  ring

/-- `Q` is convex with `Q 0 = 1` and `Q 1 = B ≤ 1`, hence bounded by `1` on `[0,1]`.

Only `0 ≤ c` is needed, not `0 ≤ A`: writing `Q t - 1 = t (A t - 2c)`, the identity
`Q 1 = B < 1` gives `A ≤ 2c` outright, and then `A t ≤ 2c` holds whether `A` is nonnegative
(as `A t ≤ A`) or negative (as `A t ≤ 0 ≤ 2c`).  That matters for batches of degrees whose
`α`-range reaches past `(n₀-1)/2`, where `A n₀ α` can be negative. -/
lemma Q_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) (hc : 0 ≤ c n α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ 1 := by
  have hB : Q n α 1 ≤ 1 := by
    rw [Q_one hn hα, div_le_one (three_add_pos hα)]
    linarith
  have hAc : A n α - 2 * c n α ≤ 0 := by
    simp only [Q] at hB
    linarith
  have h5 : A n α * t - 2 * c n α ≤ 0 := by
    rcases le_total 0 (A n α) with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [Q]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]

/-- Feasibility gives `α ≤ (n-1)/2`, and hence `c ≥ (1-B)/2 > 0`. -/
lemma c_pos_of_le_half_M (hn : 2 ≤ n) (hα : 0 ≤ α) (hhalf : α ≤ M n / 2) : 0 < c n α := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have h1 : α / M n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hM (by norm_num)]
    linarith
  have h2 : α / (2 * (3 + α)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  simp only [c]
  linarith

/-- The coefficient multiplying the integral in `Sendov.R` is nonnegative, so any upper
bound for the integral yields an upper bound for `R`.  This is how each degree replaces its
integral by an explicit rational function. -/
lemma R_le_of_integral_le (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
      A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoef : 0 ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      (M_pos hn).le) hn2) (by linarith)
  rw [R]
  have := mul_le_mul_of_nonneg_left hJ hcoef
  linarith

end Sendov
