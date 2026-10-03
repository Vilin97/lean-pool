/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Chord

/-!
# The tail bound

The large-degree argument replaces the integral in `Sendov.R` by an elementary expression:

  `∫₀¹ t³ Q^r dt ≤ 6 / (c⁴ (r+1)(r+2)(r+3)(r+4)) + Bʳ / 4`.

This is the only part of the large-degree argument that touches integration; everything after
it is elementary inequalities in `α` and `n`.

The work is done by `Sendov.integral_le_tail_cube` in `Sendov.Common.Chord`, which proves the
same split for the general quadratic `QQ c A` and an arbitrary weight `t^k` — the `α ≤ 17`
argument needs the `k = 1` instance of it.  All that is left here is to read that bound
through `Q n α t = QQ (c n α) (A n α) t` and `Q n α 1 = α/(3+α)`.

## Main statements

* `Sendov.c_le_one`: `c ≤ 1`, so the chord's zero `1/c` is at least `1`;
* `Sendov.integral_le_tail`: the bound above.
-/

public section

namespace Sendov

open MeasureTheory

variable {n : ℕ} {α t : ℝ}

/-- `c ≤ 1`, so the chord's zero `1/c` is at least `1`. -/
lemma c_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) : c n α ≤ 1 := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : 0 ≤ α / M n := by positivity
  have h2 : 0 ≤ α / (2 * (3 + α)) := by positivity
  linarith

/-- **The tail bound**, read off from `Sendov.integral_le_tail_cube`. -/
theorem integral_le_tail (hn : 2 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hc : 0 < c n α) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4)))
        + (α / (3 + α)) ^ r / 4 := by
  have h := integral_le_tail_cube hfeas hc (c_le_one hn hα) hr
  rw [← Q_one hn hα]
  simpa only [Q_eq_QQ] using h

/-! ### The elementary upper bound `U`

Everything after this point in the large-degree argument is an inequality in `α` and `n`
alone; no integral survives. -/

/-- The elementary bound replacing `Sendov.R`: `(11)` of the informal write-up, but with the
sharper Beta constant `6/((r+1)(r+2)(r+3)(r+4))` in place of `6/r⁴`. -/
@[expose]
noncomputable def U (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
    + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      * (6 / (c n α ^ 4 *
            ((((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
              * (((n : ℝ) - 4) / 2 + 4)))
        + (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) / 4)

/-- On the large-degree range `c` is bounded below, hence positive.  For `n ≥ 101` and
`α ≤ 17` this gives `c ≥ 81/200`, which is `(3)` of the write-up. -/
lemma c_ge_of_large (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : 81 / 200 ≤ c n α := by
  have hM : (100 : ℝ) ≤ M n := by
    have : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [M]; linarith
  have hM0 : (0 : ℝ) < M n := by linarith
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : α / M n ≤ 17 / 100 := by
    rw [div_le_iff₀ hM0]
    nlinarith
  have h2 : α / (2 * (3 + α)) ≤ 17 / 40 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α))]
    nlinarith
  linarith

/-- **`R` is bounded by the elementary expression `U`.**  This is the bridge out of
integration: from here the large-degree argument is elementary. -/
theorem R_le_U (hn : 5 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α) (hc : 0 < c n α) :
    R n α ≤ U n α := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < ((n : ℝ) - 4) / 2 := by linarith
  exact R_le_of_integral_le (by omega) hα (integral_le_tail (by omega) hα hfeas hc hr)

end Sendov
