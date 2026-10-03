/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Cover
public import LeanPool.Sendov.LargeDegree.Endgame

/-!
# The numerical claim, for every degree

This is the top of the development.  `Sendov.Defs` fixes the notation of equation `stat`
of the blog post; everything else establishes that its right-hand side `R n α` is below `1`.
Two arguments meet here.

* `Sendov.finite_range_le_100` certifies `5 ≤ n ≤ 100` by explicit polynomial arithmetic:
  the integral is a finite sum of moments, the moments come from a packed recurrence, and
  each of 31 batches of degrees carries one Bernstein certificate in `α`.
* `Sendov.large_degree` covers `n ≥ 101` analytically: the integral is bounded by a Beta
  integral plus a geometric tail, the resulting elementary bound `U` is shown decreasing in
  the degree, and its value at `n = 101` is below `1` by one more Bernstein certificate.

The two ranges overlap in intent but not in method, and the seam is at `100/101` rather than
at the `97/98` of the blog post: the finite side was pushed three degrees further so that the
analytic side would start with margin `0.122` instead of `0.048`.

## Main statements

* `Sendov.stat_lt_one`: `R n α < 1` for every `n ≥ 5`, `0 ≤ α ≤ 17` with `c ^ 2 ≤ A`;
* `Sendov.stat_contradiction`: equation `stat` of the blog post is therefore unsatisfiable.
-/

public section

namespace Sendov

variable {α : ℝ}

/-- **The numerical claim.**  The right-hand side of equation `stat` of the blog post is
strictly less than `1` for every degree `n ≥ 5` and every `0 ≤ α ≤ 17` satisfying the
feasibility constraint `c ^ 2 ≤ A`. -/
theorem stat_lt_one {n : ℕ} (hn : 5 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  rcases Nat.lt_or_ge n 101 with h | h
  · exact finite_range_le_100 hn (by omega) hα hα' hfeas
  · exact large_degree h hα hα' hfeas

/-- **Equation `stat` is unsatisfiable.**  This is the form in which the blog post uses the
claim: the polynomial argument there produces `1 ≤ R n α` under exactly these hypotheses, so
the assumed counterexample to Sendov's conjecture cannot exist. -/
theorem stat_contradiction {n : ℕ} (hn : 5 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) : False :=
  absurd hstat (not_le.2 (stat_lt_one hn hα hα' hfeas))

end Sendov
