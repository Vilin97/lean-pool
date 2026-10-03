/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Rpow

/-!
# The odd-degree bound

For odd `n` the exponent `(n-4)/2` is the half-integer `k + 1/2` with `k = (n-5)/2`, and
`Sendov.R` involves a genuine square root.  Writing `Q ^ (k+1/2) = Q ^ k * √Q` and bounding
`√Q` by a tangent line to the square root replaces it by polynomial moments:

  `∫ t in 0..1, t ^ 3 * Q ^ (k+1/2) ≤ ∫ t in 0..1, t ^ 3 * (Q ^ k * (Q/(2w) + w/2))`

for any `w > 0` (`Sendov.integral_rpow_le`).  This is the only place where `Real.sqrt`
appears; the statement above is already free of it.

The tangent line `√q ≤ q/(2w) + w/2` touches at `q = w²`, so `w` should be chosen near the
values of `Q` that matter.  Taking `w = 1` recovers `2√u ≤ 1 + u`, which is bound `(O)` of
the informal plan and is sharp enough for every odd `n ≥ 7`.  Degree five needs a smaller
`w`: there the relevant values of `Q` are small, `w = 1` overshoots (it gives an upper bound
exceeding `1`, so it proves nothing), and `w = 1/3` works comfortably.  This is what lets
degree five avoid the chord bound and the substitution `α = 3r²/(1-r²)` proposed in the
plan.

Note that only `0 ≤ Q` is needed, never `Q ≤ 1`: the tangent-line inequality is just
`(√q - w)² ≥ 0`.
-/

public section

namespace Sendov

open MeasureTheory

variable {n : ℕ} {α q w : ℝ}

/-- The tangent line to `√·` at `q = w²`: `√q ≤ q/(2w) + w/2`. -/
lemma sqrt_le_tangent (hq : 0 ≤ q) (hw : 0 < w) : Real.sqrt q ≤ q / (2 * w) + w / 2 := by
  have hrw : q / (2 * w) + w / 2 = (q + w ^ 2) / (2 * w) := by field_simp
  rw [hrw, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt q - w), Real.sq_sqrt hq]

/-- The half-integer power bound `q ^ (k + 1/2) ≤ q ^ k * (q/(2w) + w/2)`. -/
lemma rpow_add_half_le (hq : 0 ≤ q) (k : ℕ) (hw : 0 < w) :
    q ^ ((k : ℝ) + 1 / 2) ≤ q ^ k * (q / (2 * w) + w / 2) := by
  rcases hq.lt_or_eq with h | h
  · have he : q ^ ((k : ℝ) + 1 / 2) = q ^ k * Real.sqrt q := by
      rw [Real.rpow_add h, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [he]
    exact mul_le_mul_of_nonneg_left (sqrt_le_tangent hq hw) (pow_nonneg hq k)
  · rw [← h, Real.zero_rpow (by positivity)]
    refine mul_nonneg (pow_nonneg le_rfl k) ?_
    rw [zero_div]
    linarith

/-- **The odd-degree bound.**  The square root is eliminated in favour of polynomial
moments, at the cost of a free parameter `w > 0`. -/
lemma integral_rpow_le (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by rw [hk]; positivity
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α he).intervalIntegrable _ _)
    ((by simp only [Q]; fun_prop : Continuous fun t : ℝ =>
      t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2))).intervalIntegrable _ _) ?_
  intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.1 3)
  rw [hk]
  exact rpow_add_half_le (Q_nonneg hfeas t) k hw

end Sendov
