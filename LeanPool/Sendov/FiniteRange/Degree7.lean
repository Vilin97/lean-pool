/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Moments
public import LeanPool.Sendov.FiniteRange.OddBound

/-!
# The finite-range claim in degree seven

The first odd degree, and the prototype for the general odd-degree argument.  Here the
exponent `(n-4)/2` is `1 + 1/2`, so `Sendov.integral_rpow_le` replaces the square root by
the average of the moments of `Q` and `Q ^ 2`, after which the argument runs exactly as in
degree six.

With `M 7 = 6`, `A 7 α = 1 - α/3` and `c 7 α = (18 - α²)/(6(3+α))`:

* `∫ t in 0..1, t³ (Q + Q²)/2 dt = 1/4 - 3c/5 + (4c² + 3A)/12 - 2cA/7 + A²/16`;
* the resulting upper bound for `R 7 α` is `1 - P α / (2592 (3+α)³)` with
  `P α = -5α⁶ - 222α⁵ - 2619α⁴ + 17388α³ + 19413α² - 5022α + 33291`;
* feasibility enters only through `Sendov.alpha_le_half_M`, which gives `α ≤ 3`.

`P` is positive up to `α = 5.338`, so once again there is ample room.  The exact feasible
range is `α ≤ 2.710`, cut out by `-α⁴ - 12α³ + 108α ≥ 0`, but that is not needed.  Since
the odd-degree bound is an inequality rather than an identity, the loss it incurs is real
but small: the exact maximum of `R 7 α` over the feasible range is about `0.598`, against
`0.664` for this upper bound.
-/

public section

namespace Sendov

open MeasureTheory

variable {α : ℝ}

lemma M_seven : M 7 = 6 := by norm_num [M]

lemma A_seven (α : ℝ) : A 7 α = 1 - α / 3 := by
  rw [A, M]
  push_cast
  ring

lemma c_seven (α : ℝ) : c 7 α = 1 - α / 6 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring

lemma c_seven' (hα : 0 ≤ α) : c 7 α = (18 - α ^ 2) / (6 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_seven]
  field_simp
  ring

/-- The odd-degree bound in degree seven: the exponent is `1 + 1/2`, so the integral is
bounded by the average of the first two moments, which is computed exactly. -/
lemma integral_seven (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 7 α t ^ ((((7 : ℕ) : ℝ) - 4) / 2))
      ≤ 1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
        - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16 := by
  have hk : ((((7 : ℕ) : ℝ) - 4) / 2) = ((1 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 1 hk one_pos).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q 7 α t ^ 1 * (Q 7 α t / (2 * 1) + 1 / 2)))
      = fun t : ℝ => 1 * t ^ 3 + (-3 * c 7 α) * t ^ 4
          + ((4 * c 7 α ^ 2 + 3 * A 7 α) / 2) * t ^ 5 + (-2 * c 7 α * A 7 α) * t ^ 6
          + (A 7 α ^ 2 / 2) * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring

/-- The upper bound for `R 7 α` obtained from `Sendov.integral_seven`. -/
lemma R_seven_le (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    R 7 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16) := by
  have h := R_le_of_integral_le (n := 7) (by norm_num) hα (integral_seven hfeas)
  rw [M_seven] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))

/-- **The finite-range claim in degree seven.** -/
theorem finite_range_seven (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) : R 7 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 7) (by norm_num) hfeas
    rw [M_seven] at h
    linarith
  have hR := R_seven_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16)
      = 1 - (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
          - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := by
    rw [A_seven, c_seven' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      sq_nonneg (19413 * α - 2511)]
  have : 0 < (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith

end Sendov
