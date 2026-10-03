/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Moments
public import LeanPool.Sendov.FiniteRange.OddBound

/-!
# The finite-range claim in degree five

The lowest degree, where the exponent `(n-4)/2` is `0 + 1/2`, so `Sendov.R 5 α` involves
`√Q` itself.

The informal plan treats this degree separately, on the ground that bound `(O)` — the
tangent line at `q = 1` — is too wasteful here, and proposes instead the chord bound
`Q(t) ≤ 1 - (1-B)t`, the resulting formula for `∫ t³ √(1-(1-B)t) dt` in half-integer powers
of `B`, and the substitution `α = 3r²/(1-r²)` needed to make that rational.

None of this is necessary.  The waste in `(O)` comes entirely from the tangent line being
taken at `q = 1`, whereas the values of `Q` that matter here are small; taking the tangent
at `q = w²` for a smaller rational `w` fixes it.  With `w = 1/3`, `Sendov.integral_rpow_le`
gives `√Q ≤ 3Q/2 + 1/6` and hence

  `∫ t in 0..1, t³ √Q dt ≤ (3/2) (1/4 - 2c/5 + A/6) + 1/24`,

which is already enough.  So degree five uses exactly the same machinery as every other
odd degree, with only the parameter `w` changed, and no square roots survive.

With `M 5 = 4`, `A 5 α = 1 - α/2` and `c 5 α = (12 - α - α²)/(4(3+α))`, the resulting upper
bound for `R 5 α` is `1 - P α / (96 (3+α)²)` with

  `P α = -9α⁴ - 123α³ + 596α² + 30α + 234`,

which is positive up to `α = 3.912`, while feasibility gives `α ≤ 2` outright (this is the
one degree where `Sendov.alpha_le_half_M` is exactly the bound `A 5 α ≥ 0`).  For
orientation: over the feasible range `α ≤ 1.678` the exact maximum of `R 5 α` is about
`0.716`, against `0.737` for this upper bound — whereas `w = 1` would give `1.063`, above
`1`, and would prove nothing.
-/

public section

namespace Sendov

open MeasureTheory

variable {α : ℝ}

lemma M_five : M 5 = 4 := by norm_num [M]

lemma A_five (α : ℝ) : A 5 α = 1 - α / 2 := by
  rw [A, M]
  push_cast
  ring

lemma c_five (α : ℝ) : c 5 α = 1 - α / 4 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring

lemma c_five' (hα : 0 ≤ α) : c 5 α = (12 - α - α ^ 2) / (4 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_five]
  field_simp
  ring

/-- The odd-degree bound in degree five, with the tangent line taken at `q = 1/9`. -/
lemma integral_five (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 5 α t ^ ((((5 : ℕ) : ℝ) - 4) / 2))
      ≤ 3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24 := by
  have hk : ((((5 : ℕ) : ℝ) - 4) / 2) = ((0 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 0 hk (by norm_num : (0:ℝ) < 1/3)).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ =>
      t ^ 3 * (Q 5 α t ^ 0 * (Q 5 α t / (2 * (1/3)) + (1/3) / 2)))
      = fun t : ℝ => (3 / 2 * 1 + 1 / 6) * t ^ 3 + (3 / 2 * (-2 * c 5 α)) * t ^ 4
          + (3 / 2 * A 5 α) * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring

/-- The upper bound for `R 5 α` obtained from `Sendov.integral_five`. -/
lemma R_five_le (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    R 5 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24) := by
  have h := R_le_of_integral_le (n := 5) (by norm_num) hα (integral_five hfeas)
  rw [M_five] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))

/-- **The finite-range claim in degree five.** -/
theorem finite_range_five (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) : R 5 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 2 := by
    have h := alpha_le_half_M (n := 5) (by norm_num) hfeas
    rw [M_five] at h
    linarith
  have hR := R_five_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24)
      = 1 - (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) := by
    rw [A_five, c_five' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 2) (sub_nonneg.2 hle), sq_nonneg α, hα]
  have : 0 < (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) :=
    div_pos hP (by positivity)
  linarith

end Sendov
