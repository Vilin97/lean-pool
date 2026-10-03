/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Polynomial moments

The integrals `∫ t in 0..1, t ^ 3 * Q ^ k` appearing in `Sendov.R` are, for natural `k`,
integrals of polynomials, hence exactly computable.  This file computes them once and for
all.

Expanding `Q = 1 + bt + dt²` by the binomial theorem twice gives

  `(1 + bt + dt²) ^ k = ∑ i < k+1, ∑ l < i+1, C(k,i) C(i,l) bˡ d^(i-l) t^(2i-l)`

(`Sendov.quad_pow`), and integrating `t ^ 3` times this term by term gives

  `∫ t in 0..1, t ^ 3 * Q ^ k = ∑ i < k+1, ∑ l < i+1, C(k,i) C(i,l) bˡ d^(i-l) / (2i-l+4)`

(`Sendov.integral_moment`), with `b = -2c` and `d = A`.  This is formula `(M)` of the
informal plan.  Every degree of the finite range reduces to this finite sum: even degrees
use it directly with `k = (n-4)/2`, and odd degrees use it for `k` and `k+1` after
`Sendov.integral_rpow_le` has removed the square root.

Note that no hypothesis on `c`, `A` or `α` is needed here — the identity is a polynomial
one.  Feasibility is required only for the odd-degree reduction, never for the moments.
-/

public section

namespace Sendov

open MeasureTheory Finset

/-- Every monomial is interval integrable on `[0,1]`. -/
lemma intervalIntegrable_const_mul_pow (a : ℝ) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ m) volume 0 1 :=
  (by fun_prop : Continuous fun t : ℝ => a * t ^ m).intervalIntegrable _ _

/-- The binomial expansion of a power of a quadratic. -/
lemma quad_pow (b d t : ℝ) (k : ℕ) :
    (1 + b * t + d * t ^ 2) ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
  rw [show (1 + b * t + d * t ^ 2) = (b * t + d * t ^ 2) + 1 by ring, add_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, add_pow, sum_mul]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : l + 2 * (i - l) = 2 * i - l := by omega
  rw [mul_pow, mul_pow, ← pow_mul]
  calc b ^ l * t ^ l * (d ^ (i - l) * t ^ (2 * (i - l))) * (i.choose l : ℝ) * (k.choose i : ℝ)
      = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * (t ^ l * t ^ (2 * (i - l))) := by
        ring
    _ = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
        rw [← pow_add, hexp]

/-- The expansion of the integrand of `Sendov.R` as an explicit polynomial. -/
lemma t3_mul_Q_pow (n : ℕ) (α t : ℝ) (k : ℕ) :
    t ^ 3 * Q n α t ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) := by
  have hQ : Q n α t = 1 + (-2 * c n α) * t + A n α * t ^ 2 := by simp only [Q]; ring
  rw [hQ, quad_pow, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : 3 + (2 * i - l) = 2 * i - l + 3 := by omega
  calc t ^ 3 * (((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
        * t ^ (2 * i - l))
      = ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
          * (t ^ 3 * t ^ (2 * i - l)) := by ring
    _ = _ := by rw [← pow_add, hexp]

/-- The `k`-th moment `∫ t in 0..1, t ^ 3 * Q ^ k`, as an explicit finite double sum.  This
is `(M)` of the informal plan. -/
noncomputable def mom (n : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
    ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
      / ((2 * i - l + 4 : ℕ) : ℝ)

/-- **The moment formula.**  The integrals appearing in `Sendov.R` are exactly the finite
double sum `Sendov.mom`, for every natural `k`, with no hypotheses at all. -/
theorem integral_moment (n : ℕ) (α : ℝ) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = mom n α k := by
  rw [mom]
  have hfun : (fun t : ℝ => t ^ 3 * Q n α t ^ k)
      = fun t : ℝ => ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) :=
    funext fun t => t3_mul_Q_pow n α t k
  rw [hfun, intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      rw [one_pow]
      norm_num
      ring
    · exact fun l _ => intervalIntegrable_const_mul_pow _ _
  · intro i _
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_finsetSum _ fun l _ => by fun_prop

/-- The moments of a polynomial supported in degrees three to seven, kept as a convenience
for the low degrees. -/
lemma integral_poly7 (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    (∫ t in (0 : ℝ)..1, (a₀ * t ^ 3 + a₁ * t ^ 4 + a₂ * t ^ 5 + a₃ * t ^ 6 + a₄ * t ^ 7))
      = a₀ / 4 + a₁ / 5 + a₂ / 6 + a₃ / 7 + a₄ / 8 := by
  have h₀ := intervalIntegrable_const_mul_pow a₀ 3
  have h₁ := intervalIntegrable_const_mul_pow a₁ 4
  have h₂ := intervalIntegrable_const_mul_pow a₂ 5
  have h₃ := intervalIntegrable_const_mul_pow a₃ 6
  have h₄ := intervalIntegrable_const_mul_pow a₄ 7
  rw [intervalIntegral.integral_add (((h₀.add h₁).add h₂).add h₃) h₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring

end Sendov
