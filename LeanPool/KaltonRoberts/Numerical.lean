/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Numerical verification for the Kalton–Roberts bound

This file contains the exact rational-arithmetic verifications described in
Sections 4–5 of the companion paper.

All comparisons are between rational numbers and are therefore decidable.
-/
import LeanPool.KaltonRoberts.Defs

/-!
# Numerical verification for the Kalton-Roberts bound

Exact rational-arithmetic verifications for the parameter choices used in the
final bound.
-/

namespace KaltonRoberts

open Finset BigOperators

/-! ## Parameter identities and range checks (Section 5) -/

/-- `p₀ = 1 − q₀`.
**Reference**: Equation (9) in Section 5 of the companion paper. -/
theorem p₀_eq : p₀ = 1 - q₀ := by simp only [p₀, q₀]; norm_num

/-- `0 ≤ τ₁`.
**Reference**: paragraph after Equation (10) in Section 5 of
the companion paper. -/
theorem τ₁_nonneg : 0 ≤ τ₁ := by
  change (0 : ℚ) ≤ (q₀ ^ 3 - α₁) / (q₀ ^ 3 - q₀ ^ 4)
  simp only [q₀, α₁]; norm_num

/-- `τ₁ ≤ 1`.
**Reference**: paragraph after Equation (10) in Section 5 of
the companion paper. -/
theorem τ₁_le_one : τ₁ ≤ 1 := by
  change (q₀ ^ 3 - α₁) / (q₀ ^ 3 - q₀ ^ 4) ≤ (1 : ℚ)
  simp only [q₀, α₁]; norm_num

/-- `0 ≤ τ₂`.
**Reference**: paragraph after Equation (10) in Section 5 of
the companion paper. -/
theorem τ₂_nonneg : 0 ≤ τ₂ := by
  change (0 : ℚ) ≤ (p₀ ^ 4 - α₂) / (p₀ ^ 4 - p₀ ^ 5)
  simp only [p₀, α₂]; norm_num

/-- `τ₂ ≤ 1`.
**Reference**: paragraph after Equation (10) in Section 5 of
the companion paper. -/
theorem τ₂_le_one : τ₂ ≤ 1 := by
  change (p₀ ^ 4 - α₂) / (p₀ ^ 4 - p₀ ^ 5) ≤ (1 : ℚ)
  simp only [p₀, α₂]; norm_num

/-- The frequency identity for Case 1:
`(1 − τ₁) q₀³ + τ₁ q₀⁴ = α₁`.
**Reference**: Equation (10) and the display after it in Section 5 of
the companion paper. -/
theorem frequency_identity_case1 :
    (1 - τ₁) * q₀ ^ 3 + τ₁ * q₀ ^ 4 = α₁ := by
  change (1 - (q₀ ^ 3 - α₁) / (q₀ ^ 3 - q₀ ^ 4)) * q₀ ^ 3 +
    (q₀ ^ 3 - α₁) / (q₀ ^ 3 - q₀ ^ 4) * q₀ ^ 4 = α₁
  simp only [q₀, α₁]; ring

/-- The frequency identity for Case 2:
`(1 − τ₂) p₀⁴ + τ₂ p₀⁵ = α₂`.
**Reference**: Equation (10) and the display in Case 2 of Section 5 of
the companion paper. -/
theorem frequency_identity_case2 :
    (1 - τ₂) * p₀ ^ 4 + τ₂ * p₀ ^ 5 = α₂ := by
  change (1 - (p₀ ^ 4 - α₂) / (p₀ ^ 4 - p₀ ^ 5)) * p₀ ^ 4 +
    (p₀ ^ 4 - α₂) / (p₀ ^ 4 - p₀ ^ 5) * p₀ ^ 5 = α₂
  simp only [p₀, α₂]; ring

/-- `C₁ < C₂`.
**Reference**: the display after Equation (17) in Section 5 of
the companion paper. -/
theorem C₁_lt_C₂ : C₁ < C₂ := by
  change (23662339508853784054849 : ℚ) / 1192830849380162250000 <
    694198146664396294486127753 / 34994834677886019996000000
  norm_num

/-- `C₂ < 9919/500`.
**Reference**: the display after Equation (17) in Section 5 of
the companion paper. -/
theorem C₂_lt_KR_upper : C₂ < krUpper := by
  change (694198146664396294486127753 : ℚ) / 34994834677886019996000000 < 9919 / 500
  norm_num

/-- The combined chain `C₁ < C₂ < 9919/500`.
**Reference**: the final verification in Section 5 of
the companion paper. -/
theorem C₁_lt_C₂_lt_KR_upper : C₁ < C₂ ∧ C₂ < krUpper :=
  ⟨C₁_lt_C₂, C₂_lt_KR_upper⟩

/-! ## Expander parameter checks (Section 4) -/

/-- The four expander triples `(α, r, θ)` from the table in Section 4 of
the companion paper. -/
def expanderParams : List (ℚ × ℕ × ℚ) :=
  [ (1003 / 10000, 4, 1 / 3),      -- E₁
    (3009 / 10000, 4, 4 / 7),      -- E₂
    (47 / 625,     4, 2 / 7),      -- E₃
    (329 / 1250,   5, 5 / 11) ]    -- E₄

/-- Expander E₁ target frequency check: `α₁/(1/3) = 3009/10000`.
This verifies that the target of E₁ feeds into E₂.
**Reference**: display after Equation (13) in Section 5 of
the companion paper. -/
theorem E₁_target_frequency : α₁ / (1 / 3 : ℚ) = 3009 / 10000 := by
  simp only [α₁]; norm_num

/-- Expander E₃ target frequency check: `α₂/(2/7) = 329/1250`.
This verifies that the target of E₃ feeds into E₄.
**Reference**: display after Equation (16) in Section 5 of
the companion paper. -/
theorem E₃_target_frequency : α₂ / (2 / 7 : ℚ) = 329 / 1250 := by
  simp only [α₂]; norm_num

/-- The small-set tail bound for `δ = 1/100` and E₁: `(739/100)(1/3)^{-3}(1/100)^2 < 1/20`.
**Reference**: Equation (7) in Section 4 of the companion paper,
using `e² < 739/100`. -/
theorem small_set_bound_E₁ :
    (739 / 100 : ℚ) * (1 / 3) ^ (1 - 4 : ℤ) * (1 / 100) ^ (4 - 2 : ℤ) < 1 / 20 := by
  norm_num

/-- Small-set tail bound for E₂.
**Reference**: Equation (7) in Section 4 of the companion paper. -/
theorem small_set_bound_E₂ :
    (739 / 100 : ℚ) * (4 / 7) ^ (1 - 4 : ℤ) * (1 / 100) ^ (4 - 2 : ℤ) < 1 / 20 := by
  norm_num

/-- Small-set tail bound for E₃.
**Reference**: Equation (7) in Section 4 of the companion paper. -/
theorem small_set_bound_E₃ :
    (739 / 100 : ℚ) * (2 / 7) ^ (1 - 4 : ℤ) * (1 / 100) ^ (4 - 2 : ℤ) < 1 / 20 := by
  norm_num

/-- Small-set tail bound for E₄.
**Reference**: Equation (7) in Section 4 of the companion paper. -/
theorem small_set_bound_E₄ :
    (739 / 100 : ℚ) * (5 / 11) ^ (1 - 5 : ℤ) * (1 / 100) ^ (5 - 2 : ℤ) < 1 / 20 := by
  norm_num

/-
`e² < 739/100` (used to replace `e²` by a rational upper bound).
**Reference**: Equation (7) in Section 4 of the companion paper:
"Here we use `e² < 739/100`, an elementary consequence of the exponential series
with a geometric tail bound."
-/
theorem e_sq_lt : Real.exp 2 < 739 / 100 := by
  have := Real.exp_one_lt_d9.le
  norm_num at *
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.add_one_le_exp 1]

/-- `q₀⁴ ≤ 1/16`, which ensures that in Case 2 the pure fourfold intersection
has item frequencies at most `α₂`.
**Reference**: Case 2 of Section 5 of the companion paper:
"Its item frequencies are at most `q⁴ ≤ 1/16 < α₂`". -/
theorem q₀_pow4_le : q₀ ^ 4 ≤ 1 / 16 := by
  simp only [q₀]; norm_num

/-- `1/16 < α₂`.
**Reference**: Case 2 of Section 5 of the companion paper. -/
theorem one_sixteenth_lt_α₂ : (1 : ℚ) / 16 < α₂ := by
  change (1 : ℚ) / 16 < 47 / 625; norm_num

/-! ## Case 1 balancing (Section 5) -/

/-- In Case 1, balancing the two recombination inequalities gives `M ≤ C₁`.

The two inequalities are:
  `M ≤ A₁ − (1/2) D'`  where `A₁ = 10 + (3/2) D₁`   ... (from E₁)
  `M ≤ 15 + (7/3) D'`                                   ... (from E₂)
and `D₁ = 6 q₀ + 4 + τ₁ (2 q₀ + 2)`.
Eliminating `D'` gives `M ≤ (7/3 · A₁ + 1/2 · 15) / (7/3 + 1/2) = C₁`.

**Reference**: Equations (12)–(14) in Section 5 of
the companion paper. -/
theorem case1_balance :
    let D₁ : ℚ := 6 * q₀ + 4 + τ₁ * (2 * q₀ + 2)
    let A₁ : ℚ := 10 + 3 / 2 * D₁
    (7 / 3 * A₁ + 1 / 2 * 15) / (7 / 3 + 1 / 2) = C₁ := by
  simp only [q₀, α₁, τ₁, C₁]; norm_num

/-! ## Case 2 balancing (Section 5) -/

/-- In Case 2, balancing the two recombination inequalities gives `M ≤ C₂`.

The two inequalities are:
  `M ≤ A₂ − (2/5) Y`    where `A₂ = 47/5 + (7/5) X₀`   ... (from E₃)
  `M ≤ 47/3 + (11/6) Y`                                    ... (from E₄)
and `X₀ = 4 p₀ + 6 + τ₂ (p₀ + 1)`.
Eliminating `Y` gives `M ≤ (11/6 · A₂ + 2/5 · 47/3) / (11/6 + 2/5) = C₂`.

**Reference**: Equations (15)–(17) in Section 5 of
the companion paper. -/
theorem case2_balance :
    let X₀ : ℚ := 4 * p₀ + 6 + τ₂ * (p₀ + 1)
    let A₂ : ℚ := 47 / 5 + 7 / 5 * X₀
    (11 / 6 * A₂ + 2 / 5 * (47 / 3)) / (11 / 6 + 2 / 5) = C₂ := by
  simp only [p₀, α₂, τ₂, C₂]; norm_num

/-! ## Convexity check: Φ'' > 3 (Section 4, Equation (8)) -/

/-
The second derivative of `Φ_{r,θ}` satisfies `Φ''(x) > 3` for all
`x ∈ [δ, α]`, for each of the four expander rows with `δ = 1/100`.
Since `Φ''(x) = (r−2)/x + (r−1)/(1−x) − 1/(θ−x)`, this is a rational
inequality. Since `Φ''` is convex (it suffices to check the endpoints
because the function is convex on the interval), we verify at the right
endpoint (minimum point for each row).

**Reference**: Equation (8) in Section 4 of the companion paper.

Φ'' lower bound for E₁: `(α, r, θ) = (1003/10000, 4, 1/3)`.
-/
theorem Phi''_lower_E₁ :
    ∀ x : ℚ, 1 / 100 ≤ x → x ≤ 1003 / 10000 →
      3 < (4 - 2 : ℚ) / x + (4 - 1) / (1 - x) - 1 / (1 / 3 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;>
    nlinarith [mul_self_nonneg (x - 1003 / 10000)]

/-
Φ'' lower bound for E₂: `(α, r, θ) = (3009/10000, 4, 4/7)`.
**Reference**: Equation (8) in Section 4 of the companion paper.
-/
theorem Phi''_lower_E₂ :
    ∀ x : ℚ, 1 / 100 ≤ x → x ≤ 3009 / 10000 →
      3 < (4 - 2 : ℚ) / x + (4 - 1) / (1 - x) - 1 / (4 / 7 - x) := by
  intros x hx₁ hx₂; rw [ div_add_div, div_sub_div, lt_div_iff₀ ] <;> try nlinarith;
  · nlinarith [ mul_nonneg ( sub_nonneg.2 hx₁ ) ( sub_nonneg.2 hx₂ ) ];
  · exact mul_pos ( mul_pos ( by linarith ) ( by linarith ) ) ( by linarith )

/-
Φ'' lower bound for E₃: `(α, r, θ) = (47/625, 4, 2/7)`.
**Reference**: Equation (8) in Section 4 of the companion paper.
-/
theorem Phi''_lower_E₃ :
    ∀ x : ℚ, 1 / 100 ≤ x → x ≤ 47 / 625 →
      3 < (4 - 2 : ℚ) / x + (4 - 1) / (1 - x) - 1 / (2 / 7 - x) := by
  -- Let's simplify the expression and show that it is greater than 3.
  intro x hx1 hx2
  field_simp;
  rw [ add_div', div_sub_div, lt_div_iff₀ ] <;> nlinarith [ mul_self_nonneg ( x - 1 / 100 ) ]

/-
Φ'' lower bound for E₄: `(α, r, θ) = (329/1250, 5, 5/11)`.
**Reference**: Equation (8) in Section 4 of the companion paper.
-/
theorem Phi''_lower_E₄ :
    ∀ x : ℚ, 1 / 100 ≤ x → x ≤ 329 / 1250 →
      3 < (5 - 2 : ℚ) / x + (5 - 1) / (1 - x) - 1 / (5 / 11 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;>
    nlinarith [
      mul_pos (sub_pos.mpr (show x < 1 by linarith))
        (sub_pos.mpr (show x < 5 / 11 by linarith))]
end KaltonRoberts
