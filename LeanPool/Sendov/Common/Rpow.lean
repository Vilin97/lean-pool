/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Common.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real powers, shared by both ranges

The exponent `(n-4)/2` in `Sendov.R` is a real exponent, so both halves of the development —
the finite range and the large-degree argument — manipulate `Real.rpow`, and both need the
integrand `t ^ 3 * Q ^ e` to be continuous in order to integrate it.  Those facts have no
connection to either strategy, so they live here rather than in the strategy-specific files.

In particular:

* the finite range uses `Sendov.continuous_integrand` to compare integrals in
  `Sendov.integral_rpow_le`, and the large-degree argument needs the same fact to split
  `∫₀¹` at the vertex of `Q`;
* `Sendov.rpow_add_nat_pos` is used by the Beta integral, and the same splitting of a real
  power into a real and a natural part is what turns `B ^ ((n-4)/2)` into `B ^ k * √B` in
  the large-degree reduction.
-/

public section

namespace Sendov

open MeasureTheory

/-- `∫₀¹ xˢ dx = 1/(s+1)` for `s > -1`. -/
lemma integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- `x ^ (s + m) = x ^ s * x ^ m` for positive `x` and a natural `m`. -/
lemma rpow_add_nat_pos {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

/-- `fun x ↦ x ^ e` is continuous on all of `ℝ` for a nonnegative real exponent `e`.  The
exponent must be nonnegative: at `e < 0` the function blows up at the origin. -/
lemma continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x e (Or.inr he)

/-- The integrand of `Sendov.R` is continuous, hence interval integrable.  Needed wherever an
integral involving `Q ^ e` is split or compared. -/
lemma continuous_integrand (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by
  have hQ : Continuous fun t : ℝ => Q n α t := by
    simp only [Q]; fun_prop
  have h3 : Continuous fun t : ℝ => t ^ 3 := by fun_prop
  exact h3.mul ((continuous_rpow_const he).comp hQ)

/-- On `[0,1]` a real power is decreasing in the exponent: `x ^ s ≤ x ^ t` for `t ≤ s`.
Used to drop the `√B` from `B ^ (k + 1/2)`. -/
lemma rpow_le_rpow_of_le_one {x s t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hts : t ≤ s) :
    x ^ s ≤ x ^ t :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hts

end Sendov
