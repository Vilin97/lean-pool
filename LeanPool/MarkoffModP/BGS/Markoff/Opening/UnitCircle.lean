/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Normalization

/-!
# The real compactness lemma in the opening

The published opening rules out finite characteristic-zero orbits by first placing all three
normalized trace coordinates in `[-2, 2]`.  The elementary real inequality used at that point is
proved here independently of the later cyclotomic lifting argument.
-/

namespace BGS.Markoff

/-- A real normalized Markoff point whose first trace coordinate lies in `[-2, 2]` is the
origin.  In particular, the published hypothesis that all three coordinates lie in this interval
is more than is needed.

The proof uses `2|bc| ≤ b² + c²`.  Since the Markoff equation makes `abc` equal to the
nonnegative sum of three squares and `|a| ≤ 2`, it follows that `a² ≤ 0`; the remaining two
squares then vanish as well. -/
theorem real_normalizedMarkoff_eq_origin_of_firstCoordinate_mem_Icc
    (x : NormalizedPoint ℝ) (hx : IsNormalizedMarkoff x)
    (hfirst : x.u1 ∈ Set.Icc (-2 : ℝ) 2) :
    x = normalizedOrigin := by
  rcases x with ⟨a, b, c⟩
  change a ^ 2 + b ^ 2 + c ^ 2 - a * b * c = 0 at hx
  have haAbs : |a| ≤ 2 := (abs_le).2 hfirst
  have hsumNonnegative : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hproductEq : a * b * c = a ^ 2 + b ^ 2 + c ^ 2 := by linarith
  have hproductNonnegative : 0 ≤ a * b * c := hproductEq ▸ hsumNonnegative
  have habsProduct : |a * b * c| = a * b * c := abs_of_nonneg hproductNonnegative
  have habsBCNonnegative : 0 ≤ |b| * |c| := mul_nonneg (abs_nonneg b) (abs_nonneg c)
  have hproductBound : |a * b * c| ≤ 2 * |b| * |c| := by
    rw [abs_mul, abs_mul]
    nlinarith
  have hbcBound : 2 * |b| * |c| ≤ b ^ 2 + c ^ 2 := by
    have hsquare := sq_nonneg (|b| - |c|)
    have hbAbsSquare : |b| ^ 2 = b ^ 2 := sq_abs b
    have hcAbsSquare : |c| ^ 2 = c ^ 2 := sq_abs c
    nlinarith
  have haSquareNonpositive : a ^ 2 ≤ 0 := by
    rw [habsProduct] at hproductBound
    nlinarith
  have ha : a = 0 := sq_eq_zero_iff.mp (le_antisymm haSquareNonpositive (sq_nonneg a))
  have hbSquareNonpositive : b ^ 2 ≤ 0 := by
    rw [ha] at hx
    norm_num at hx
    nlinarith [sq_nonneg c]
  have hb : b = 0 := sq_eq_zero_iff.mp (le_antisymm hbSquareNonpositive (sq_nonneg b))
  have hc : c = 0 := by
    rw [ha, hb] at hx
    norm_num at hx
    exact hx
  subst a
  subst b
  subst c
  rfl

/-- Published Proposition 16's real inequality, stated with all three interval hypotheses. -/
theorem real_normalizedMarkoff_eq_origin_of_coordinates_mem_Icc
    (x : NormalizedPoint ℝ) (hx : IsNormalizedMarkoff x)
    (hfirst : x.u1 ∈ Set.Icc (-2 : ℝ) 2)
    (_hsecond : x.u2 ∈ Set.Icc (-2 : ℝ) 2)
    (_hthird : x.u3 ∈ Set.Icc (-2 : ℝ) 2) :
    x = normalizedOrigin :=
  real_normalizedMarkoff_eq_origin_of_firstCoordinate_mem_Icc x hx hfirst

end BGS.Markoff
