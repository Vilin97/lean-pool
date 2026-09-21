/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.Basic

/-! # Means and branch-safe quadratic domains -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The squared arithmetic mean occurring in Carlson's first quadratic transformation. -/
def arithmeticMeanSq (x y : ℂ) : ℂ := ((x + y) / 2) ^ 2

/-- The squared geometric mean occurring in Carlson's first quadratic transformation. -/
def geometricMeanSq (x y : ℂ) : ℂ := x * y

/-- The arithmetic mean is symmetric in its arguments. -/
theorem arithmeticMeanSq_comm (x y : ℂ) : arithmeticMeanSq x y = arithmeticMeanSq y x := by
  simp [arithmeticMeanSq, add_comm]

/-- The squared geometric mean is symmetric in its arguments. -/
theorem geometricMeanSq_comm (x y : ℂ) : geometricMeanSq x y = geometricMeanSq y x := by
  simp [geometricMeanSq, mul_comm]

/-- Branch-safe domain for Carlson's first quadratic transformation 6.9-3. -/
def FirstQuadraticDomain (x y : ℂ) : Prop :=
  pair x y ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

/-- Branch-safe domain for Carlson's second quadratic transformation 6.10-1. -/
def SecondQuadraticDomain (x y : ℂ) : Prop :=
  pair (x ^ 2) (y ^ 2) ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

private lemma re_affine_prod_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hxy : 0 < (x * y).re) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (((1 - s : ℂ) + s * x) * ((1 - s : ℂ) + s * y)).re := by
  have heq : (((1 - s : ℂ) + s * x) * ((1 - s : ℂ) + s * y)).re =
      (1 - s) ^ 2 + s * (1 - s) * (x.re + y.re) + s ^ 2 * (x * y).re := by
    simp [mul_re, sub_re, add_re]
    ring
  rw [heq]
  have hmiddle : 0 ≤ s * (1 - s) * (x.re + y.re) := by positivity
  by_cases hs : s = 1
  · subst s; simpa using hxy
  · have : 0 < (1 - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hs))
    positivity

/-- The branch-safe domain is preserved along the segment from the all-one nodes. -/
theorem FirstQuadraticDomain.affine {x y : ℂ} (hz : FirstQuadraticDomain x y)
    {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    FirstQuadraticDomain (1 - (r : ℂ) + r * x) (1 - (r : ℂ) + r * y) := by
  have hpos {v : ℂ} (hv : 0 < v.re) : 0 < (1 - (r : ℂ) + r * v).re := by
    have H := convex_carlsonRightHalfPlane (by norm_num [carlsonRightHalfPlane] : (1 : ℂ) ∈
      carlsonRightHalfPlane)
      hv (sub_nonneg.mpr hr.2) hr.1 (by ring : 1 - r + r = 1)
    simpa [Complex.real_smul, carlsonRightHalfPlane] using H
  have hm : 0 < ((x + y) / 2).re := by
    have hx := hz.1 0
    have hy := hz.1 1
    change 0 < x.re at hx
    change 0 < y.re at hy
    simp only [div_ofNat_re, add_re]
    positivity
  have hA := re_affine_prod_pos hm hm (by
    have hh := hz.2 0
    change 0 < (((x + y) / 2) ^ 2).re at hh
    simpa only [pow_two] using hh) hr.1 hr.2
  have heq : arithmeticMeanSq ((1 - (r : ℂ) + r * x)) ((1 - (r : ℂ) + r * y)) =
      (1 - (r : ℂ) + r * ((x + y) / 2)) *
        (1 - (r : ℂ) + r * ((x + y) / 2)) := by
    dsimp [arithmeticMeanSq]; ring
  constructor
  · intro i; fin_cases i
    · exact hpos (hz.1 0)
    · exact hpos (hz.1 1)
  · intro i; fin_cases i
    · change 0 < (arithmeticMeanSq _ _).re
      rw [heq]
      exact hA
    · exact re_affine_prod_pos (hz.1 0) (hz.1 1) (hz.2 1) hr.1 hr.2

/-- The component with positive-real-part square roots is star-shaped about `(1,1)`. -/
lemma SecondQuadraticDomain.affine {x y : ℂ} (hz : SecondQuadraticDomain x y)
    (hx : 0 < x.re) (hy : 0 < y.re) {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    SecondQuadraticDomain (1 - (r : ℂ) + r * x) (1 - (r : ℂ) + r * y) := by
  have hfirst : FirstQuadraticDomain x y := by
    refine ⟨?_, hz.2⟩
    intro i; fin_cases i
    · exact hx
    · exact hy
  refine ⟨?_, (hfirst.affine hr).2⟩
  intro i; fin_cases i
  · change 0 < ((1 - (r : ℂ) + r * x) ^ 2).re
    rw [pow_two]
    exact re_affine_prod_pos hx hx (by
      have h : 0 < (x ^ 2).re := hz.1 0
      simpa only [pow_two] using h) hr.1 hr.2
  · change 0 < ((1 - (r : ℂ) + r * y) ^ 2).re
    rw [pow_two]
    exact re_affine_prod_pos hy hy (by
      have h : 0 < (y ^ 2).re := hz.1 1
      simpa only [pow_two] using h) hr.1 hr.2

/-- The two square-root nodes lie in the same component of the square preimage of the
right half-plane. The product condition rules out opposite components. -/
lemma SecondQuadraticDomain.same_sign {x y : ℂ} (hz : SecondQuadraticDomain x y) :
    (0 < x.re ∧ 0 < y.re) ∨ (0 < (-x).re ∧ 0 < (-y).re) := by
  have hx : x.im ^ 2 < x.re ^ 2 := by
    have h := hz.1 0
    change 0 < (x ^ 2).re at h
    simp only [pow_two, mul_re] at h ⊢
    linarith
  have hy : y.im ^ 2 < y.re ^ 2 := by
    have h := hz.1 1
    change 0 < (y ^ 2).re at h
    simp only [pow_two, mul_re] at h ⊢
    linarith
  have hsq : (x.im * y.im) ^ 2 < (x.re * y.re) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact (mul_le_mul_of_nonneg_right hx.le (sq_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hy ((sq_nonneg _).trans_lt hx))
  have hxy := hz.2 1
  change 0 < (x * y).re at hxy
  rw [mul_re] at hxy
  have hp : 0 < x.re * y.re := by
    by_contra h
    have hle := le_of_not_gt h
    nlinarith
  rcases mul_pos_iff.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using neg_pos.mpr h.1, by simpa using neg_pos.mpr h.2⟩

end DirichletTransform.TwoVariable
