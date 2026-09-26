/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Shared norm and quadratic estimates

The sibling and row-column certificates use the same norm expansions and tangent bounds.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

/-- A norm is bounded by its quadratic tangent at a positive radius. -/
theorem norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E) {r : ℝ}
    (hr : 0 < r) : ‖x‖ ≤ (‖x‖ ^ 2 + r ^ 2) / (2 * r) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * r)]
  nlinarith [sq_nonneg (‖x‖ - r)]

/-- A nonnegative weighted norm is bounded by its quadratic tangent. -/
theorem weighted_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight r : ℝ) (hr : 0 < r) (hweight : 0 ≤ weight) :
    weight * ‖x‖ ≤ weight / (2 * r) * (‖x‖ ^ 2 + r ^ 2) := by
  calc
    weight * ‖x‖ ≤ weight * ((‖x‖ ^ 2 + r ^ 2) / (2 * r)) :=
      mul_le_mul_of_nonneg_left (norm_tangent x hr) hweight
    _ = _ := by ring

/-- The squared norm of a nonnegative weighted pair in terms of its separation. -/
theorem weighted_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Twice a norm is bounded by a positive radius and its squared-norm quotient. -/
theorem two_mul_norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E)
    {r : ℝ} (hr : 0 < r) : 2 * ‖x‖ ≤ r + ‖x‖ ^ 2 / r := by
  have h := norm_tangent x hr
  calc
    2 * ‖x‖ ≤ 2 * ((‖x‖ ^ 2 + r ^ 2) / (2 * r)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = r + ‖x‖ ^ 2 / r := by field_simp; ring

/-- A convex quadratic on an interval is bounded by its endpoint values. -/
theorem quadratic_le_max_endpoints {a b d l x u : ℝ} (ha : 0 ≤ a)
    (hlx : l ≤ x) (hxu : x ≤ u) :
    a * x ^ 2 + b * x + d ≤ max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := by
  by_cases hlu : l = u
  · subst u
    have hx : x = l := le_antisymm hxu hlx
    subst x
    exact le_max_left _ _
  have hwidth : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxu) hlu)
  have hcurve : a * (x - l) * (x - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha (sub_nonneg.mpr hlx))
      (sub_nonpos.mpr hxu)
  have hleft := le_max_left (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d)
  have hright := le_max_right (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d)
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hxu))
    (mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr hlx))
  apply (mul_le_mul_iff_of_pos_left hwidth).mp
  nlinarith

/-- Expand the squared norm of a difference of three vectors. -/
theorem norm_sub_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x y : E) :
    ‖e - x - y‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ⟪e, x⟫_ℝ - 2 * ⟪e, y⟫_ℝ + 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

/-- The nonnegative part of a real coefficient. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- The magnitude of the negative part of a real coefficient. -/
def negativePart (x : ℝ) : ℝ := max (-x) 0

/-- Positive and negative parts recover the coefficient. -/
theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, hx', neg_nonneg.mpr hx']

/-- The positive part is nonnegative. -/
theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := le_max_right _ _

/-- The negative part is nonnegative. -/
theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := le_max_right _ _

/-- A negative linear radial term is bounded by its quadratic secant. -/
theorem radial_secant {r d l u : ℝ} (hd : 0 ≤ d) (hl : l ≤ r) (hu : r ≤ u)
    (hsum : 0 < l + u) :
    -d * r ≤ -d / (l + u) * r ^ 2 - d * l * u / (l + u) := by
  have hproduct : 0 ≤ (r - l) * (u - r) :=
    mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  have hbase : r ^ 2 + l * u ≤ (l + u) * r := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (div_nonneg hd hsum.le)
  field_simp [hsum.ne'] at hscaled ⊢
  nlinarith

/-- Split a signed quadratic coefficient to bound it at the interval endpoints. -/
theorem balance_mul_sq_le {a r l u : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r) (hru : r ≤ u) :
    a * r ^ 2 ≤ positivePart a * u ^ 2 - negativePart a * l ^ 2 := by
  have hr := hl.trans hlr
  have hu := hr.trans hru
  have hupperSq := (sq_le_sq₀ hr hu).2 hru
  have hlowerSq := (sq_le_sq₀ hl hr).2 hlr
  have hupper := mul_le_mul_of_nonneg_left hupperSq (positivePart_nonneg a)
  have hlower := mul_le_mul_of_nonneg_left hlowerSq (negativePart_nonneg a)
  have hparts := congrArg (fun x : ℝ ↦ x * r ^ 2) (positivePart_sub_negativePart a)
  linarith only [hparts, hupper, hlower]

/-- A positive quadratic coefficient gives a global tangent bound for a weighted norm. -/
theorem weightedNorm_le_quadratic {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight coefficient : ℝ) (hcoefficient : 0 < coefficient) :
    weight * ‖x‖ ≤ coefficient * ‖x‖ ^ 2 + weight ^ 2 / (4 * coefficient) := by
  have hsquare := sq_nonneg (2 * coefficient * ‖x‖ - weight)
  field_simp [hcoefficient.ne']
  nlinarith

end LeanPool.Besicovitch
