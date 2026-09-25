/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.InnerProductSpace.Positive
public import LeanPool.OperatorTheory.Operator.NumericalRange.Helpers

/-!
# Double-layer positivity of the resolvent kernel (L4.2d)

The symmetrized Crouzeix--Palencia bound `‖p(A) + G⋆‖ ≤ 2 m` rests on one positivity fact:
along a positively oriented boundary curve `γ` of a convex domain containing `W(A)`, the
operator kernel of `p(A) + G⋆` is `(2π)⁻¹ p(γ t) • (ν R_A(γ t) + (ν R_A(γ t))⋆)` with
`ν = -i γ'(t)` an outward normal, and the symmetric part `ν R_A(σ) + (ν R_A(σ))⋆` is a
*positive* operator.  This file proves that positivity pointwise, in its natural generality:
the only input is that `W(A)` lies in the closed half-plane cut out at `σ` by the direction `ν`.

Route: for `y = R_A(σ) x` one has `x = σ • y - A y`, hence
`⟪x, ν • R_A(σ) x⟫ = ν · conj (σ‖y‖² - ⟪y, A y⟫)`, whose real part is
`‖y‖² · re (conj ν · (σ - a))` with `a = ⟪y, A y⟫ / ‖y‖² ∈ W(A)`.

## Main declarations

* `re_inner_smul_resolvent_nonneg` -- the pointwise positivity at a supporting point.
* `re_inner_add_adjoint_smul_resolvent_nonneg` -- positivity of the
  self-adjoint double-layer kernel.
* `isPositive_add_adjoint_smul_resolvent` -- the corresponding operator-order
  positivity statement.
* `re_inner_smul_resolvent_circleMap_nonneg` -- its instance on a circle enclosing `W(A)`,
  with `ν = -I * deriv (circleMap c R) t`, the kernel direction produced by `contourIntegral`.
* `re_inner_add_adjoint_smul_resolvent_circleMap_nonneg` -- positivity of the
  symmetric circle kernel.
* `isPositive_add_adjoint_smul_resolvent_circleMap` -- the circle kernel in
  positive-operator form.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem re_inner_adjoint_apply_eq [CompleteSpace E] (B : E →L[ℂ] E) (x : E) :
    (⟪x, (ContinuousLinearMap.adjoint B) x⟫_ℂ).re = (⟪x, B x⟫_ℂ).re := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    (⟪B x, x⟫_ℂ).re = ((starRingEnd ℂ) ⟪B x, x⟫_ℂ).re := (Complex.conj_re _).symm
    _ = (⟪x, B x⟫_ℂ).re := by rw [inner_conj_symm]

/-- `x = σ • y - A y` for `y = R_A(σ) x` and `σ` in the resolvent set. -/
theorem eq_smul_resolvent_apply_sub_apply (A : E →L[ℂ] E) {σ : ℂ}
    (hσ : σ ∈ resolventSet ℂ A) (x : E) :
    x = σ • resolvent A σ x - A (resolvent A σ x) := by
  have hmul : (σ • (1 : E →L[ℂ] E) - A) * resolvent A σ = 1 := by
    have hunit : σ • (1 : E →L[ℂ] E) - A = (hσ.unit : E →L[ℂ] E) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hσ.unit_spec.symm
    calc
      (σ • (1 : E →L[ℂ] E) - A) * resolvent A σ =
          (hσ.unit : E →L[ℂ] E) * (↑((hσ.unit)⁻¹) : E →L[ℂ] E) := by
            rw [hunit, spectrum.resolvent_eq hσ]
      _ = 1 := Units.mul_inv _
  have h := congrArg (fun T : E →L[ℂ] E => T x) hmul
  simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using h.symm

/-- **Double-layer positivity at a supporting point.**  If the numerical range of `A` lies in
the closed half-plane `{w | re (conj ν * (w - σ)) ≤ 0}` -- for instance `σ` a boundary point
of a convex domain containing `W(A)` and `ν` an outward normal there -- then the quadratic
form of `ν • R_A(σ)` has nonnegative real part.  No resolvent-set hypothesis is needed: off
the resolvent set Mathlib's `resolvent` is `0` and the form vanishes. -/
theorem re_inner_smul_resolvent_nonneg (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, (ν • resolvent A σ) x⟫_ℂ).re := by
  by_cases hσ : σ ∈ resolventSet ℂ A
  · rw [smul_apply, inner_smul_right]
    set y := resolvent A σ x with hy
    have hx : x = σ • y - A y := eq_smul_resolvent_apply_sub_apply A hσ x
    by_cases hy0 : y = 0
    · rw [hy0, inner_zero_right, mul_zero, Complex.zero_re]
    · set a := ⟪y, A y⟫_ℂ / (‖y‖ : ℂ) ^ 2 with ha_def
      have hmem : a ∈ numericalRange A := by
        refine ⟨((‖y‖ : ℂ)⁻¹) • y, norm_inv_norm_smul hy0, ?_⟩
        exact inner_inv_norm_smul_apply A hy0
      have hne : (‖y‖ : ℂ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy0))
      have ha : ⟪y, A y⟫_ℂ = (‖y‖ : ℂ) ^ 2 * a := by
        rw [ha_def, mul_div_cancel₀ _ hne]
      have hyy : ⟪y, y⟫_ℂ = (‖y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K y
      have hinner : ⟪x, y⟫_ℂ = (‖y‖ : ℂ) ^ 2 * (starRingEnd ℂ) (σ - a) := by
        rw [hx, inner_sub_left, inner_smul_left, ← inner_conj_symm (A y) y, hyy, ha, map_sub,
          map_mul, map_pow, Complex.conj_ofReal]
        ring
      have hre : (ν * ⟪x, y⟫_ℂ).re = ‖y‖ ^ 2 * ((starRingEnd ℂ) ν * (σ - a)).re := by
        rw [hinner]
        have h1 : ν * ((‖y‖ : ℂ) ^ 2 * (starRingEnd ℂ) (σ - a)) =
            ((‖y‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) ((starRingEnd ℂ) ν * (σ - a)) := by
          rw [map_mul, Complex.conj_conj, Complex.ofReal_pow]
          ring
        rw [h1, Complex.re_ofReal_mul, Complex.conj_re]
      rw [hre, ← neg_sub a σ, mul_neg, Complex.neg_re]
      exact mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (hW a hmem))
  · have hσ' : σ ∈ spectrum ℂ A := hσ
    rw [spectrum.resolvent_zero_of_mem_spectrum hσ', smul_zero, zero_apply, inner_zero_right,
      Complex.zero_re]

/-- The self-adjoint double-layer kernel
`nu • R_A(sigma) + (nu • R_A(sigma))†` has nonnegative quadratic form at a
supporting point. -/
theorem re_inner_add_adjoint_smul_resolvent_nonneg [CompleteSpace E]
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) x⟫_ℂ).re := by
  let B := ν • resolvent A σ
  have hpos : 0 ≤ (⟪x, B x⟫_ℂ).re := re_inner_smul_resolvent_nonneg A hW x
  change 0 ≤ (⟪x, (B + ContinuousLinearMap.adjoint B) x⟫_ℂ).re
  rw [add_apply, inner_add_right, Complex.add_re, re_inner_adjoint_apply_eq]
  exact add_nonneg hpos hpos

/-- The symmetric double-layer kernel is a positive continuous linear map at
every supporting point. -/
theorem isPositive_add_adjoint_smul_resolvent [CompleteSpace E]
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) :
    ContinuousLinearMap.IsPositive ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact IsSelfAdjoint.add_star_self _
  · intro x
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [inner_re_symm]
    exact re_inner_add_adjoint_smul_resolvent_nonneg A hW x

/-- The circle instance: on the positively oriented circle `circleMap c R` the contour kernel
direction is `ν = -I * deriv (circleMap c R) t = R • exp (t I)`, an outward normal, so the
quadratic form of `ν • R_A(circleMap c R t)` has nonnegative real part whenever `W(A)` lies in
the closed disk. -/
theorem re_inner_smul_resolvent_circleMap_nonneg (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) x⟫_ℂ).re := by
  refine re_inner_smul_resolvent_nonneg A (fun w hw => ?_) x
  have hwc : dist w c ≤ R := Metric.mem_closedBall.mp (hW hw)
  have hR : 0 ≤ R := le_trans dist_nonneg hwc
  have hζ : ‖circleMap 0 R t‖ = R := by rw [norm_circleMap_zero, abs_of_nonneg hR]
  have hν : -I * deriv (circleMap c R) t = circleMap 0 R t := by
    rw [deriv_circleMap]
    linear_combination (-circleMap 0 R t) * I_sq
  have hsub : w - circleMap c R t = (w - c) - circleMap 0 R t := by
    rw [← circleMap_sub_center c R t]
    ring
  have h1 : ((starRingEnd ℂ) (circleMap 0 R t) * (w - c)).re ≤ R * dist w c := by
    calc ((starRingEnd ℂ) (circleMap 0 R t) * (w - c)).re
        ≤ ‖(starRingEnd ℂ) (circleMap 0 R t) * (w - c)‖ := Complex.re_le_norm _
      _ = R * dist w c := by rw [norm_mul, Complex.norm_conj, hζ, dist_eq_norm]
  have h2 : ((starRingEnd ℂ) (circleMap 0 R t) * circleMap 0 R t).re = R ^ 2 := by
    rw [Complex.conj_mul', hζ, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h3 : R * dist w c ≤ R * R := mul_le_mul_of_nonneg_left hwc hR
  rw [hν, hsub, mul_sub, Complex.sub_re]
  linarith [h1, h2, h3]

/-- The symmetric double-layer kernel is positive along every enclosing
circle, with the outward normal induced by the positive circle orientation. -/
theorem re_inner_add_adjoint_smul_resolvent_circleMap_nonneg [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
      ContinuousLinearMap.adjoint
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) x⟫_ℂ).re := by
  let B := (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)
  have hpos : 0 ≤ (⟪x, B x⟫_ℂ).re := re_inner_smul_resolvent_circleMap_nonneg A hW t x
  change 0 ≤ (⟪x, (B + ContinuousLinearMap.adjoint B) x⟫_ℂ).re
  rw [add_apply, inner_add_right, Complex.add_re, re_inner_adjoint_apply_eq]
  exact add_nonneg hpos hpos

/-- The symmetric double-layer kernel along an enclosing circle is a positive
continuous linear map. -/
theorem isPositive_add_adjoint_smul_resolvent_circleMap [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) :
    ContinuousLinearMap.IsPositive
      (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact IsSelfAdjoint.add_star_self _
  · intro x
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [inner_re_symm]
    exact re_inner_add_adjoint_smul_resolvent_circleMap_nonneg A hW t x

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
