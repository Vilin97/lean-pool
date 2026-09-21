/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Parameterized contour integrals (L4.2a)

Contour integrals along a parameterized closed curve `γ : ℝ → ℂ`, defined as the interval
integral `∫ t in 0..2π, deriv γ t • f (γ t)`.  This is exactly the shape of Mathlib's
`circleIntegral` (the special case `γ = circleMap c R`), so the circle results of
`CircleCauchy.lean` transfer by `rfl`, while general smooth boundaries of convex domains — the
contours of the Crouzeix–Palencia argument — become available.

## Main declarations

* `ContourIntegrable f γ` — integrability of `t ↦ deriv γ t • f (γ t)` on `[0, 2π]`.
* `contourIntegral f γ` — the contour integral `∫ t in 0..2π, deriv γ t • f (γ t)`.
* `contourIntegral_circleMap`, `contourIntegrable_circleMap_iff` — agreement with Mathlib's
  `circleIntegral` / `CircleIntegrable` for `γ = circleMap c R`.
* `ContourIntegrable.of_continuousOn` — continuity of the curve derivative and of `f` on the
  trace gives integrability.
* `contourIntegral_add`, `contourIntegral_sub`, `contourIntegral_neg`, `contourIntegral_smul` —
  linearity in the integrand.
* `ContinuousLinearMap.contourIntegral_comp_comm`, `contourIntegral_const_mul`,
  `contourIntegral_mul_const` — continuous linear maps and constant algebra factors commute
  with the integral.
* `norm_contourIntegral_le_of_norm_le_const` — the length-type bound `‖∫‖ ≤ 2π C`.
* `contourIntegral_eq_sub_of_hasDerivAt`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed` —
  the fundamental theorem of calculus along `γ`: an integrand with a global primitive
  integrates to the boundary difference, hence to `0` along a closed curve (Cauchy's theorem
  for integrands with a primitive).
-/

open scoped Real Interval
open MeasureTheory Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `f` is integrable along the parameterized curve `γ` over `[0, 2π]`: the integrand
`t ↦ deriv γ t • f (γ t)` is interval integrable. -/
def ContourIntegrable (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume 0 (2 * π)

/-- The contour integral `∫ t in 0..2π, γ'(t) • f (γ t)` of `f` along the parameterized curve
`γ`. -/
noncomputable def contourIntegral (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  ∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)

/-- Along the circle parameterization `circleMap c R` the contour integral is Mathlib's
`circleIntegral`. -/
theorem contourIntegral_circleMap (f : ℂ → F) (c : ℂ) (R : ℝ) :
    contourIntegral f (circleMap c R) = circleIntegral f c R := rfl

/-- Along the circle parameterization `circleMap c R` contour integrability is Mathlib's
`CircleIntegrable`. -/
theorem contourIntegrable_circleMap_iff {f : ℂ → F} {c : ℂ} (R : ℝ) :
    ContourIntegrable f (circleMap c R) ↔ CircleIntegrable f c R :=
  (circleIntegrable_iff R).symm

/-- A function continuous on the trace of a curve with continuous derivative is contour
integrable. -/
theorem ContourIntegrable.of_continuousOn {f : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 (2 * π))) (hγ' : ContinuousOn (deriv γ) (Icc 0 (2 * π)))
    (hf : ContinuousOn f (γ '' Icc 0 (2 * π))) : ContourIntegrable f γ := by
  unfold ContourIntegrable
  rw [← uIcc_of_le Real.two_pi_pos.le] at hγ hγ' hf
  exact (hγ'.smul (hf.comp hγ (mapsTo_image _ _))).intervalIntegrable

theorem contourIntegral_add {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z + g z) γ = contourIntegral f γ + contourIntegral g γ := by
  unfold contourIntegral
  simp only [smul_add]
  exact intervalIntegral.integral_add hf hg

theorem contourIntegral_neg (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => -f z) γ = -contourIntegral f γ := by
  unfold contourIntegral
  simp only [smul_neg]
  exact intervalIntegral.integral_neg

theorem contourIntegral_sub {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z - g z) γ = contourIntegral f γ - contourIntegral g γ := by
  unfold contourIntegral
  simp only [smul_sub]
  exact intervalIntegral.integral_sub hf hg

theorem contourIntegral_smul (a : ℂ) (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => a • f z) γ = a • contourIntegral f γ := by
  unfold contourIntegral
  have h : (fun t => deriv γ t • a • f (γ t)) = fun t => a • deriv γ t • f (γ t) :=
    funext fun t => smul_comm _ _ _
  rw [h]
  exact intervalIntegral.integral_smul a _

section Linearity

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Continuous complex-linear maps commute with contour integrals. -/
theorem ContinuousLinearMap.contourIntegral_comp_comm [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℂ] G)
    {f : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => L (f z)) γ = L (contourIntegral f γ) := by
  unfold contourIntegral
  simpa only [Function.comp_apply, map_smul] using L.intervalIntegral_comp_comm hf

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- A constant left factor moves through a contour integral in a complex Banach algebra. -/
theorem contourIntegral_const_mul {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => b * f z) γ = b * contourIntegral f γ := by
  let L : B →L[ℂ] B := ContinuousLinearMap.mul ℂ B b
  simpa only [L, ContinuousLinearMap.mul_apply'] using L.contourIntegral_comp_comm hf

/-- A constant right factor moves through a contour integral in a complex Banach algebra. -/
theorem contourIntegral_mul_const {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => f z * b) γ = contourIntegral f γ * b := by
  let L : B →L[ℂ] B := (ContinuousLinearMap.mul ℂ B).flip b
  simpa only [L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    L.contourIntegral_comp_comm hf

end Linearity

/-- The length-type bound: if the integrand `γ'(t) • f (γ t)` is bounded by `C` on
`[0, 2π]`, the contour integral is bounded by `2π C`. -/
theorem norm_contourIntegral_le_of_norm_le_const {f : ℂ → F} {γ : ℝ → ℂ} {C : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) (2 * π), ‖deriv γ t • f (γ t)‖ ≤ C) :
    ‖contourIntegral f γ‖ ≤ 2 * π * C := by
  unfold contourIntegral
  calc
    ‖∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)‖ ≤ C * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le Real.two_pi_pos.le] at ht
      exact h t (Ioc_subset_Icc_self ht)
    _ = 2 * π * C := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
      ring

/-- Fundamental theorem of calculus along a curve: if `Fp` is a primitive of `f` along the
trace of the differentiable curve `γ`, the contour integral is the boundary difference. -/
theorem contourIntegral_eq_sub_of_hasDerivAt [CompleteSpace F] {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) :
    contourIntegral f γ = Fp (γ (2 * π)) - Fp (γ 0) := by
  unfold ContourIntegrable at hint
  unfold contourIntegral
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Fp (γ t)) (fun t ht => ?_) hint
  rw [uIcc_of_le Real.two_pi_pos.le] at ht
  exact (hF t ht).scomp t (hγ t ht).hasDerivAt

/-- Cauchy's theorem for integrands with a global primitive: along a closed differentiable
curve the contour integral of `f = Fp'` vanishes. -/
theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 := by
  classical
  by_cases hcomplete : CompleteSpace F
  · let _ : CompleteSpace F := hcomplete
    rw [contourIntegral_eq_sub_of_hasDerivAt hγ hF hint, hclosed, sub_self]
  · unfold contourIntegral intervalIntegral
    rw [integral_of_not_completeSpace hcomplete, integral_of_not_completeSpace hcomplete,
      sub_self]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
