/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Constancy of the scalar Cauchy kernel on a convex carrier

For constant boundary data, the scalar Crouzeix companion is the normalized
Cauchy winding kernel.  Its derivative in the carrier is the contour integral
of `(sigma - z)⁻²`, which vanishes because this integrand has the global
primitive `-(sigma - z)⁻¹` along the boundary.  The carrier is open and
preconnected by strict convexity, so the zero-derivative theorem makes the
kernel constant throughout it.

Consequently, the stagewise winding hypothesis in the scalar-companion route
need only be checked at one point of each carrier.

## Main declarations

* `crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier` --
  the constant-data companion has zero derivative in the carrier;
* `crouzeixScalarCauchyKernel_eq_of_mem_carrier` -- the scalar kernel has the
  same value at every two carrier points;
* `crouzeixScalarCauchyKernel_eq_one_of_basepoint` -- one normalized
  basepoint propagates winding normalization through the carrier.
* `contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier` -- the scalar
  Cauchy contour vanishes at every exterior point;
* `crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier` -- the
  corresponding exterior winding normalization.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex Set
open scoped Interval Real

/-- The constant-data scalar companion has zero derivative at every carrier
point.  Its inverse-square derivative kernel has the explicit primitive
`-(sigma - z)⁻¹` as a function of the contour variable. -/
theorem crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
    (Omega : SmoothJordanDomain) {z : ℂ} (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionDeriv Omega (Polynomial.C 1) z = 0 := by
  have hne : ∀ t : ℝ, Omega.boundaryParam t - z ≠ 0 := by
    intro t hzero
    have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
    have hfrontier : z ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hfrontier⟩
    exact hempty
  have hzero : contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹ ^ 2)
      Omega.boundaryParam = 0 := by
    apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
      (Fp := fun sigma : ℂ => -(sigma - z)⁻¹)
    · intro _ _
      exact
        (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
    · intro t _
      have hsub : HasDerivAt (fun sigma : ℂ => sigma - z) 1
          (Omega.boundaryParam t) := (hasDerivAt_id _).sub_const z
      have hinv := hsub.inv (hne t)
      convert hinv.neg using 1
      · rfl
      · rw [inv_pow]
        ring
    · apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · apply ContinuousOn.pow
        apply ContinuousOn.inv₀
        · exact (continuous_id.sub continuous_const).continuousOn
        · rintro _ ⟨t, _, rfl⟩
          exact hne t
    · simpa only [zero_add] using Omega.boundaryParam_periodic 0
  unfold contourIntegral at hzero
  unfold crouzeixPolynomialScalarCompanionDeriv
  simp only [Polynomial.eval_C, star_one, mul_one, smul_eq_mul] at hzero ⊢
  rw [hzero, mul_zero]

/-- The normalized scalar Cauchy kernel is constant on the open strictly
convex carrier. -/
theorem crouzeixScalarCauchyKernel_eq_of_mem_carrier
    (Omega : SmoothJordanDomain) {z w : ℂ}
    (hz : z ∈ Omega.carrier) (hw : w ∈ Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z =
      crouzeixScalarCauchyKernel Omega w := by
  let f : ℂ → ℂ :=
    crouzeixPolynomialScalarCompanion Omega (Polynomial.C 1)
  have hf : DifferentiableOn ℂ f Omega.carrier := by
    exact (analyticOn_crouzeixPolynomialScalarCompanion
      Omega (Polynomial.C 1)).differentiableOn
  have hfzero : EqOn (deriv f) 0 Omega.carrier := by
    intro x hx
    rw [Pi.zero_apply]
    have hderiv := (hasDerivAt_crouzeixPolynomialScalarCompanion
      Omega (Polynomial.C 1) hx).deriv
    dsimp only [f] at hderiv ⊢
    rw [hderiv,
      crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
        Omega hx]
  have heq := Omega.isOpen_carrier.is_const_of_deriv_eq_zero
    Omega.strictConvex_carrier.convex.isPreconnected hf hfzero hz hw
  simpa only [f, crouzeixPolynomialScalarCompanion,
    crouzeixScalarCauchyKernel, Polynomial.eval_C, star_one, one_mul] using heq

/-- Winding normalization at one point of the carrier propagates to every
carrier point. -/
theorem crouzeixScalarCauchyKernel_eq_one_of_basepoint
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hkc : crouzeixScalarCauchyKernel Omega c = 1) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by
  intro z hz
  exact (crouzeixScalarCauchyKernel_eq_of_mem_carrier
    Omega hz hc).trans hkc

/-- The scalar Cauchy contour vanishes at every point outside the closed
convex carrier.  Strict Hahn--Banach separation puts the entire boundary in
one branch of the complex logarithm, which supplies a global primitive for
the inverse kernel along the contour. -/
theorem contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam = 0 := by
  have hconvex : Convex ℝ (closure Omega.carrier) :=
    Omega.strictConvex_carrier.convex.closure
  obtain ⟨f, u, hf, hfz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hconvex isClosed_closure hz
  have hfrontier (t : ℝ) :
      Omega.boundaryParam t ∈ closure Omega.carrier :=
    frontier_subset_closure (by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t)
  have hne (t : ℝ) : Omega.boundaryParam t ≠ z := by
    intro heq
    apply hz
    rw [← heq]
    exact hfrontier t
  have hslit (t : ℝ) :
      f (z - Omega.boundaryParam t) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [map_sub, Complex.sub_re]
    have ht := hf (Omega.boundaryParam t) (hfrontier t)
    exact sub_pos.mpr (ht.trans hfz)
  have hfa (w : ℂ) : f w = w * f 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (map_smul f w (1 : ℂ))
  have ha : f 1 ≠ 0 := by
    intro ha
    have hzero (w : ℂ) : f w = 0 := by
      rw [hfa, ha, mul_zero]
    have ht := hf (Omega.boundaryParam 0) (hfrontier 0)
    rw [hzero] at ht hfz
    simp only [map_zero] at ht hfz
    linarith
  have hslit' (t : ℝ) :
      (z - Omega.boundaryParam t) * f 1 ∈ Complex.slitPlane := by
    rw [← hfa]
    exact hslit t
  let Fp : ℂ → ℂ := fun w => Complex.log ((z - w) * f 1)
  have hF : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt Fp ((Omega.boundaryParam t - z)⁻¹)
        (Omega.boundaryParam t) := by
    intro t _ht
    have hsub : HasDerivAt (fun w : ℂ => z - w) (-1)
        (Omega.boundaryParam t) :=
      (hasDerivAt_id' (Omega.boundaryParam t)).const_sub z
    have hinner : HasDerivAt (fun w : ℂ => (z - w) * f 1) (-f 1)
        (Omega.boundaryParam t) := by
      simpa only [neg_mul, one_mul] using hsub.mul_const (f 1)
    have hlog' : HasDerivAt Fp
        ((-f 1) / ((z - Omega.boundaryParam t) * f 1))
        (Omega.boundaryParam t) := by
      simpa only [Fp] using hinner.clog (hslit' t)
    have hderiv :
        (-f 1) / ((z - Omega.boundaryParam t) * f 1) =
          (Omega.boundaryParam t - z)⁻¹ := by
      field_simp [ha, sub_ne_zero.mpr (hne t).symm,
        sub_ne_zero.mpr (hne t)]
      ring
    rw [hderiv] at hlog'
    exact hlog'
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := Fp)
  · intro t _
    exact
      (Omega.boundaryParam_contDiff.differentiable
        (by norm_num)).differentiableAt
  · exact hF
  · apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · apply ContinuousOn.inv₀
      · exact (continuous_id.sub continuous_const).continuousOn
      · rintro _ ⟨t, _ht, rfl⟩
        exact sub_ne_zero.mpr (hne t)
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0

/-- The normalized scalar Cauchy kernel is zero throughout the exterior of
the closed convex carrier. -/
theorem crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z = 0 := by
  unfold crouzeixScalarCauchyKernel
  rw [contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
    Omega hz, mul_zero]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
