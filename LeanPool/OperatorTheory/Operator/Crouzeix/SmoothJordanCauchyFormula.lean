/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanCauchy
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCauchyKernelWinding
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Cauchy's integral formula on smooth convex Jordan domains

The smooth-Jordan Cauchy theorem extends to the Cauchy integral formula by
removing the apparent singularity with `dslope`.  The resulting identity is
first stated using the raw scalar contour mass, then normalized under winding
one.  Oriented and canonical-orientation corollaries expose the forms needed
by polynomial approximation on smooth convex domains.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The divided difference of a `DiffContOnCl` scalar function, filled in by
the derivative at an interior point, is again `DiffContOnCl`. -/
theorem DiffContOnCl.dslope_of_mem_isOpen
    {U : Set ℂ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f U)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DiffContOnCl ℂ (dslope f z) U := by
  constructor
  · exact (Complex.differentiableOn_dslope (hU.mem_nhds hz)).2
      hf.differentiableOn
  · apply (continuousOn_dslope (mem_of_superset
      (hU.mem_nhds hz) subset_closure)).2
    exact ⟨hf.continuousOn, hf.differentiableAt hU hz⟩

/-- Cauchy's formula before winding normalization: the contour integral of
`(sigma - z)⁻¹ f(sigma)` is the raw scalar contour mass times `f z`. -/
theorem contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
        Omega.boundaryParam * f z := by
  have hfrontier (t : ℝ) :
      Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hne (t : ℝ) : Omega.boundaryParam t ≠ z := by
    intro heq
    have hzfrontier : z ∈ frontier Omega.carrier := by
      rw [← heq]
      exact hfrontier t
    have : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact this
  have htrace : Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi) ⊆
      closure Omega.carrier := by
    rintro _ ⟨t, _ht, rfl⟩
    exact frontier_subset_closure (hfrontier t)
  have htrace_ne : ∀ sigma ∈
      Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi), sigma - z ≠ 0 := by
    rintro _ ⟨t, _ht, rfl⟩
    exact sub_ne_zero.mpr (hne t)
  have hinv : ContourIntegrable (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne)
  have hinvf : ContourIntegrable (fun sigma : ℂ => (sigma - z)⁻¹ * f sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne).mul
        (hf.continuousOn.mono htrace)
  have hinvconst : ContourIntegrable
      (fun sigma : ℂ => (sigma - z)⁻¹ * f z) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne).mul
        continuousOn_const
  have hzero := contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
    Omega (hf.dslope_of_mem_isOpen Omega.isOpen_carrier hz)
  have hrewrite : contourIntegral (dslope f z) Omega.boundaryParam =
      contourIntegral
        (fun sigma : ℂ =>
          (sigma - z)⁻¹ * f sigma - (sigma - z)⁻¹ * f z)
        Omega.boundaryParam := by
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _ht
    change deriv Omega.boundaryParam t * dslope f z (Omega.boundaryParam t) =
      deriv Omega.boundaryParam t *
        ((Omega.boundaryParam t - z)⁻¹ * f (Omega.boundaryParam t) -
          (Omega.boundaryParam t - z)⁻¹ * f z)
    rw [dslope_of_ne f (hne t)]
    simp only [slope_def_module, smul_eq_mul]
    ring
  rw [hrewrite, contourIntegral_sub hinvf hinvconst,
    contourIntegral_mul_const (f z) hinv] at hzero
  exact sub_eq_zero.mp hzero

/-- Cauchy's formula on a smooth Jordan carrier at a point where the
normalized scalar winding kernel is one. -/
theorem contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier)
    (hkernel : crouzeixScalarCauchyKernel Omega z = 1) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  rw [contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
    Omega hf hz]
  have hq : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  have hmass : contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam = 2 * (Real.pi : ℂ) * I := by
    calc
      contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
          Omega.boundaryParam =
          (2 * (Real.pi : ℂ) * I) *
            ((2 * (Real.pi : ℂ) * I)⁻¹ *
              contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
                Omega.boundaryParam) := by
            field_simp [Real.pi_ne_zero, I_ne_zero]
      _ = (2 * (Real.pi : ℂ) * I) *
          crouzeixScalarCauchyKernel Omega z := by
            rfl
      _ = 2 * (Real.pi : ℂ) * I := by
            rw [hkernel, mul_one]
  rw [hmass]

/-- Cauchy's formula with the boundary datum placed before the scalar kernel,
matching the exterior-kernel approximation interface. -/
theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier)
    (hkernel : crouzeixScalarCauchyKernel Omega z = 1) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  simpa only [mul_comm] using
    contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
      Omega hf hz hkernel

/-- Consistent supporting-normal orientation supplies the winding-one
hypothesis in Cauchy's formula. -/
theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  apply contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
    Omega hf hz
  exact crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
    Omega c hc hcside z hz

/-- The canonical orientation of every smooth convex Jordan domain satisfies
the winding-one Cauchy integral formula. -/
theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.canonicalOrientation.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  let Psi := Omega.canonicalOrientation
  have hfPsi : DiffContOnCl ℂ f Psi.carrier := by
    simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hf
  have hzPsi : z ∈ Psi.carrier := by
    simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hz
  obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  exact contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
    Psi hfPsi c hc hcside hzPsi

/-- The normalized Cauchy integral formula on the canonical orientation,
with `f z` isolated for direct use by polynomial approximation. -/
theorem cauchyFormula_canonicalOrientation
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.canonicalOrientation.boundaryParam := by
  rw [contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
    Omega hf hz]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
