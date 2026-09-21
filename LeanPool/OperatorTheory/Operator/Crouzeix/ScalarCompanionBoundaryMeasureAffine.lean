/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Complex-affine invariance of the boundary double-layer density

A nonconstant complex-affine map `z ↦ a * z + b` carries a smooth strictly
convex Jordan domain to another such domain while preserving its boundary
parameter.  The logarithmic-derivative factors contributed by `a` cancel,
so the scalar boundary double-layer density is pointwise invariant when its
base point is transported by the same map.

Consequently, integrability, total mass, and nonnegativity of the density all
transport exactly.  In particular, an oriented double-layer probability
density on the original frontier gives sharp boundary-phase contractivity for
every polynomial on any translate, rotation, or nonzero scaling of the
domain.

## Main declarations

* `SmoothJordanDomain.complexAffine` -- the transported smooth Jordan domain;
* `SmoothJordanDomain.frontier_complexAffine` -- its frontier is the image of
  the original frontier;
* `crouzeixBoundaryDoubleLayerDensity_complexAffine` -- pointwise density
  invariance;
* `integral_crouzeixBoundaryDoubleLayerDensity_complexAffine` -- exact mass
  transport;
* `crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability`
  -- sharp phase contractivity on the image from the original probability
  density.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasure

open Complex MeasureTheory Set
open scoped Interval Real

/-- The image of a smooth Jordan domain under the nonconstant complex-affine
map `z ↦ a * z + b`, with its boundary parametrization transported by the
same map. -/
noncomputable def SmoothJordanDomain.complexAffine
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0) :
    SmoothJordanDomain := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  refine
    { carrier := (fun z => a * z + b) '' Omega.carrier
      isOpen_carrier := ?_
      strictConvex_carrier := ?_
      boundaryParam := fun t => a * Omega.boundaryParam t + b
      boundaryParam_periodic := ?_
      boundaryParam_contDiff := ?_
      boundaryParam_range := ?_
      boundaryParam_injOn := ?_
      boundaryParam_regular := ?_ }
  · change IsOpen (e '' Omega.carrier)
    exact e.isOpenMap Omega.carrier Omega.isOpen_carrier
  · rintro x' ⟨x, hx, hx'⟩ y' ⟨y, hy, hy'⟩ hxy α β hα hβ hsum
    subst x'
    subst y'
    have hxy0 : x ≠ y := by
      intro h
      apply hxy
      rw [h]
    have hcombo :=
      Omega.strictConvex_carrier hx hy hxy0 hα hβ hsum
    change α • e x + β • e y ∈ interior (e '' Omega.carrier)
    rw [← e.image_interior]
    refine ⟨α • x + β • y, hcombo, ?_⟩
    dsimp only [e, Homeomorph.trans_apply]
    change a * (α • x + β • y) + b =
      α • (a * x + b) + β • (a * y + b)
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul,
      Complex.real_smul]
    have hsumC : (α : ℂ) + (β : ℂ) = 1 := by
      exact_mod_cast hsum
    calc
      a * ((α : ℂ) * x + (β : ℂ) * y) + b =
          a * ((α : ℂ) * x + (β : ℂ) * y) +
            ((α : ℂ) + (β : ℂ)) * b := by rw [hsumC, one_mul]
      _ = (α : ℂ) * (a * x + b) +
          (β : ℂ) * (a * y + b) := by ring
  · intro t
    exact congrArg (fun z => a * z + b)
      (Omega.boundaryParam_periodic t)
  · exact (contDiff_const.mul Omega.boundaryParam_contDiff).add contDiff_const
  · change Set.range (fun t => e (Omega.boundaryParam t)) =
      frontier (e '' Omega.carrier)
    rw [show (fun t => e (Omega.boundaryParam t)) =
        e ∘ Omega.boundaryParam by rfl,
      Set.range_comp, Omega.boundaryParam_range, e.image_frontier]
  · intro x hx y hy hxy
    apply Omega.boundaryParam_injOn hx hy
    apply e.injective
    exact hxy
  · intro t
    have hgamma : HasDerivAt Omega.boundaryParam
        (deriv Omega.boundaryParam t) t :=
      (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hderiv : deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t =
        a * deriv Omega.boundaryParam t := by
      have hmul := (hasDerivAt_const t a).mul hgamma
      have hadd := hmul.add (hasDerivAt_const t b)
      rw [show (fun s : ℝ => a * Omega.boundaryParam s + b) =
          (fun _ : ℝ => a) * Omega.boundaryParam +
            (fun _ : ℝ => b) by
        funext s
        rfl]
      simpa only [zero_mul, zero_add, add_zero] using hadd.deriv
    rw [hderiv]
    exact mul_ne_zero ha (Omega.boundaryParam_regular t)

/-- The frontier of a complex-affine image is exactly the image of the
original frontier. -/
theorem SmoothJordanDomain.frontier_complexAffine
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0) :
    frontier (Omega.complexAffine a b ha).carrier =
      (fun z => a * z + b) '' frontier Omega.carrier := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  change frontier (e '' Omega.carrier) = e '' frontier Omega.carrier
  exact (e.image_frontier Omega.carrier).symm

/-- Simultaneously transporting the domain and base point by a nonconstant
complex-affine map leaves the scalar double-layer density unchanged. -/
theorem crouzeixBoundaryDoubleLayerDensity_complexAffine
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) (t : ℝ) :
    crouzeixBoundaryDoubleLayerDensity (Omega.complexAffine a b ha)
        (a * xi + b) t =
      crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  have hgamma : HasDerivAt Omega.boundaryParam
      (deriv Omega.boundaryParam t) t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
  have hderiv : deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t =
      a * deriv Omega.boundaryParam t := by
    have hmul := (hasDerivAt_const t a).mul hgamma
    have hadd := hmul.add (hasDerivAt_const t b)
    rw [show (fun s : ℝ => a * Omega.boundaryParam s + b) =
        (fun _ : ℝ => a) * Omega.boundaryParam +
          (fun _ : ℝ => b) by
      funext s
      rfl]
    simpa only [zero_mul, zero_add, add_zero] using hadd.deriv
  unfold crouzeixBoundaryDoubleLayerDensity
  change (deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t *
      (a * Omega.boundaryParam t + b - (a * xi + b))⁻¹).im /
        Real.pi = _
  rw [hderiv]
  have hsub : a * Omega.boundaryParam t + b - (a * xi + b) =
      a * (Omega.boundaryParam t - xi) := by ring
  rw [hsub, mul_inv_rev]
  congr 2
  calc
    a * deriv Omega.boundaryParam t *
          ((Omega.boundaryParam t - xi)⁻¹ * a⁻¹) =
        (a * a⁻¹) *
          (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹) := by ring
    _ = deriv Omega.boundaryParam t *
        (Omega.boundaryParam t - xi)⁻¹ := by
      rw [mul_inv_cancel₀ ha, one_mul]

/-- Interval integrability of the transported density is equivalent to that
of the original density. -/
theorem
    intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    IntervalIntegrable
        (crouzeixBoundaryDoubleLayerDensity
          (Omega.complexAffine a b ha) (a * xi + b))
        volume 0 (2 * Real.pi) ↔
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi) := by
  apply iff_of_eq
  congr 1
  funext t
  exact crouzeixBoundaryDoubleLayerDensity_complexAffine
    Omega a b xi ha t

/-- The total interval-integral mass of the double-layer density is invariant
under nonconstant complex-affine transport. -/
theorem integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (Omega.complexAffine a b ha) (a * xi + b) t) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  exact crouzeixBoundaryDoubleLayerDensity_complexAffine
    Omega a b xi ha t

/-- If the original frontier carries a pointwise nonnegative unit-mass
double-layer density, then every polynomial satisfies the sharp boundary
phase estimate on every nonconstant complex-affine image of the domain. -/
theorem
    crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0)
    (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive (Omega.complexAffine a b ha) p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    rw [
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff]
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        Omega xi (hmass xi hxi)
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    rw [integral_crouzeixBoundaryDoubleLayerDensity_complexAffine]
    exact hmass xi hxi
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    intro t ht
    rw [crouzeixBoundaryDoubleLayerDensity_complexAffine]
    exact hpos xi hxi t ht

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
