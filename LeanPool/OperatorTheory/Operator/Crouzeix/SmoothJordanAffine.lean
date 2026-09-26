/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothApprox
public import Mathlib.Analysis.Convex.ContinuousLinearEquiv

/-!
# Affine transport of smooth Jordan domains

Smooth strictly convex Jordan domains are stable under invertible real-linear
maps and translations.  Besides making the geometric package coordinate-free,
this supplies ellipses as exact model domains: they are affine images of disks,
with their transported boundary parametrizations and derivatives exposed by
simp lemmas.

This file does not assert that ellipses approximate an arbitrary convex body.
Its role is the reusable affine geometry needed by such approximation
arguments.
-/

@[expose] public section

open Complex Metric Set
open scoped ContDiff

namespace SmoothJordanDomain

/-- The derivative of a smooth Jordan parametrization after applying an
invertible real-linear map. -/
theorem deriv_continuousLinearEquiv_comp (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    deriv (e ∘ Omega.boundaryParam) t = e (deriv Omega.boundaryParam t) := by
  have hdiff : DifferentiableAt ℝ Omega.boundaryParam t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  exact (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t hdiff.hasDerivAt).deriv

/-- Transport a smooth Jordan domain by an invertible real-linear map. -/
noncomputable def linearImage (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) : SmoothJordanDomain where
  carrier := e '' Omega.carrier
  isOpen_carrier := e.toHomeomorph.isOpen_image.mpr Omega.isOpen_carrier
  strictConvex_carrier := e.strictConvex_image.mpr Omega.strictConvex_carrier
  boundaryParam := e ∘ Omega.boundaryParam
  boundaryParam_periodic := Omega.boundaryParam_periodic.comp e
  boundaryParam_contDiff :=
    Omega.boundaryParam_contDiff.continuousLinearMap_comp e.toContinuousLinearMap
  boundaryParam_range := by
    rw [Set.range_comp, Omega.boundaryParam_range]
    exact e.toHomeomorph.image_frontier Omega.carrier
  boundaryParam_injOn := by
    intro x hx y hy hxy
    exact Omega.boundaryParam_injOn hx hy (e.injective hxy)
  boundaryParam_regular := by
    intro t hzero
    rw [deriv_continuousLinearEquiv_comp] at hzero
    exact Omega.boundaryParam_regular t (e.injective (by simpa using hzero))

@[simp] theorem linearImage_carrier (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) :
    (Omega.linearImage e).carrier = e '' Omega.carrier := rfl

@[simp] theorem linearImage_boundaryParam (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) :
    (Omega.linearImage e).boundaryParam = e ∘ Omega.boundaryParam := rfl

@[simp] theorem linearImage_boundaryParam_apply (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    (Omega.linearImage e).boundaryParam t = e (Omega.boundaryParam t) := rfl

theorem linearImage_boundaryParam_deriv (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    deriv (Omega.linearImage e).boundaryParam t =
      e (deriv Omega.boundaryParam t) := by
  exact deriv_continuousLinearEquiv_comp Omega e t

/-- The derivative of a parametrization is unchanged by translation. -/
theorem deriv_const_add_boundaryParam (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    deriv (fun u => c + Omega.boundaryParam u) t =
      deriv Omega.boundaryParam t := by
  have hdiff : DifferentiableAt ℝ Omega.boundaryParam t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  exact (hdiff.hasDerivAt.const_add c).deriv

/-- Translate a smooth Jordan domain by a complex vector. -/
noncomputable def translate (Omega : SmoothJordanDomain)
    (c : ℂ) : SmoothJordanDomain where
  carrier := (fun z => c + z) '' Omega.carrier
  isOpen_carrier := (Homeomorph.addLeft c).isOpen_image.mpr Omega.isOpen_carrier
  strictConvex_carrier := Omega.strictConvex_carrier.add_left c
  boundaryParam := fun t => c + Omega.boundaryParam t
  boundaryParam_periodic := by
    simpa only [Function.comp_def] using
      Omega.boundaryParam_periodic.comp (fun z : ℂ => c + z)
  boundaryParam_contDiff := contDiff_const.add Omega.boundaryParam_contDiff
  boundaryParam_range := by
    rw [Set.range_comp' (fun z => c + z), Omega.boundaryParam_range]
    exact (Homeomorph.addLeft c).image_frontier Omega.carrier
  boundaryParam_injOn := by
    intro x hx y hy hxy
    exact Omega.boundaryParam_injOn hx hy (add_left_cancel hxy)
  boundaryParam_regular := by
    intro t
    rw [deriv_const_add_boundaryParam]
    exact Omega.boundaryParam_regular t

@[simp] theorem translate_carrier (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).carrier = (fun z => c + z) '' Omega.carrier := rfl

@[simp] theorem translate_boundaryParam (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).boundaryParam = fun t => c + Omega.boundaryParam t := rfl

@[simp] theorem translate_boundaryParam_apply (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    (Omega.translate c).boundaryParam t = c + Omega.boundaryParam t := rfl

theorem translate_boundaryParam_deriv (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    deriv (Omega.translate c).boundaryParam t =
      deriv Omega.boundaryParam t := by
  exact deriv_const_add_boundaryParam Omega c t

/-- An affine image of a positive-radius disk.  In the real plane this is an
ellipse, represented with its exact smooth regular boundary parametrization. -/
noncomputable def ellipse (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) : SmoothJordanDomain :=
  ((SmoothJordanDomain.ball 0 R hR).linearImage e).translate c

@[simp] theorem ellipse_carrier (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) :
    (ellipse c e R hR).carrier =
      (fun z => c + z) '' (e '' Metric.ball 0 R) := rfl

@[simp] theorem ellipse_boundaryParam (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) :
    (ellipse c e R hR).boundaryParam =
      fun t => c + e (circleMap 0 R t) := rfl

theorem ellipse_boundaryParam_deriv (c : ℂ)
    (e : ℂ ≃L[ℝ] ℂ) (R : ℝ) (hR : 0 < R) (t : ℝ) :
    deriv (ellipse c e R hR).boundaryParam t =
      e (circleMap 0 R t * I) := by
  unfold ellipse
  rw [translate_boundaryParam_deriv, linearImage_boundaryParam_deriv]
  change e (deriv (circleMap 0 R) t) = e (circleMap 0 R t * I)
  rw [deriv_circleMap]

end SmoothJordanDomain

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
