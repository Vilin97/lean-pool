/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Convex envelopes of planar support functions

A real support function determines a closed convex set by intersecting its
directional halfspaces; its interior is the corresponding open convex
carrier.  This file develops the elementary global envelope facts needed by
the smooth support-curve construction.  For rounded finite-polytope supports,
the original convex hull lies in that interior with the explicit rounding
margin.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.PolytopeSoftSupportCurvature

open Complex Metric Set
open scoped ComplexConjugate

/-- The real-linear directional functional at angle `theta`. -/
noncomputable def smoothSupportDirectionalLinearMap (theta : ℝ) :
    ℂ →ₗ[ℝ] ℝ :=
  Real.cos theta • Complex.reCLM.toLinearMap +
    Real.sin theta • Complex.imCLM.toLinearMap

@[simp] theorem smoothSupportDirectionalLinearMap_apply
    (theta : ℝ) (z : ℂ) :
    smoothSupportDirectionalLinearMap theta z =
      polytopeDirectionalValue z theta := by
  unfold smoothSupportDirectionalLinearMap polytopeDirectionalValue
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  change Real.cos theta * z.re + Real.sin theta * z.im =
    z.re * Real.cos theta + z.im * Real.sin theta
  ring

/-- Closed convex envelope cut out by all directional support halfspaces. -/
def smoothSupportClosedEnvelope (h : ℝ → ℝ) : Set ℂ :=
  {z | ∀ theta, polytopeDirectionalValue z theta ≤ h theta}

/-- Open carrier associated with a support function. -/
def smoothSupportOpenEnvelope (h : ℝ → ℝ) : Set ℂ :=
  interior (smoothSupportClosedEnvelope h)

/-- The support envelope as an explicit intersection of halfspaces. -/
theorem smoothSupportClosedEnvelope_eq_iInter (h : ℝ → ℝ) :
    smoothSupportClosedEnvelope h =
      ⋂ theta : ℝ, {z : ℂ | polytopeDirectionalValue z theta ≤ h theta} := by
  ext z
  simp only [smoothSupportClosedEnvelope, mem_ofPred_eq, mem_iInter]

/-- Each directional-value function is continuous in the planar point. -/
theorem continuous_polytopeDirectionalValue_left (theta : ℝ) :
    Continuous (fun z : ℂ => polytopeDirectionalValue z theta) := by
  unfold polytopeDirectionalValue
  exact (continuous_re.mul continuous_const).add
    (continuous_im.mul continuous_const)

/-- The closed support envelope is closed. -/
theorem isClosed_smoothSupportClosedEnvelope (h : ℝ → ℝ) :
    IsClosed (smoothSupportClosedEnvelope h) := by
  rw [smoothSupportClosedEnvelope_eq_iInter]
  apply isClosed_iInter
  intro theta
  exact isClosed_le (continuous_polytopeDirectionalValue_left theta)
    continuous_const

/-- The closed support envelope is convex. -/
theorem convex_smoothSupportClosedEnvelope (h : ℝ → ℝ) :
    Convex ℝ (smoothSupportClosedEnvelope h) := by
  rw [smoothSupportClosedEnvelope_eq_iInter]
  apply convex_iInter
  intro theta
  simpa only [smoothSupportDirectionalLinearMap_apply] using
    (convex_halfSpace_le (smoothSupportDirectionalLinearMap theta).isLinear
      (h theta))

/-- The open support envelope is open. -/
theorem isOpen_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    IsOpen (smoothSupportOpenEnvelope h) :=
  isOpen_interior

/-- The open support envelope is convex. -/
theorem convex_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    Convex ℝ (smoothSupportOpenEnvelope h) :=
  (convex_smoothSupportClosedEnvelope h).interior

/-- In Mathlib's open-set formulation, the open support envelope is strictly
convex. -/
theorem strictConvex_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    StrictConvex ℝ (smoothSupportOpenEnvelope h) :=
  (convex_smoothSupportOpenEnvelope h).strictConvex_of_isOpen
    (isOpen_smoothSupportOpenEnvelope h)

/-- A unit directional functional changes by at most the ambient distance. -/
theorem polytopeDirectionalValue_le_add_dist
    (z w : ℂ) (theta : ℝ) :
    polytopeDirectionalValue w theta ≤
      polytopeDirectionalValue z theta + dist w z := by
  let n : ℂ := circleMap 0 1 theta
  have hid (v : ℂ) :
      polytopeDirectionalValue v theta = (conj n * v).re := by
    unfold polytopeDirectionalValue n
    simp only [circleMap_zero_re, circleMap_zero_im, one_mul,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  calc
    polytopeDirectionalValue w theta =
        polytopeDirectionalValue z theta +
          (conj n * (w - z)).re := by
      rw [hid w, hid z]
      simp only [mul_sub, Complex.sub_re]
      ring
    _ ≤ polytopeDirectionalValue z theta +
        ‖conj n * (w - z)‖ := by
      simpa only [add_comm] using
        add_le_add_left (Complex.re_le_norm (conj n * (w - z)))
          (polytopeDirectionalValue z theta)
    _ = polytopeDirectionalValue z theta + dist w z := by
      rw [norm_mul, Complex.norm_conj, show ‖n‖ = 1 by
        unfold n
        rw [norm_circleMap_zero, abs_one], one_mul, dist_eq_norm]

/-- The convex hull lies in the open rounded-support envelope, with `rho` as
an explicit uniform interior margin. -/
theorem convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} {delta rho : ℝ} (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    convexHull ℝ (u : Set ℂ) ⊆
      smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho) := by
  intro z hz
  rw [smoothSupportOpenEnvelope, mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrho))
  intro w hw
  change ∀ theta, polytopeDirectionalValue w theta ≤
    polytopeRoundedSupport u delta rho theta
  intro theta
  have hzsupport :=
    polytopeDirectionalValue_le_softSupport_of_mem_convexHull
      hz hdelta theta
  have hdist : dist w z < rho := by
    simpa only [Metric.mem_ball] using hw
  unfold polytopeRoundedSupport
  exact (polytopeDirectionalValue_le_add_dist z w theta).trans
    (by linarith)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
