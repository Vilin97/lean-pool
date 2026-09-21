/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Smooth planar curves from support functions

For a smooth periodic real support function `h`, let `n(theta)` be the unit
normal and `tau(theta) = n(theta) * I` the positively oriented unit tangent.
The classical support curve is

`gamma(theta) = h(theta) n(theta) + h'(theta) tau(theta)`.

Its derivative is exactly `(h + h'') tau`.  Thus strict positivity of the
curvature radius `h + h''` gives a smooth periodic regular curve, with explicit
speed and outward-normal formulas.  These local identities are independent of
the later global argument identifying the curve with the frontier of its
support envelope.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.PolytopeSoftSupportCurvature

open Complex Set
open scoped ContDiff

/-- Unit outward normal at angle `theta`. -/
noncomputable def smoothSupportUnitNormal (theta : ℝ) : ℂ :=
  circleMap 0 1 theta

/-- Positively oriented unit tangent at angle `theta`. -/
noncomputable def smoothSupportUnitTangent (theta : ℝ) : ℂ :=
  smoothSupportUnitNormal theta * I

/-- The planar curve represented by a differentiable support function. -/
noncomputable def smoothSupportCurve (h : ℝ → ℝ) (theta : ℝ) : ℂ :=
  h theta • smoothSupportUnitNormal theta +
    deriv h theta • smoothSupportUnitTangent theta

/-- The radius of curvature associated with a twice differentiable support
function. -/
noncomputable def smoothSupportCurvatureRadius
    (h : ℝ → ℝ) (theta : ℝ) : ℝ :=
  h theta + deriv (deriv h) theta

/-- Differentiation preserves an additive period. -/
theorem periodic_deriv_of_periodic {f : ℝ → ℝ} {p : ℝ}
    (hf : Function.Periodic f p) :
    Function.Periodic (deriv f) p := by
  intro x
  calc
    deriv f (x + p) = deriv (fun y => f (y + p)) x := by
      rw [deriv_comp_add_const]
    _ = deriv f x := by rw [hf.funext]

/-- The unit normal is `2*pi`-periodic. -/
theorem periodic_smoothSupportUnitNormal :
    Function.Periodic smoothSupportUnitNormal (2 * Real.pi) := by
  exact periodic_circleMap 0 1

/-- The unit tangent is `2*pi`-periodic. -/
theorem periodic_smoothSupportUnitTangent :
    Function.Periodic smoothSupportUnitTangent (2 * Real.pi) := by
  exact periodic_smoothSupportUnitNormal.comp (fun z : ℂ => z * I)

/-- A smooth periodic support function produces a periodic support curve. -/
theorem periodic_smoothSupportCurve {h : ℝ → ℝ}
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    Function.Periodic (smoothSupportCurve h) (2 * Real.pi) := by
  intro theta
  unfold smoothSupportCurve
  rw [hperiodic theta,
    (periodic_deriv_of_periodic hperiodic) theta,
    periodic_smoothSupportUnitNormal theta,
    periodic_smoothSupportUnitTangent theta]

/-- The unit normal is infinitely differentiable. -/
theorem contDiff_smoothSupportUnitNormal :
    ContDiff ℝ ∞ smoothSupportUnitNormal := by
  exact contDiff_circleMap 0 1

/-- The unit tangent is infinitely differentiable. -/
theorem contDiff_smoothSupportUnitTangent :
    ContDiff ℝ ∞ smoothSupportUnitTangent := by
  exact contDiff_smoothSupportUnitNormal.mul contDiff_const

/-- A smooth support function produces an infinitely differentiable support
curve. -/
theorem contDiff_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (smoothSupportCurve h) := by
  have hderiv : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  exact (hsmooth.smul contDiff_smoothSupportUnitNormal).add
    (hderiv.smul contDiff_smoothSupportUnitTangent)

/-- Exact derivative of the unit normal. -/
theorem deriv_smoothSupportUnitNormal (theta : ℝ) :
    deriv smoothSupportUnitNormal theta =
      smoothSupportUnitTangent theta := by
  unfold smoothSupportUnitNormal smoothSupportUnitTangent
  exact deriv_circleMap 0 1 theta

/-- Exact derivative of the unit tangent. -/
theorem deriv_smoothSupportUnitTangent (theta : ℝ) :
    deriv smoothSupportUnitTangent theta =
      -smoothSupportUnitNormal theta := by
  unfold smoothSupportUnitTangent
  rw [deriv_mul_const
    (contDiff_smoothSupportUnitNormal.differentiable (by norm_num) theta) I,
    deriv_smoothSupportUnitNormal]
  unfold smoothSupportUnitTangent
  simp only [mul_assoc, I_mul_I, mul_neg, mul_one]

/-- Derivative witness for the unit tangent. -/
theorem hasDerivAt_smoothSupportUnitTangent (theta : ℝ) :
    HasDerivAt smoothSupportUnitTangent
      (-smoothSupportUnitNormal theta) theta := by
  have hdiff :=
    (contDiff_smoothSupportUnitTangent.differentiable (by norm_num) theta).hasDerivAt
  rwa [deriv_smoothSupportUnitTangent] at hdiff

/-- Exact velocity formula for a smooth support curve. -/
theorem deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitTangent theta := by
  have hderivSmooth : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  have hh := hsmooth.differentiable (by norm_num) theta
  have hdh := hderivSmooth.differentiable (by norm_num) theta
  have hn := contDiff_smoothSupportUnitNormal.differentiable (by norm_num) theta
  have ht := contDiff_smoothSupportUnitTangent.differentiable (by norm_num) theta
  change deriv
      (h • smoothSupportUnitNormal + deriv h • smoothSupportUnitTangent) theta = _
  rw [deriv_add (hh.smul hn) (hdh.smul ht),
    deriv_smul hh hn, deriv_smul hdh ht,
    deriv_smoothSupportUnitNormal, deriv_smoothSupportUnitTangent]
  unfold smoothSupportCurvatureRadius
  module

/-- Positive curvature radius makes the support curve regular. -/
theorem smoothSupportCurve_regular {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ theta, 0 < smoothSupportCurvatureRadius h theta)
    (theta : ℝ) :
    deriv (smoothSupportCurve h) theta ≠ 0 := by
  rw [deriv_smoothSupportCurve hsmooth]
  exact smul_ne_zero (hcurv theta).ne' (by
    unfold smoothSupportUnitTangent smoothSupportUnitNormal
    rw [mul_ne_zero_iff_right I_ne_zero]
    intro hzero
    have hnorm := congrArg norm hzero
    rw [norm_circleMap_zero, abs_one, norm_zero] at hnorm
    exact one_ne_zero hnorm)

/-- The speed of a positive-curvature support curve is its curvature radius. -/
theorem norm_deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ theta, 0 < smoothSupportCurvatureRadius h theta)
    (theta : ℝ) :
    ‖deriv (smoothSupportCurve h) theta‖ =
      smoothSupportCurvatureRadius h theta := by
  rw [deriv_smoothSupportCurve hsmooth, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hcurv theta)]
  unfold smoothSupportUnitTangent smoothSupportUnitNormal
  rw [norm_mul, norm_circleMap_zero, norm_I, abs_one, one_mul]
  exact mul_one _

/-- Rotating the positive tangent velocity clockwise gives the outward normal
scaled by the curvature radius. -/
theorem neg_I_mul_deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    -I * deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitNormal theta := by
  rw [deriv_smoothSupportCurve hsmooth]
  unfold smoothSupportUnitTangent
  change -I * ((smoothSupportCurvatureRadius h theta : ℂ) *
      (smoothSupportUnitNormal theta * I)) =
    (smoothSupportCurvatureRadius h theta : ℂ) *
      smoothSupportUnitNormal theta
  ring_nf
  rw [I_sq]
  ring

/-- The curve point has the prescribed support value in its own normal
direction. -/
theorem polytopeDirectionalValue_smoothSupportCurve_self
    (h : ℝ → ℝ) (theta : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h theta) theta = h theta := by
  unfold polytopeDirectionalValue smoothSupportCurve
    smoothSupportUnitTangent smoothSupportUnitNormal
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one,
    add_zero, circleMap_zero_re, circleMap_zero_im,
    one_mul]
  ring_nf
  calc
    Real.cos theta ^ 2 * h theta + h theta * Real.sin theta ^ 2 =
        h theta * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
    _ = h theta := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The support curve associated with the strictly rounded log-sum-exp
support of a finite polytope. -/
noncomputable def polytopeRoundedSupportCurve
    (u : Finset ℂ) (delta rho : ℝ) : ℝ → ℂ :=
  smoothSupportCurve (polytopeRoundedSupport u delta rho)

/-- The rounded polytope support curve is `2*pi`-periodic. -/
theorem periodic_polytopeRoundedSupportCurve
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupportCurve u delta rho)
      (2 * Real.pi) := by
  exact periodic_smoothSupportCurve
    (periodic_polytopeRoundedSupport u delta rho)

/-- The rounded polytope support curve is infinitely differentiable. -/
theorem contDiff_polytopeRoundedSupportCurve
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) := by
  exact contDiff_smoothSupportCurve
    (contDiff_polytopeRoundedSupport hu delta rho)

/-- Positive smoothing and rounding scales make the rounded polytope support
curve regular. -/
theorem polytopeRoundedSupportCurve_regular
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by
  apply smoothSupportCurve_regular
    (contDiff_polytopeRoundedSupport hu delta rho)
  intro x
  unfold smoothSupportCurvatureRadius
  exact polytopeRoundedSupport_add_deriv_deriv_pos
    hu hdelta hrho x

/-- In every direction, the rounded support curve lies on a supporting line
outside the entire original finite convex hull. -/
theorem polytopeDirectionalValue_le_roundedSupportCurve_self
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 ≤ rho)
    (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeDirectionalValue
        (polytopeRoundedSupportCurve u delta rho theta) theta := by
  unfold polytopeRoundedSupportCurve
  rw [polytopeDirectionalValue_smoothSupportCurve_self]
  unfold polytopeRoundedSupport
  exact (polytopeDirectionalValue_le_softSupport_of_mem_convexHull
    hz hdelta theta).trans (le_add_of_nonneg_right hrho)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
