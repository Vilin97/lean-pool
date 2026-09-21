/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportCurveGlobal

/-!
# Exact frontier range of rounded support curves

This file proves the reverse inclusion missing from the global support-curve
calculus: every frontier point of a bounded rounded support envelope is hit by
the support curve.  The key local fact is that an active support inequality
recovers both normal and tangent coordinates of the contact point.
-/

open Complex Metric Set
open scoped ContDiff

/-- Angular derivative of the directional value of a fixed planar point. -/
theorem deriv_polytopeDirectionalValue_right (z : ℂ) (theta : ℝ) :
    deriv (polytopeDirectionalValue z) theta =
      -z.re * Real.sin theta + z.im * Real.cos theta := by
  unfold polytopeDirectionalValue
  change deriv
    ((fun _ : ℝ => z.re) * Real.cos + (fun _ : ℝ => z.im) * Real.sin)
      theta = _
  rw [deriv_add
    ((differentiableAt_const z.re).mul Real.differentiableAt_cos)
    ((differentiableAt_const z.im).mul Real.differentiableAt_sin),
    deriv_mul (differentiableAt_const z.re) Real.differentiableAt_cos,
    deriv_mul (differentiableAt_const z.im) Real.differentiableAt_sin,
    deriv_const, deriv_const, Real.deriv_cos, Real.deriv_sin]
  ring

/-- If a point of a smooth support envelope activates the inequality in
direction `theta`, then it is the corresponding support-curve point. -/
theorem eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    {z : ℂ} (hz : z ∈ smoothSupportClosedEnvelope h) {theta : ℝ}
    (hactive : polytopeDirectionalValue z theta = h theta) :
    z = smoothSupportCurve h theta := by
  let gap : ℝ → ℝ := fun x => polytopeDirectionalValue z x - h x
  have hmax : IsLocalMax gap theta := by
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [gap]
    have hx := hz x
    linarith
  have hgapDeriv : deriv gap theta =
      (-z.re * Real.sin theta + z.im * Real.cos theta) - deriv h theta := by
    dsimp only [gap]
    change deriv (polytopeDirectionalValue z - h) theta = _
    have hdirDiff : DifferentiableAt ℝ (polytopeDirectionalValue z) theta := by
      unfold polytopeDirectionalValue
      fun_prop
    rw [deriv_sub
      hdirDiff
      (hsmooth.differentiable (by norm_num) theta),
      deriv_polytopeDirectionalValue_right]
  have htangent :
      -z.re * Real.sin theta + z.im * Real.cos theta = deriv h theta := by
    have hzero := hmax.deriv_eq_zero
    rw [hgapDeriv] at hzero
    linarith
  rw [show smoothSupportCurve h theta =
      h theta • smoothSupportUnitNormal theta +
        deriv h theta • smoothSupportUnitTangent theta by rfl]
  unfold polytopeDirectionalValue at hactive
  have hre : z.re =
      h theta * Real.cos theta - deriv h theta * Real.sin theta := by
    calc
      z.re = z.re * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
        rw [Real.sin_sq_add_cos_sq, mul_one]
      _ =
          (z.re * Real.cos theta + z.im * Real.sin theta) *
              Real.cos theta -
            (-z.re * Real.sin theta + z.im * Real.cos theta) *
              Real.sin theta := by
        ring
      _ = h theta * Real.cos theta - deriv h theta * Real.sin theta := by
        rw [hactive, htangent]
  have him : z.im =
      h theta * Real.sin theta + deriv h theta * Real.cos theta := by
    calc
      z.im = z.im * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
        rw [Real.sin_sq_add_cos_sq, mul_one]
      _ =
          (z.re * Real.cos theta + z.im * Real.sin theta) *
              Real.sin theta +
            (-z.re * Real.sin theta + z.im * Real.cos theta) *
              Real.cos theta := by
        ring
      _ = h theta * Real.sin theta + deriv h theta * Real.cos theta := by
        rw [hactive, htangent]
  apply Complex.ext
  · unfold smoothSupportUnitTangent smoothSupportUnitNormal
    simp only [Complex.add_re, Complex.smul_re, Complex.mul_re,
      circleMap_zero_re, circleMap_zero_im, I_re, I_im, one_mul,
      mul_zero, mul_one, zero_sub, smul_eq_mul]
    simpa only [sub_eq_add_neg, mul_neg] using hre
  · unfold smoothSupportUnitTangent smoothSupportUnitNormal
    simp only [Complex.add_im, Complex.smul_im, Complex.mul_im,
      circleMap_zero_re, circleMap_zero_im, I_re, I_im, one_mul,
      mul_zero, mul_one, smul_eq_mul]
    simpa only [add_zero] using him

/-- If every support inequality is strict for a continuous periodic support
function, then the point lies in the open support envelope. -/
theorem mem_smoothSupportOpenEnvelope_of_forall_lt
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : ∀ theta, polytopeDirectionalValue z theta < h theta) :
    z ∈ smoothSupportOpenEnvelope h := by
  let gap : ℝ → ℝ := fun theta =>
    h theta - polytopeDirectionalValue z theta
  have hgapContinuous : Continuous gap := by
    exact hcontinuous.sub (contDiff_polytopeDirectionalValue z).continuous
  have hgapPeriodic : Function.Periodic gap (2 * Real.pi) := by
    intro theta
    dsimp only [gap]
    rw [hperiodic theta, periodic_polytopeDirectionalValue z theta]
  obtain ⟨r, hr, hrbound⟩ :
      ∃ r : ℝ, 0 < r ∧
        ∀ theta ∈ Icc (0 : ℝ) (2 * Real.pi), r ≤ gap theta :=
    isCompact_Icc.exists_forall_le' hgapContinuous.continuousOn
      (fun theta _ => by
        dsimp only [gap]
        exact sub_pos.mpr (hz theta))
  have hgapLower (theta : ℝ) : r ≤ gap theta := by
    obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico Real.pi theta
    let psi : ℝ := theta - (k : ℝ) * (2 * Real.pi)
    have hpsi : psi ∈ Icc (0 : ℝ) (2 * Real.pi) := by
      dsimp only [psi]
      constructor <;> linarith [hk.1, hk.2]
    have hbound := hrbound psi hpsi
    have hgapEq : gap psi = gap theta := by
      exact hgapPeriodic.sub_int_mul_eq k
    rwa [hgapEq] at hbound
  rw [smoothSupportOpenEnvelope, mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hr)))
  intro w hw
  change ∀ theta, polytopeDirectionalValue w theta ≤ h theta
  intro theta
  have hdist : dist w z < r / 2 := by
    simpa only [mem_ball] using hw
  have hdir := polytopeDirectionalValue_le_add_dist z w theta
  have hlower := hgapLower theta
  dsimp only [gap] at hlower
  linarith

/-- Every frontier point of a continuous periodic support envelope activates
at least one of its defining support inequalities. -/
theorem exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : z ∈ frontier (smoothSupportOpenEnvelope h)) :
    ∃ theta, polytopeDirectionalValue z theta = h theta := by
  rw [(isOpen_smoothSupportOpenEnvelope h).frontier_eq] at hz
  have hclosureSubset :
      closure (smoothSupportOpenEnvelope h) ⊆
        smoothSupportClosedEnvelope h := by
    apply closure_minimal
    · exact interior_subset
    · exact isClosed_smoothSupportClosedEnvelope h
  have hzclosed := hclosureSubset hz.1
  by_contra hnone
  have hzstrict (theta : ℝ) :
      polytopeDirectionalValue z theta < h theta := by
    exact lt_of_le_of_ne (hzclosed theta) (fun heq =>
      hnone ⟨theta, heq⟩)
  exact hz.2
    (mem_smoothSupportOpenEnvelope_of_forall_lt
      hcontinuous hperiodic hzstrict)

/-- For a smooth periodic support function, every frontier point of its open
support envelope is hit by the support curve. -/
theorem frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    frontier (smoothSupportOpenEnvelope h) ⊆ range (smoothSupportCurve h) := by
  intro z hz
  obtain ⟨theta, hactive⟩ :=
    exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
      hsmooth.continuous hperiodic hz
  have hclosureSubset :
      closure (smoothSupportOpenEnvelope h) ⊆
        smoothSupportClosedEnvelope h := by
    apply closure_minimal
    · exact interior_subset
    · exact isClosed_smoothSupportClosedEnvelope h
  have hzclosed : z ∈ smoothSupportClosedEnvelope h := by
    exact hclosureSubset (frontier_subset_closure hz)
  refine ⟨theta, ?_⟩
  exact (eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
    hsmooth hzclosed hactive).symm

/-- The rounded positive-curvature support curve has exactly the frontier of
its open support envelope as its range. -/
theorem range_polytopeRoundedSupportCurve_eq_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) =
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  apply Subset.antisymm
  · exact range_polytopeRoundedSupportCurve_subset_frontier
      hu hdelta hrho
  · exact frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
      (contDiff_polytopeRoundedSupport hu delta rho)
      (periodic_polytopeRoundedSupport u delta rho)

/-- A positive-periodic function has the same range on any half-open
fundamental interval as it does on the whole real line. -/
theorem image_Ico_eq_range_of_periodic
    {α : Type*} {f : ℝ → α} {p : ℝ}
    (hp : Function.Periodic f p) (hp_pos : 0 < p) (a : ℝ) :
    f '' Ico a (a + p) = range f := by
  apply Subset.antisymm (image_subset_range f _)
  rintro z ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico hp_pos x a
  exact ⟨y, hy, hxy.symm⟩

/-- The rounded support curve parametrizes its whole frontier already on the
standard half-open interval `[0, 2 * pi)`. -/
theorem image_Ico_polytopeRoundedSupportCurve_eq_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    polytopeRoundedSupportCurve u delta rho '' Ico 0 (2 * Real.pi) =
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  calc
    polytopeRoundedSupportCurve u delta rho '' Ico 0 (2 * Real.pi) =
        range (polytopeRoundedSupportCurve u delta rho) := by
      simpa only [zero_add] using
        image_Ico_eq_range_of_periodic
          (periodic_polytopeRoundedSupportCurve u delta rho)
          (by positivity) 0
    _ = frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) :=
      range_polytopeRoundedSupportCurve_eq_frontier hu hdelta hrho

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
