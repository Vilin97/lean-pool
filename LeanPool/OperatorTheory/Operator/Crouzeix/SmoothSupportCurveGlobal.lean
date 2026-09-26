/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportCurve
public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportEnvelopeApproximation

/-!
# Global geometry of smooth support curves

For a smooth periodic support function with positive curvature radius, every
fixed directional projection of its support curve increases strictly until
the matching normal angle and decreases strictly afterward.  Periodicity then
turns this local derivative calculation into global support-halfspace control,
uniqueness of the supporting contact, and injectivity on every fundamental
period.
-/

@[expose] public section

open Complex Metric Set
open scoped ContDiff

/-- The projection of the support curve onto a normal at `theta`, written in
normal/tangent coordinates at `phi`. -/
theorem polytopeDirectionalValue_smoothSupportCurve
    (h : ℝ → ℝ) (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta =
      h phi * Real.cos (theta - phi) +
        deriv h phi * Real.sin (theta - phi) := by
  unfold polytopeDirectionalValue smoothSupportCurve
    smoothSupportUnitTangent smoothSupportUnitNormal
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one,
    zero_sub, add_zero, circleMap_zero_re, circleMap_zero_im, one_mul]
  rw [Real.cos_sub, Real.sin_sub]
  ring

/-- The derivative of a fixed directional projection is the curvature radius
times the sine of the angular displacement. -/
theorem deriv_smoothSupportCurve_projection
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    deriv
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) phi =
      smoothSupportCurvatureRadius h phi * Real.sin (theta - phi) := by
  have hh : DifferentiableAt ℝ h phi :=
    hsmooth.differentiable (by norm_num) phi
  have hderivSmooth : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  have hdh : DifferentiableAt ℝ (deriv h) phi :=
    hderivSmooth.differentiable (by norm_num) phi
  have hsub : DifferentiableAt ℝ (fun x : ℝ => theta - x) phi :=
    differentiableAt_const theta |>.sub differentiableAt_id
  have hcos : DifferentiableAt ℝ (fun x : ℝ => Real.cos (theta - x)) phi :=
    hsub.cos
  have hsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (theta - x)) phi :=
    hsub.sin
  have hsub_deriv : deriv (fun x : ℝ => theta - x) phi = -1 := by
    change deriv ((fun _ : ℝ => theta) - id) phi = _
    rw [deriv_sub (differentiableAt_const theta) differentiableAt_id,
      deriv_const, deriv_id]
    ring
  rw [show (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) =
      (fun x => h x * Real.cos (theta - x) +
        deriv h x * Real.sin (theta - x)) by
    funext x
    exact polytopeDirectionalValue_smoothSupportCurve h theta x]
  change deriv
    (h * (fun x => Real.cos (theta - x)) +
      deriv h * (fun x => Real.sin (theta - x))) phi = _
  rw [deriv_add (hh.mul hcos) (hdh.mul hsin),
    deriv_mul hh hcos, deriv_mul hdh hsin,
    deriv_cos hsub, deriv_sin hsub, hsub_deriv]
  unfold smoothSupportCurvatureRadius
  ring

/-- Derivative witness for a fixed directional projection of the support
curve. -/
theorem hasDerivAt_smoothSupportCurve_projection
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    HasDerivAt
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (smoothSupportCurvatureRadius h phi * Real.sin (theta - phi)) phi := by
  have hdiff : DifferentiableAt ℝ
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) phi := by
    rw [show (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) =
        (fun x => h x * Real.cos (theta - x) +
          deriv h x * Real.sin (theta - x)) by
      funext x
      exact polytopeDirectionalValue_smoothSupportCurve h theta x]
    have hh := hsmooth.differentiable (by norm_num) phi
    have hdh := ((contDiff_infty_iff_deriv.mp hsmooth).2.differentiable
      (by norm_num) phi)
    have hsub : DifferentiableAt ℝ (fun x : ℝ => theta - x) phi :=
      differentiableAt_const theta |>.sub differentiableAt_id
    exact (hh.mul hsub.cos).add (hdh.mul hsub.sin)
  have hd := hdiff.hasDerivAt
  rwa [deriv_smoothSupportCurve_projection hsmooth theta phi] at hd

/-- Before its normal angle, a positive-curvature support curve has strictly
increasing projection onto that normal. -/
theorem strictMonoOn_smoothSupportCurve_projection_left
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta : ℝ) :
    StrictMonoOn
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (Icc (theta - Real.pi) theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (theta - Real.pi) theta)
  · exact (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_smoothSupportCurve_projection hsmooth theta x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    simp only [mem_Ioo] at hx
    rw [deriv_smoothSupportCurve_projection hsmooth]
    exact mul_pos (hcurv x)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

/-- After its normal angle, a positive-curvature support curve has strictly
decreasing projection onto that normal. -/
theorem strictAntiOn_smoothSupportCurve_projection_right
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta : ℝ) :
    StrictAntiOn
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (Icc theta (theta + Real.pi)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc theta (theta + Real.pi))
  · exact (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_smoothSupportCurve_projection hsmooth theta x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    simp only [mem_Ioo] at hx
    rw [deriv_smoothSupportCurve_projection hsmooth]
    exact mul_neg_of_pos_of_neg (hcurv x)
      (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

/-- Every real angle has an integer-period translate in the half-open interval
centered at any prescribed angle. -/
theorem exists_sub_int_mul_two_pi_mem_Ico (theta phi : ℝ) :
    ∃ k : ℤ,
      phi - (k : ℝ) * (2 * Real.pi) ∈
        Ico (theta - Real.pi) (theta + Real.pi) := by
  let k : ℤ := ⌊(phi - (theta - Real.pi)) / (2 * Real.pi)⌋
  refine ⟨k, ?_⟩
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hlo := Int.sub_floor_div_mul_nonneg
    (phi - (theta - Real.pi)) hperiod
  have hhi := Int.sub_floor_div_mul_lt
    (phi - (theta - Real.pi)) hperiod
  change theta - Real.pi ≤ phi - (k : ℝ) * (2 * Real.pi) ∧
    phi - (k : ℝ) * (2 * Real.pi) < theta + Real.pi
  dsimp [k] at hlo hhi ⊢
  constructor <;> linarith

/-- A smooth periodic positive-curvature support curve lies in every
halfspace prescribed by its support function. -/
theorem polytopeDirectionalValue_smoothSupportCurve_le
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta ≤ h theta := by
  obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico theta phi
  let psi : ℝ := phi - (k : ℝ) * (2 * Real.pi)
  have hcurvePeriod := periodic_smoothSupportCurve hperiodic
  have hcurveEq : smoothSupportCurve h psi = smoothSupportCurve h phi := by
    exact hcurvePeriod.sub_int_mul_eq k
  rw [← hcurveEq]
  have hthetaSelf := polytopeDirectionalValue_smoothSupportCurve_self h theta
  by_cases hleft : psi ≤ theta
  · have hmono :=
      (strictMonoOn_smoothSupportCurve_projection_left
        hsmooth hcurv theta).monotoneOn
    have hle := hmono
      (show psi ∈ Icc (theta - Real.pi) theta from ⟨hk.1, hleft⟩)
      (show theta ∈ Icc (theta - Real.pi) theta from
        ⟨by linarith [Real.pi_pos], le_rfl⟩) hleft
    change polytopeDirectionalValue (smoothSupportCurve h psi) theta ≤
      polytopeDirectionalValue (smoothSupportCurve h theta) theta at hle
    rwa [hthetaSelf] at hle
  · have hthetaPsi : theta < psi := lt_of_not_ge hleft
    have hanti := strictAntiOn_smoothSupportCurve_projection_right
      hsmooth hcurv theta
    have hlt := hanti
      (show theta ∈ Icc theta (theta + Real.pi) from
        ⟨le_rfl, by linarith [Real.pi_pos]⟩)
      (show psi ∈ Icc theta (theta + Real.pi) from
        ⟨hthetaPsi.le, hk.2.le⟩) hthetaPsi
    change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
      polytopeDirectionalValue (smoothSupportCurve h theta) theta at hlt
    rw [hthetaSelf] at hlt
    exact hlt.le

/-- A directional projection reaches its support value exactly at parameters
congruent to the matching normal angle modulo `2 * pi`. -/
theorem polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta = h theta ↔
      ∃ k : ℤ, phi = theta + (k : ℝ) * (2 * Real.pi) := by
  constructor
  · intro heq
    obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico theta phi
    let psi : ℝ := phi - (k : ℝ) * (2 * Real.pi)
    have hcurvePeriod := periodic_smoothSupportCurve hperiodic
    have hcurveEq : smoothSupportCurve h psi = smoothSupportCurve h phi := by
      exact hcurvePeriod.sub_int_mul_eq k
    have heqPsi :
        polytopeDirectionalValue (smoothSupportCurve h psi) theta = h theta := by
      rw [hcurveEq]
      exact heq
    by_cases hpsi : psi = theta
    · refine ⟨k, ?_⟩
      dsimp [psi] at hpsi
      linarith
    · have hself := polytopeDirectionalValue_smoothSupportCurve_self h theta
      rcases lt_or_gt_of_ne hpsi with hlt | hgt
      · have hstrict := strictMonoOn_smoothSupportCurve_projection_left
          hsmooth hcurv theta
          (show psi ∈ Icc (theta - Real.pi) theta from ⟨hk.1, hlt.le⟩)
          (show theta ∈ Icc (theta - Real.pi) theta from
            ⟨by linarith [Real.pi_pos], le_rfl⟩) hlt
        change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
          polytopeDirectionalValue (smoothSupportCurve h theta) theta at hstrict
        rw [hself, heqPsi] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · have hstrict := strictAntiOn_smoothSupportCurve_projection_right
          hsmooth hcurv theta
          (show theta ∈ Icc theta (theta + Real.pi) from
            ⟨le_rfl, by linarith [Real.pi_pos]⟩)
          (show psi ∈ Icc theta (theta + Real.pi) from
            ⟨hgt.le, hk.2.le⟩) hgt
        change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
          polytopeDirectionalValue (smoothSupportCurve h theta) theta at hstrict
        rw [hself, heqPsi] at hstrict
        exact (lt_irrefl _ hstrict).elim
  · rintro ⟨k, rfl⟩
    have hcurvePeriod := periodic_smoothSupportCurve hperiodic
    rw [(hcurvePeriod.int_mul k) theta]
    exact polytopeDirectionalValue_smoothSupportCurve_self h theta

/-- A smooth periodic positive-curvature support curve is injective on every
half-open fundamental period. -/
theorem injOn_smoothSupportCurve_Ico
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (a : ℝ) :
    Set.InjOn (smoothSupportCurve h) (Ico a (a + 2 * Real.pi)) := by
  intro x hx y hy hxy
  simp only [mem_Ico] at hx hy
  have heqProjection :
      polytopeDirectionalValue (smoothSupportCurve h y) x = h x := by
    rw [← hxy]
    exact polytopeDirectionalValue_smoothSupportCurve_self h x
  obtain ⟨k, hyk⟩ :=
    (polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
      hsmooth hperiodic hcurv x y).mp heqProjection
  have hklt : (k : ℝ) < 1 := by
    rw [hyk] at hy
    nlinarith only [hy.2, hx.1, Real.pi_pos]
  have hkgt : (-1 : ℝ) < (k : ℝ) := by
    rw [hyk] at hy
    nlinarith only [hy.1, hx.2, Real.pi_pos]
  have hkltInt : k < 1 := by exact_mod_cast hklt
  have hkgtInt : (-1 : ℤ) < k := by exact_mod_cast hkgt
  have hk : k = 0 := by omega
  subst k
  simpa using hyk.symm

/-- A unit normal has directional value one in its own direction. -/
theorem polytopeDirectionalValue_smoothSupportUnitNormal_self
    (theta : ℝ) :
    polytopeDirectionalValue (smoothSupportUnitNormal theta) theta = 1 := by
  unfold polytopeDirectionalValue smoothSupportUnitNormal
  simp only [circleMap_zero_re, circleMap_zero_im, one_mul]
  nlinarith only [Real.sin_sq_add_cos_sq theta]

/-- A support-curve point cannot lie in the interior of its prescribed closed
support envelope: moving a short distance in its outward normal direction
violates the active halfspace. -/
theorem smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
    (h : ℝ → ℝ) (theta : ℝ) :
    smoothSupportCurve h theta ∉ smoothSupportOpenEnvelope h := by
  intro hz
  obtain ⟨eps, heps, hepsSub⟩ :=
    Metric.isOpen_iff.mp (isOpen_smoothSupportOpenEnvelope h)
      (smoothSupportCurve h theta) hz
  let w : ℂ := smoothSupportCurve h theta +
    (eps / 2) • smoothSupportUnitNormal theta
  have hwball : w ∈ ball (smoothSupportCurve h theta) eps := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    unfold smoothSupportUnitNormal
    rw [norm_circleMap_zero, abs_one, mul_one]
    linarith
  have hwclosed : w ∈ smoothSupportClosedEnvelope h :=
    interior_subset (hepsSub hwball)
  have hwdir := hwclosed theta
  have hself := polytopeDirectionalValue_smoothSupportCurve_self h theta
  have hwdirEq : polytopeDirectionalValue w theta = h theta + eps / 2 := by
    dsimp only [w]
    rw [← smoothSupportDirectionalLinearMap_apply,
      map_add, map_smul, smoothSupportDirectionalLinearMap_apply,
      smoothSupportDirectionalLinearMap_apply,
      polytopeDirectionalValue_smoothSupportUnitNormal_self,
      hself]
    simp only [smul_eq_mul, mul_one]
  rw [hwdirEq] at hwdir
  linarith

/-- Every point of the rounded support curve belongs to its closed support
envelope. -/
theorem polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) := by
  intro phi
  exact polytopeDirectionalValue_smoothSupportCurve_le
    (contDiff_polytopeRoundedSupport hu delta rho)
    (periodic_polytopeRoundedSupport u delta rho)
    (fun x => by
      unfold smoothSupportCurvatureRadius
      exact polytopeRoundedSupport_add_deriv_deriv_pos
        hu hdelta hrho x)
    phi theta

/-- Every point of the rounded support curve lies on the frontier of the open
rounded support envelope. -/
theorem polytopeRoundedSupportCurve_mem_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  rw [(isOpen_smoothSupportOpenEnvelope _).frontier_eq]
  constructor
  · rw [closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hu hdelta hrho]
    exact polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
      hu hdelta hrho theta
  · exact smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
      (polytopeRoundedSupport u delta rho) theta

/-- The range of the rounded support curve is contained in the frontier of
its open support envelope. -/
theorem range_polytopeRoundedSupportCurve_subset_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) ⊆
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  rintro z ⟨theta, rfl⟩
  exact polytopeRoundedSupportCurve_mem_frontier hu hdelta hrho theta

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
