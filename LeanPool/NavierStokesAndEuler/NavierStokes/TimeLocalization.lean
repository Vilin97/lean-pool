/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement

@[expose] public section

/-!
# Time localization of the actual presingular fields

The velocity and pressure are multiplied by the constructed smooth switch from
`SmoothCutoffs`. This gives zero initial velocity without an initial-value
assumption on the original field. The divergence, residual and blowup claims
below use the concrete operators and quantified blowup definition from
`ProblemStatement`.

This transformation does not construct the incoming singular fields or a smooth
global force extension. It supplies the time-switch portion of Proposition 11.4.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.TimeLocalization

open ProblemStatement SmoothCutoffs ResidualCalculus

def activatedVelocity (u : VelocityField) : VelocityField :=
  fun z => timeSwitch z.1 • u z

def activatedPressure (p : PressureField) : PressureField :=
  fun z => timeSwitch z.1 * p z

theorem activatedVelocity_smooth (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContDiffOn ℝ ∞ (activatedVelocity u) preSingularDomain :=
  (timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul hu

theorem activatedPressure_smooth (p : PressureField)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (activatedPressure p) preSingularDomain :=
  (timeSwitch_contDiff.comp contDiff_fst).contDiffOn.mul hp

theorem activatedVelocity_periodic (u : VelocityField) (times : Set ℝ)
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (activatedVelocity u) := by
  intro t ht x i
  change timeSwitch t • u (t, x + coordinateVector i) = timeSwitch t • u (t, x)
  rw [hu t ht x i]

theorem activatedPressure_periodic (p : PressureField) (times : Set ℝ)
    (hp : UnitSpatialPeriodsOn times p) :
    UnitSpatialPeriodsOn times (activatedPressure p) := by
  intro t ht x i
  change timeSwitch t * p (t, x + coordinateVector i) = timeSwitch t * p (t, x)
  rw [hp t ht x i]

theorem activatedVelocity_zero_early (u : VelocityField) {t : ℝ}
    (ht : |t| ≤ 3 / 8) (x : Space) : activatedVelocity u (t, x) = 0 := by
  simp only [activatedVelocity, timeSwitch_zero_of_abs_le ht, zero_smul]

theorem activatedPressure_zero_early (p : PressureField) {t : ℝ}
    (ht : |t| ≤ 3 / 8) (x : Space) : activatedPressure p (t, x) = 0 := by
  simp only [activatedPressure, timeSwitch_zero_of_abs_le ht, zero_mul]

/-- No hypothesis on `u (0,x)` is required. -/
theorem activatedVelocity_zero_initial (u : VelocityField) (x : Space) :
    activatedVelocity u (0, x) = 0 :=
  activatedVelocity_zero_early u (by norm_num) x

theorem activatedPressure_zero_initial (p : PressureField) (x : Space) :
    activatedPressure p (0, x) = 0 :=
  activatedPressure_zero_early p (by norm_num) x

theorem activatedVelocity_eq_late (u : VelocityField) {t : ℝ}
    (ht : 3 / 4 ≤ t) (x : Space) : activatedVelocity u (t, x) = u (t, x) := by
  simp only [activatedVelocity, timeSwitch_one_of_three_quarters_le ht, one_smul]

theorem activatedPressure_eq_late (p : PressureField) {t : ℝ}
    (ht : 3 / 4 ≤ t) (x : Space) : activatedPressure p (t, x) = p (t, x) := by
  simp only [activatedPressure, timeSwitch_one_of_three_quarters_le ht, one_mul]

/-- The entire spacetime field agrees locally, so all its existing local jets
agree at every time strictly later than `3/4`. -/
theorem activatedVelocity_eventuallyEq_late (u : VelocityField) {t : ℝ}
    (ht : 3 / 4 < t) (x : Space) : activatedVelocity u =ᶠ[𝓝 (t, x)] u := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (t, x)] (fun _ => 1) :=
    (timeSwitch_eventually_one ht).comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedVelocity, hz, one_smul]

theorem activatedPressure_eventuallyEq_late (p : PressureField) {t : ℝ}
    (ht : 3 / 4 < t) (x : Space) : activatedPressure p =ᶠ[𝓝 (t, x)] p := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (t, x)] (fun _ => 1) :=
    (timeSwitch_eventually_one ht).comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedPressure, hz, one_mul]

/-- Restricting to a spatial slice is smooth also at time zero, because the
slice maps entirely into the relative presingular domain. -/
theorem spatial_smooth_including_initial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SpaceTime → V) (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x : Space => g (t, x)) := by
  apply contDiffOn_univ.mp
  exact hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn (by
    intro x _
    exact ⟨ht, mem_univ x⟩)

theorem activatedVelocity_divergence (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) (x : Space) :
    spatialDivergence (activatedVelocity u) t x =
      timeSwitch t * spatialDivergence u t x := by
  change spatialDivergence (fun z => timeSwitch t • u z) t x = _
  exact spatialDivergence_const_smul u t x (timeSwitch t)
    ((spatial_smooth_including_initial u hu t ht).differentiable (by simp) x)

theorem activatedVelocity_divergence_free (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (activatedVelocity u) t x = 0 := by
  intro t ht x
  rw [activatedVelocity_divergence u hu t ht x, hdiv t ht x, mul_zero]

/-- Exact residual of the constructed activation: `χ R + χ' u + (χ²-χ)(u·∇)u`. -/
theorem activated_residual_formula (u : VelocityField) (p : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    navierStokesResidual (activatedVelocity u) (activatedPressure p) t x =
      timeSwitch t • navierStokesResidual u p t x + deriv timeSwitch t • u (t, x) +
        (timeSwitch t * timeSwitch t - timeSwitch t) • advection u t x := by
  unfold activatedVelocity activatedPressure
  simpa only [deriv, smul_eq_mul] using
    navierStokesResidual_time_smul u p timeSwitch t x
      (timeSwitch_contDiff.differentiable (by simp) t)
      (temporal_differentiable_of_presingular_smooth u hu t ht x)
      ((spatial_contDiff_of_presingular_smooth u hu t ht).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      ((spatial_contDiff_of_presingular_smooth p hp t ht).differentiable (by simp) x)

theorem activated_temporalDerivative_eq_late (u : VelocityField) {t : ℝ}
    (ht : 3 / 4 < t) (x : Space) :
    temporalDerivative (activatedVelocity u) t x = temporalDerivative u t x := by
  have he : (fun s : ℝ => activatedVelocity u (s, x)) =ᶠ[𝓝 t]
      (fun s : ℝ => u (s, x)) := by
    filter_upwards [timeSwitch_eventually_one ht] with s hs
    simp only [activatedVelocity, hs, one_smul]
  unfold temporalDerivative
  rw [he.fderiv_eq]

/-- Local agreement proves residual agreement without any smoothness assumption
on the original fields. The same concrete derivative operators are used. -/
theorem activated_residual_eq_late (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : 3 / 4 < t) (x : Space) :
    navierStokesResidual (activatedVelocity u) (activatedPressure p) t x =
      navierStokesResidual u p t x := by
  unfold navierStokesResidual
  rw [activated_temporalDerivative_eq_late u ht x]
  simp only [advection, spatialLaplacian, spatialDerivative, pressureGradient,
    activatedVelocity, activatedPressure,
    timeSwitch_one_of_three_quarters_le ht.le, one_smul, one_mul]

theorem activatedVelocity_norm_le (u : VelocityField) (z : SpaceTime) :
    ‖activatedVelocity u z‖ ≤ ‖u z‖ := by
  have hs := timeSwitch_mem_Icc z.1
  rw [activatedVelocity, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

/-- Activating the field does not remove speed blowup, because the switch is
identically one on the final quarter of the time interval. -/
theorem activatedVelocity_speed_unbounded (u : VelocityField)
    (hu : SpeedUnboundedAtOne u) : SpeedUnboundedAtOne (activatedVelocity u) := by
  intro M hM δ hδ
  have hsmall : 0 < min δ (1 / 4 : ℝ) := lt_min hδ (by norm_num)
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hu M hM (min δ (1 / 4)) hsmall
  have hlate : 3 / 4 < t := by
    have hmin := min_le_right δ (1 / 4 : ℝ)
    linarith
  refine ⟨t, x, ht, ?_, ?_⟩
  · have hmin := min_le_left δ (1 / 4 : ℝ)
    linarith
  · simpa only [activatedVelocity_eq_late u hlate.le x] using hlarge

theorem activatedVelocity_speed_unbounded_iff (u : VelocityField) :
    SpeedUnboundedAtOne (activatedVelocity u) ↔ SpeedUnboundedAtOne u := by
  constructor
  · intro hu M hM δ hδ
    obtain ⟨t, x, ht, hnear, hlarge⟩ := hu M hM δ hδ
    exact ⟨t, x, ht, hnear, hlarge.trans_le (activatedVelocity_norm_le u (t, x))⟩
  · exact activatedVelocity_speed_unbounded u

/-- A constructed pair with zero initial velocity, retaining the incoming
presingular smoothness, periods, divergence constraint and terminal blowup.
The input field is not assumed to vanish initially. -/
theorem exists_time_localized_pair (u : VelocityField) (p : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u) :
    ∃ v : VelocityField, ∃ q : PressureField,
      ContDiffOn ℝ ∞ v preSingularDomain ∧
      ContDiffOn ℝ ∞ q preSingularDomain ∧
      UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) v ∧
      UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) q ∧
      (∀ x : Space, v (0, x) = 0) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence v t x = 0) ∧
      SpeedUnboundedAtOne v ∧
      (∀ t : ℝ, 3 / 4 < t → ∀ x : Space,
        v (t, x) = u (t, x) ∧ q (t, x) = p (t, x) ∧
          navierStokesResidual v q t x = navierStokesResidual u p t x) := by
  refine ⟨activatedVelocity u, activatedPressure p,
    activatedVelocity_smooth u hu, activatedPressure_smooth p hp,
    activatedVelocity_periodic u _ huper, activatedPressure_periodic p _ hpper,
    activatedVelocity_zero_initial u, activatedVelocity_divergence_free u hu hdiv,
    activatedVelocity_speed_unbounded u hunbounded, ?_⟩
  intro t ht x
  exact ⟨activatedVelocity_eq_late u ht.le x, activatedPressure_eq_late p ht.le x,
    activated_residual_eq_late u p ht x⟩

end NavierStokes.TimeLocalization
