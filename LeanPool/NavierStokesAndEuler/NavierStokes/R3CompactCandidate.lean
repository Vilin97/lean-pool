/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSpatialForceDecay
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicResidualLimits

@[expose] public section

/-!
# The compact whole-space fields behind the periodic construction

Keep the cut potential, direct field, and pressure before periodization.
They agree locally with the periodic fields on the inner cube, and vanish
outside the fixed support cylinder. A second, larger cutoff applied to the
already extended smooth force gives a force on `ℝ³` with compact spatial
support. Locality of the derivatives proves the exact equation.

This construction makes no uniqueness assertion about comparison solutions.
-/

noncomputable section

namespace NavierStokes.R3CompactCandidate

open Set Filter ProblemStatement SpatialLocalization
open scoped ContDiff Topology

/-- The whole-space candidate conditions needed for option (C). -/
structure Properties (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  velocity_support : ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0
  pressure_support : ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → p (t, x) = 0
  force_support : ∃ K : Set Space, IsCompact K ∧ CompactSpatialForceDecay.SupportedIn K f
  zero_initial_velocity : ∀ x, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

def outerCutoff (x : Space) : ℝ := spatialCutoff ((1 / 2 : ℝ) • x)

def outerSupport : Set Space := (fun x : Space => (2 : ℝ) • x) '' supportCylinder

theorem outerSupport_compact : IsCompact outerSupport :=
  isCompact_supportCylinder.image (by fun_prop)

theorem outerCutoff_smooth : ContDiff ℝ ∞ outerCutoff :=
  spatialCutoff_contDiff.comp (by fun_prop)

theorem outerCutoff_one {x : Space} (hx : x ∈ supportCylinder) : outerCutoff x = 1 := by
  have hr := hx.1
  have hz := hx.2
  change radialSquare x ≤ 1 / 16 at hr
  have hrad : |16 * radialSquare ((1 / 2 : ℝ) • x)| ≤ 1 / 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (radialSquare_nonneg _))]
    simp only [radialSquare, PiLp.smul_apply, smul_eq_mul] at hr ⊢
    nlinarith
  have hax : |4 * ((1 / 2 : ℝ) • x) 2| ≤ 1 / 2 := by
    simp only [PiLp.smul_apply, smul_eq_mul, ← mul_assoc]
    norm_num
    linarith
  exact congrArg₂ (· * ·) (SmoothCutoffs.cutoff_one_of_abs_le hrad)
    (SmoothCutoffs.cutoff_one_of_abs_le hax) |>.trans (one_mul 1)

theorem outerCutoff_zero_outside {x : Space} (hx : x ∉ outerSupport) : outerCutoff x = 0 := by
  by_contra h
  have hm : (1 / 2 : ℝ) • x ∈ supportCylinder := spatialCutoff_support_subset h
  apply hx
  refine ⟨(1 / 2 : ℝ) • x, hm, ?_⟩
  simp [smul_smul]

theorem outerCutoff_ne_zero_inner {x : Space} (hx : outerCutoff x ≠ 0) :
    x ∈ PeriodicLocalization.innerCube (1 / 4) := by
  have hm : (1 / 2 : ℝ) • x ∈ supportCylinder := spatialCutoff_support_subset hx
  intro i
  have hb := supportCylinder_coordinate_bound hm i
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul] at hb
  norm_num at hb
  change |x i| < 1 - 1 / 4
  linarith

theorem supportCylinder_inner {x : Space} (hx : x ∈ supportCylinder) :
    x ∈ PeriodicLocalization.innerCube (1 / 4) := by
  intro i
  have hb := supportCylinder_coordinate_bound hx i
  change |x i| < 1 - 1 / 4
  linarith

def compactForce (f : VelocityField) : VelocityField := fun z => outerCutoff z.2 • f z

theorem compactForce_smooth {f : VelocityField} (hf : ContDiffOn ℝ ∞ f futureDomain) :
    ContDiffOn ℝ ∞ (compactForce f) futureDomain :=
  (outerCutoff_smooth.comp contDiff_snd).contDiffOn.smul hf

theorem compactForce_supported (f : VelocityField) :
    CompactSpatialForceDecay.SupportedIn outerSupport (compactForce f) := by
  intro t ht x hx
  simp [compactForce, outerCutoff_zero_outside hx]

theorem compactForce_time_support {f : VelocityField} (hf : CompactFutureTimeSupport f) :
    CompactFutureTimeSupport (compactForce f) := by
  obtain ⟨T, hT, hz⟩ := hf
  exact ⟨T, hT, fun t ht x => by simp [compactForce, hz t ht x]⟩

theorem eventually_zero_outside {V : Type*} [Zero V] {g : SpaceTime → V}
    (hg : ∀ t x, x ∉ supportCylinder → g (t, x) = 0)
    {z : SpaceTime} (hz : z.2 ∉ supportCylinder) : g =ᶠ[𝓝 z] (fun _ => 0) := by
  have hn : {z : SpaceTime | z.2 ∉ supportCylinder} ∈ 𝓝 z :=
    (isClosed_supportCylinder.isOpen_compl.preimage continuous_snd).mem_nhds hz
  filter_upwards [hn] with y hy
  exact hg y.1 y.2 hy

theorem local_model_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g G : SpaceTime → V} (hG : ContDiffOn ℝ ∞ G preSingularDomain)
    (hs : ∀ t x, x ∉ supportCylinder → g (t, x) = 0)
    (he : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) →
      G =ᶠ[𝓝 z] g) : ContDiffOn ℝ ∞ g preSingularDomain := by
  intro z hz
  by_cases hx : z.2 ∈ supportCylinder
  · exact (hG z hz).congr_of_eventuallyEq
      ((he z (supportCylinder_inner hx)).symm.filter_mono nhdsWithin_le_nhds)
      (he z (supportCylinder_inner hx)).self_of_nhds.symm
  · exact contDiffWithinAt_const.congr_of_eventuallyEq
      ((eventually_zero_outside hs hx).filter_mono nhdsWithin_le_nhds) (hs z.1 z.2 hx)

theorem local_model_divergence {u U : VelocityField}
    (hs : ∀ t x, x ∉ supportCylinder → u (t, x) = 0)
    (he : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) →
      U =ᶠ[𝓝 z] u) {t : ℝ}
    (hd : ∀ x, spatialDivergence U t x = 0) : ∀ x, spatialDivergence u t x = 0 := by
  intro x
  by_cases hx : x ∈ supportCylinder
  · unfold spatialDivergence spatialDerivative
    rw [ResidualRegularity.space_fderiv_congr (he (t, x) (supportCylinder_inner hx)).symm]
    exact hd x
  · unfold spatialDivergence spatialDerivative
    rw [ResidualRegularity.space_fderiv_congr (eventually_zero_outside hs (z := (t, x)) hx)]
    simp

theorem local_model_equation {u U : VelocityField} {p P : PressureField} {f : VelocityField}
    (hu : ∀ t x, x ∉ supportCylinder → u (t, x) = 0)
    (hp : ∀ t x, x ∉ supportCylinder → p (t, x) = 0)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u)
    (hep : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → P =ᶠ[𝓝 z] p)
    {t : ℝ} (hNS : ∀ x, navierStokesResidual U P t x = f (t, x)) :
    ∀ x, navierStokesResidual u p t x = compactForce f (t, x) := by
  intro x
  by_cases hx : x ∈ supportCylinder
  · have hi := supportCylinder_inner hx
    rw [← ResidualRegularity.residual_congr (heu (t, x) hi) (hep (t, x) hi), hNS]
    simp [compactForce, outerCutoff_one hx]
  · have hzero := ResidualRegularity.residual_eq_zero_of_eventually_zero
      (eventually_zero_outside hu (z := (t, x)) hx)
      (eventually_zero_outside hp (z := (t, x)) hx)
    rw [hzero]
    by_cases hχ : outerCutoff x = 0
    · simp [compactForce, hχ]
    · have hi := outerCutoff_ne_zero_inner hχ
      have he := ResidualRegularity.residual_congr (heu (t, x) hi) (hep (t, x) hi)
      rw [hNS, hzero] at he
      simp [compactForce, he]

theorem local_model_unbounded {u U : VelocityField}
    (hper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) U)
    (he : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u)
    (hb : SpeedUnboundedAtOne U) : SpeedUnboundedAtOne u := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hb M hM δ hδ
  let y := PeriodicResidualLimits.representative x
  have hperiods : UnitSpatialPeriodsOn univ (fun z : SpaceTime => U (t, z.2)) :=
    fun _ _ z i => hper t ⟨ht.1.le, ht.2⟩ z i
  have heq : U (t, y) = U (t, x) :=
    (CompactForceDecay.periodic_integerShift hperiods t
      (PeriodicResidualLimits.nearestIndex x)).sub_eq x
  have hlocal : U (t, y) = u (t, y) :=
    (he (t, y) (PeriodicResidualLimits.representative_mem_innerCube x)).self_of_nhds
  exact ⟨t, y, ht, hnear, by rwa [← hlocal, heq]⟩

/-- Extract a compact whole-space candidate from its periodic local model. -/
theorem of_periodic_local_model {u U : VelocityField} {p P : PressureField} {f : VelocityField}
    (h : CandidateProperties U P f)
    (hu : ∀ t x, x ∉ supportCylinder → u (t, x) = 0)
    (hp : ∀ t x, x ∉ supportCylinder → p (t, x) = 0)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u)
    (hep : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → P =ᶠ[𝓝 z] p) :
    Properties u p (compactForce f) := by
  refine ⟨local_model_smooth h.velocity_smooth hu heu,
    local_model_smooth h.pressure_smooth hp hep, compactForce_smooth h.force_smooth,
    ⟨supportCylinder, isCompact_supportCylinder, fun t _ => hu t⟩,
    ⟨supportCylinder, isCompact_supportCylinder, fun t _ => hp t⟩,
    ⟨outerSupport, outerSupport_compact, compactForce_supported f⟩, ?_,
    compactForce_time_support h.force_time_support,
    fun t ht => local_model_divergence hu heu (h.divergence_free t ht),
    fun t ht => local_model_equation hu hp heu hep (h.navier_stokes t ht),
    local_model_unbounded h.velocity_periodic heu h.speed_unbounded⟩
  intro x
  by_cases hx : x ∈ supportCylinder
  · rw [← (heu (0, x) (supportCylinder_inner hx)).self_of_nhds]
    exact h.zero_initial_velocity x
  · exact hu 0 x hx

def velocity (A B : VelocityField) : VelocityField :=
  TimeLocalization.activatedVelocity (fun z => cutVelocity A z + cutPotential B z)

def pressure (P : PressureField) : PressureField :=
  TimeLocalization.activatedPressure (cutPressure P)

def periodicVelocity (A B : VelocityField) : VelocityField :=
  TimeLocalization.activatedVelocity (fun z => SpatialLocalization.periodicVelocity A z +
    PeriodicLocalization.periodize (cutPotential B) z)

def periodicPressure (P : PressureField) : PressureField :=
  TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure P)

theorem velocity_supported (A B : VelocityField) (t : ℝ) (x : Space)
    (hx : x ∉ supportCylinder) : velocity A B (t, x) = 0 := by
  have hv : cutVelocity A (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => cutVelocity A (t, y))
      (fun hm => hx (cutVelocity_tsupport A t hm))
  have hc : spatialCutoff x = 0 := by
    by_contra hn
    exact hx (spatialCutoff_support_subset hn)
  simp [velocity, TimeLocalization.activatedVelocity, cutPotential, hv, hc]

theorem pressure_supported (P : PressureField) (t : ℝ) (x : Space)
    (hx : x ∉ supportCylinder) : pressure P (t, x) = 0 := by
  have hc : spatialCutoff x = 0 := by
    by_contra hn
    exact hx (spatialCutoff_support_subset hn)
  simp [pressure, TimeLocalization.activatedPressure, cutPressure, hc]

theorem velocity_locally_eq (A B : VelocityField) (z : SpaceTime)
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicVelocity A B =ᶠ[𝓝 z] velocity A B := by
  have he := (SpatialLocalization.periodicVelocity_eventuallyEq_cut A hz).add
    (PeriodicLocalization.periodize_eventuallyEq (cutPotential_supported B) hz)
  filter_upwards [he] with w hw
  change SmoothCutoffs.timeSwitch w.1 • _ = SmoothCutoffs.timeSwitch w.1 • _
  exact congrArg (fun v : Space => SmoothCutoffs.timeSwitch w.1 • v) hw

theorem pressure_locally_eq (P : PressureField) (z : SpaceTime)
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicPressure P =ᶠ[𝓝 z] pressure P := by
  filter_upwards [SpatialLocalization.periodicPressure_eventuallyEq_cut P hz] with w hw
  exact congrArg (fun p : ℝ => SmoothCutoffs.timeSwitch w.1 * p) hw

/-- Use the very same three raw sums retained by `selected_witness`; no
new singular-field existence hypothesis is needed. -/
theorem of_localized_fields {A B : VelocityField} {P : PressureField} {f : VelocityField}
    (h : CandidateProperties (periodicVelocity A B) (periodicPressure P) f) :
    Properties (velocity A B) (pressure P) (compactForce f) :=
  of_periodic_local_model h (velocity_supported A B) (pressure_supported P)
    (velocity_locally_eq A B) (pressure_locally_eq P)

/-- Every compact whole-space force constructed here satisfies the exact
spatial and temporal decay requirements of the comparator. -/
theorem Properties.forceConditionDecay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : Properties u p f) : Comparator.ForceConditionDecay (ComparatorBridge.toComparator f) := by
  obtain ⟨K, hK, hsupport⟩ := h.force_support
  exact CompactSpatialForceDecay.forceConditionDecay hK h.force_smooth hsupport h.force_time_support

/-- After equality with the compact candidate has been proved, smoothness on
a compact space-time neighborhood of time one gives the contradiction. -/
theorem Properties.not_global_agreement {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : Properties u p f) {v : VelocityField} (hv : ContDiffOn ℝ ∞ v futureDomain) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ futureDomain := fun _ hz => ⟨hz.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hv.continuousOn.mono hsub)
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    by_contra hnot
    rw [hs t ⟨ht.1.le, ht.2⟩ x hnot, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [heq t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

end NavierStokes.R3CompactCandidate
