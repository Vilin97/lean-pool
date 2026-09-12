/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeGluing
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactForceDecay
public import LeanPool.NavierStokesAndEuler.NavierStokes.TimeLocalization
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeEndpoint
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity

/-!
# Conditional candidate construction from actual residual derivative limits

The inputs are physical velocity and pressure fields and locally uniform limits
of every full derivative of their actual Navier--Stokes residual. No future force
or boundary compatibility is assumed. The force is the explicit Taylor--Borel
extension of the traced residual of the activated, zero-extended fields.

The residual limits and the existence of singular incoming fields remain
analytic hypotheses. This module does not prove the unconditional candidate.
-/

section

/-!
# Extending activated physical fields to the whole open past

The physical hypotheses constrain only nonnegative times. We explicitly replace
negative-time values by zero. A zero germ at time zero makes this replacement
jointly smooth, without any assumption on the original negative-time values.
The actual residual is smooth and periodic on the whole open past and retains
the original residual's terminal germ and all of its terminal derivative data.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.PastExtension

open ProblemStatement TimeLocalization ResidualRegularity SmoothCutoffs

/-- Past domain: an abbreviation for `SpacetimeEndpoint.openPast 1`. -/
abbrev pastDomain : Set SpaceTime := SpacetimeEndpoint.openPast 1

section Generic

variable {V : Type*} [NormedAddCommGroup V]

/-- Preserve nonnegative times and replace all negative-time values by zero. -/
def zeroBefore (g : SpaceTime → V) (z : SpaceTime) : V :=
  if 0 ≤ z.1 then g z else 0

theorem zeroBefore_of_nonneg (g : SpaceTime → V) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    zeroBefore g (t, x) = g (t, x) := by
  simp only [zeroBefore, ht, ite_eq_left]

theorem zeroBefore_of_neg (g : SpaceTime → V) {t : ℝ} (ht : t < 0) (x : Space) :
    zeroBefore g (t, x) = 0 := by
  simp only [zeroBefore, not_le.mpr ht, ite_false]

theorem zeroBefore_eqOn_nonneg (g : SpaceTime → V) :
    EqOn (zeroBefore g) g (Ici (0 : ℝ) ×ˢ (univ : Set Space)) := by
  intro z hz
  exact zeroBefore_of_nonneg g hz.1 z.2

theorem zeroBefore_eventuallyEq_pos {g : SpaceTime → V} {z : SpaceTime}
    (hz : 0 < z.1) : zeroBefore g =ᶠ[𝓝 z] g := by
  have hU : {w : SpaceTime | 0 < w.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hz
  filter_upwards [hU] with w hw
  exact zeroBefore_of_nonneg g hw.le w.2

theorem zeroBefore_eventually_zero_neg {g : SpaceTime → V} {z : SpaceTime}
    (hz : z.1 < 0) : zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) := by
  have hU : {w : SpaceTime | w.1 < 0} ∈ 𝓝 z :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hz
  filter_upwards [hU] with w hw
  exact zeroBefore_of_neg g hw w.2

theorem zeroBefore_eventually_zero_at_zero {g : SpaceTime → V} (x : Space)
    (hzero : g =ᶠ[𝓝 (0, x)] (fun _ => 0)) :
    zeroBefore g =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  filter_upwards [hzero] with z hz
  by_cases ht : 0 ≤ z.1
  · simpa only [zeroBefore, ite_eq_left ht] using hz
  · simp only [zeroBefore, ite_eq_right ht]

/-- The zero germ also preserves every local derivative at time zero. -/
theorem zeroBefore_eventuallyEq_nonneg {g : SpaceTime → V}
    (hzero : ∀ x : Space, g =ᶠ[𝓝 (0, x)] (fun _ => 0))
    {t : ℝ} (ht : 0 ≤ t) (x : Space) : zeroBefore g =ᶠ[𝓝 (t, x)] g := by
  rcases lt_or_eq_of_le ht with hpos | heq
  · exact zeroBefore_eventuallyEq_pos hpos
  · subst t
    exact (zeroBefore_eventually_zero_at_zero x (hzero x)).trans (hzero x).symm

variable [NormedSpace ℝ V]

/-- Relative physical smoothness and a zero initial germ suffice for joint
smoothness on the entire open past. No negative-time regularity is assumed. -/
theorem zeroBefore_contDiffOn_past {g : SpaceTime → V}
    (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (hzero : ∀ x : Space, g =ᶠ[𝓝 (0, x)] (fun _ => 0)) :
    ContDiffOn ℝ ∞ (zeroBefore g) pastDomain := by
  rintro ⟨t, x⟩ hz
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · have hc : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : V)) (t, x) :=
      contDiffAt_const
    exact (hc.congr_of_eventuallyEq (zeroBefore_eventually_zero_neg hneg)).contDiffWithinAt
  · subst t
    have hc : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : V)) (0, x) :=
      contDiffAt_const
    exact (hc.congr_of_eventuallyEq
      (zeroBefore_eventually_zero_at_zero x (hzero x))).contDiffWithinAt
  · exact ((smooth_at_interior hg ⟨hpos, hz.1⟩ x).congr_of_eventuallyEq
      (zeroBefore_eventuallyEq_pos hpos)).contDiffWithinAt

omit [NormedSpace ℝ V] in
theorem zeroBefore_periodic {g : SpaceTime → V}
    (hg : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) g) :
    UnitSpatialPeriodsOn (Iio (1 : ℝ)) (zeroBefore g) := by
  intro t ht x i
  by_cases hnonneg : 0 ≤ t
  · rw [zeroBefore_of_nonneg g hnonneg, zeroBefore_of_nonneg g hnonneg]
    exact hg t ⟨hnonneg, ht⟩ x i
  · simp only [zeroBefore, ite_eq_right hnonneg]

end Generic

/-- Activated velocity with explicitly zero negative-time values. -/
def pastVelocity (u : VelocityField) : VelocityField := zeroBefore (activatedVelocity u)

/-- Activated pressure with explicitly zero negative-time values. -/
def pastPressure (p : PressureField) : PressureField := zeroBefore (activatedPressure p)

theorem activatedVelocity_zero_germ (u : VelocityField) (x : Space) :
    activatedVelocity u =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (0, x)] (fun _ => 0) :=
    timeSwitch_eventually_zero.comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedVelocity, hz, zero_smul]

theorem activatedPressure_zero_germ (p : PressureField) (x : Space) :
    activatedPressure p =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (0, x)] (fun _ => 0) :=
    timeSwitch_eventually_zero.comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedPressure, hz, zero_mul]

theorem pastVelocity_eq_activated (u : VelocityField) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    pastVelocity u (t, x) = activatedVelocity u (t, x) :=
  zeroBefore_of_nonneg _ ht x

theorem pastPressure_eq_activated (p : PressureField) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    pastPressure p (t, x) = activatedPressure p (t, x) :=
  zeroBefore_of_nonneg _ ht x

theorem pastVelocity_zero_negative (u : VelocityField) {t : ℝ} (ht : t < 0) (x : Space) :
    pastVelocity u (t, x) = 0 := zeroBefore_of_neg _ ht x

theorem pastPressure_zero_negative (p : PressureField) {t : ℝ} (ht : t < 0) (x : Space) :
    pastPressure p (t, x) = 0 := zeroBefore_of_neg _ ht x

theorem pastVelocity_smooth (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) :
    ContDiffOn ℝ ∞ (pastVelocity u) pastDomain :=
  zeroBefore_contDiffOn_past (activatedVelocity_smooth u hu) (activatedVelocity_zero_germ u)

theorem pastPressure_smooth (p : PressureField)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (pastPressure p) pastDomain :=
  zeroBefore_contDiffOn_past (activatedPressure_smooth p hp) (activatedPressure_zero_germ p)

theorem pastVelocity_periodic (u : VelocityField)
    (hu : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u) :
    UnitSpatialPeriodsOn (Iio (1 : ℝ)) (pastVelocity u) :=
  zeroBefore_periodic (activatedVelocity_periodic u _ hu)

theorem pastPressure_periodic (p : PressureField)
    (hp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn (Iio (1 : ℝ)) (pastPressure p) :=
  zeroBefore_periodic (activatedPressure_periodic p _ hp)

theorem pastVelocity_eventuallyEq_activated (u : VelocityField) {t : ℝ}
    (ht : 0 ≤ t) (x : Space) :
    pastVelocity u =ᶠ[𝓝 (t, x)] activatedVelocity u :=
  zeroBefore_eventuallyEq_nonneg (activatedVelocity_zero_germ u) ht x

theorem pastPressure_eventuallyEq_activated (p : PressureField) {t : ℝ}
    (ht : 0 ≤ t) (x : Space) :
    pastPressure p =ᶠ[𝓝 (t, x)] activatedPressure p :=
  zeroBefore_eventuallyEq_nonneg (activatedPressure_zero_germ p) ht x

theorem pastVelocity_eq_late (u : VelocityField) {t : ℝ} (ht : 3 / 4 ≤ t) (x : Space) :
    pastVelocity u (t, x) = u (t, x) := by
  rw [pastVelocity_eq_activated u (by linarith), activatedVelocity_eq_late u ht]

theorem pastPressure_eq_late (p : PressureField) {t : ℝ} (ht : 3 / 4 ≤ t) (x : Space) :
    pastPressure p (t, x) = p (t, x) := by
  rw [pastPressure_eq_activated p (by linarith), activatedPressure_eq_late p ht]

theorem pastVelocity_eventuallyEq_late (u : VelocityField) {t : ℝ}
    (ht : 3 / 4 < t) (x : Space) : pastVelocity u =ᶠ[𝓝 (t, x)] u :=
  (pastVelocity_eventuallyEq_activated u (by linarith) x).trans
    (activatedVelocity_eventuallyEq_late u ht x)

theorem pastPressure_eventuallyEq_late (p : PressureField) {t : ℝ}
    (ht : 3 / 4 < t) (x : Space) : pastPressure p =ᶠ[𝓝 (t, x)] p :=
  (pastPressure_eventuallyEq_activated p (by linarith) x).trans
    (activatedPressure_eventuallyEq_late p ht x)

theorem pastVelocity_divergence_free (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0) :
    ∀ t ∈ Iio (1 : ℝ), ∀ x : Space, spatialDivergence (pastVelocity u) t x = 0 := by
  intro t ht x
  by_cases hnonneg : 0 ≤ t
  · have hder := spatialDerivative_congr (pastVelocity_eventuallyEq_activated u hnonneg x)
    simpa only [spatialDivergence, hder] using
      activatedVelocity_divergence_free u hu hdiv t ⟨hnonneg, ht⟩ x
  · have heq : pastVelocity u =ᶠ[𝓝 (t, x)] (fun _ => 0) :=
      zeroBefore_eventually_zero_neg (lt_of_not_ge hnonneg)
    have hder := spatialDerivative_congr heq
    simp only [spatialDivergence, hder]
    simp [spatialDerivative]

theorem pastVelocity_speed_unbounded (u : VelocityField) (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (pastVelocity u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := activatedVelocity_speed_unbounded u hu M hM δ hδ
  refine ⟨t, x, ht, hnear, ?_⟩
  simpa only [pastVelocity_eq_activated u ht.1.le] using hlarge

/-- The force used by the endpoint theorem is the actual residual of the
new fields on the entire open past, including negative times. -/
def pastResidual (u : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (pastVelocity u) (pastPressure p) z.1 z.2

theorem pastResidual_smooth (u : VelocityField) (p : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (pastResidual u p) pastDomain :=
  contDiffOn_residual (SpacetimeEndpoint.openPast_isOpen 1)
    (pastVelocity_smooth u hu) (pastPressure_smooth p hp)

theorem pastResidual_periodic (u : VelocityField) (p : PressureField)
    (hu : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn (Iio (1 : ℝ)) (pastResidual u p) :=
  residual_periods isOpen_Iio (pastVelocity_periodic u hu) (pastPressure_periodic p hp)

theorem pastResidual_eventually_zero_nonpos (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : t ≤ 0) (x : Space) :
    pastResidual u p =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
  rcases lt_or_eq_of_le ht with hneg | heq
  · exact residual_eventually_zero
      (zeroBefore_eventually_zero_neg hneg) (zeroBefore_eventually_zero_neg hneg)
  · subst t
    exact residual_eventually_zero
      (zeroBefore_eventually_zero_at_zero x (activatedVelocity_zero_germ u x))
      (zeroBefore_eventually_zero_at_zero x (activatedPressure_zero_germ p x))

theorem pastResidual_zero_nonpos (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : t ≤ 0) (x : Space) : pastResidual u p (t, x) = 0 :=
  (pastResidual_eventually_zero_nonpos u p ht x).self_of_nhds

theorem pastResidual_eq_activated (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    pastResidual u p (t, x) =
      navierStokesResidual (activatedVelocity u) (activatedPressure p) t x :=
  residual_congr (pastVelocity_eventuallyEq_activated u ht x)
    (pastPressure_eventuallyEq_activated p ht x)

theorem pastResidual_eventuallyEq_late (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : 3 / 4 < t) (x : Space) :
    pastResidual u p =ᶠ[𝓝 (t, x)] (fun z => navierStokesResidual u p z.1 z.2) :=
  residual_eventuallyEq (pastVelocity_eventuallyEq_late u ht x)
    (pastPressure_eventuallyEq_late p ht x)

theorem pastResidual_eq_late (u : VelocityField) (p : PressureField)
    {t : ℝ} (ht : 3 / 4 < t) (x : Space) :
    pastResidual u p (t, x) = navierStokesResidual u p t x :=
  (pastResidual_eventuallyEq_late u p ht x).self_of_nhds

/-- Full joint derivative tensors, not only values, retain the terminal germ. -/
theorem pastResidual_iteratedFDeriv_eq_late (u : VelocityField) (p : PressureField)
    (n : ℕ) {t : ℝ} (ht : 3 / 4 < t) (x : Space) :
    iteratedFDeriv ℝ n (pastResidual u p) (t, x) =
      iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x) := by
  have heq := pastResidual_eventuallyEq_late u p ht x
  have heq' : pastResidual u p =ᶠ[𝓝[univ] (t, x)]
      (fun z => navierStokesResidual u p z.1 z.2) := heq.filter_mono nhdsWithin_le_nhds
  simpa only [iteratedFDerivWithin_univ] using
    heq'.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.eq_of_nhds n

/-- Any locally uniform limiting full derivative tensor transfers unchanged.
This hypothesis is not supplied by the zero extension itself. -/
theorem pastResidual_locallyUniform_limit (u : VelocityField) (p : PressureField)
    (n : ℕ) (L : Space → SpaceTime [×n]→L[ℝ] Space)
    (hlim : TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
      L (𝓝[<] (1 : ℝ))) :
    TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n (pastResidual u p) (t, x))
      L (𝓝[<] (1 : ℝ)) := by
  intro U hU x
  obtain ⟨s, hs, hbound⟩ := hlim U hU x
  refine ⟨s, hs, ?_⟩
  have hlate₀ : ∀ᶠ t in 𝓝 (1 : ℝ), 3 / 4 < t :=
    Ioi_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1)
  have hlate : ∀ᶠ t in 𝓝[<] (1 : ℝ), 3 / 4 < t :=
    hlate₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hbound, hlate] with t ht htlate y hy
  rw [pastResidual_iteratedFDeriv_eq_late u p n htlate y]
  exact ht y hy

/-- The full derivative family required by `SpacetimeEndpoint` is supplied
by the actual derivatives of the constructed past residual. -/
theorem pastResidual_derivative_recurrence (u : VelocityField) (p : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) (n : ℕ) (z : SpaceTime)
    (hz : z.1 < 1) :
    HasFDerivAt (iteratedFDeriv ℝ n (pastResidual u p))
      (iteratedFDeriv ℝ (n + 1) (pastResidual u p) z).curryLeft z := by
  have hs : ContDiffAt ℝ ∞ (pastResidual u p) z :=
    (pastResidual_smooth u p hu hp).contDiffAt
      ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds ⟨hz, mem_univ z.2⟩)
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n (pastResidual u p)) z :=
    hs.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  simp only [fderiv_iteratedFDeriv, Function.comp_apply] at hd
  exact hd

/-- A direct adapter to joint endpoint regularity. Only the locally uniform
limits near time one remain an analytic input; no negative-time assumptions
are imposed on the original velocity or pressure. -/
theorem exists_joint_endpoint_extension_of_residual_limits
    (u : VelocityField) (p : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
      (fun x => L x n) (𝓝[<] (1 : ℝ))) :
    ∃ g : VelocityField, EqOn g (pastResidual u p) pastDomain ∧
      ContDiffOn ℝ ∞ g (SpacetimeEndpoint.closedPast 1) ∧
      ∀ n : ℕ, ∀ x : Space,
        iteratedFDerivWithin ℝ n g (SpacetimeEndpoint.closedPast 1) (1, x) = L x n := by
  apply SpacetimeEndpoint.exists_joint_endpoint_extension
    (J := ftaylorSeries ℝ (pastResidual u p))
  · intro z _
    rfl
  · exact pastResidual_derivative_recurrence u p hu hp
  · intro n
    exact pastResidual_locallyUniform_limit u p n (fun x => L x n) (hlim n)

end NavierStokes.PastExtension

end
end

end

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.CandidateFromLimits

open ProblemStatement TimeLocalization

/-- Fill in the endpoint trace after extending the activated residual to
negative times by the construction in `PastExtension`. -/
def tracedResidual (u : VelocityField) (p : PressureField)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space) : VelocityField :=
  SpacetimeEndpoint.extendTrace 1 (PastExtension.pastResidual u p)
    (fun x => (L x 0).curry0)

section Construction

variable (u : VelocityField) (p : PressureField)
variable (hu : ContDiffOn ℝ ∞ u preSingularDomain)
variable (hp : ContDiffOn ℝ ∞ p preSingularDomain)
variable (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
variable (hlim : ∀ n : ℕ, TendstoLocallyUniformly
  (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
  (fun x => L x n) (𝓝[<] (1 : ℝ)))

include hu hp hlim

/-- Closed-side joint smoothness is derived from the actual derivative
recurrence and the supplied locally uniform limits. -/
theorem tracedResidual_smooth :
    ContDiffOn ℝ ∞ (tracedResidual u p L) (SpacetimeEndpoint.closedPast 1) := by
  apply SpacetimeEndpoint.contDiffOn_joint_extension
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_derivative_recurrence u p hu hp
  · intro n
    exact PastExtension.pastResidual_locallyUniform_limit u p n (fun x => L x n) (hlim n)

theorem tracedResidual_boundary_jets (n : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ n (tracedResidual u p L)
      (SpacetimeEndpoint.closedPast 1) (1, x) = L x n := by
  apply SpacetimeEndpoint.boundary_jets_eq_limits
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_derivative_recurrence u p hu hp
  · intro k
    exact PastExtension.pastResidual_locallyUniform_limit u p k (fun y => L y k) (hlim k)

omit hu hp in
theorem tracedResidual_periodic
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn univ (tracedResidual u p L) := by
  apply SpacetimeEndpoint.unit_periods_joint_extension
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_locallyUniform_limit u p 0 (fun x => L x 0) (hlim 0)
  · exact PastExtension.pastResidual_periodic u p huper hpper

/-- The specified force: glue the traced past residual to the Taylor--Borel
series of its actual normal jets. No force is an input to this definition. -/
def force : VelocityField :=
  SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)
    (tracedResidual_smooth u p hu hp L hlim)

theorem force_smooth : ContDiff ℝ ∞ (force u p hu hp L hlim) :=
  SpacetimeGluing.smoothExtension_contDiff (tracedResidual_smooth u p hu hp L hlim)

theorem force_periodic
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn univ (force u p hu hp L hlim) := by
  apply SpacetimeGluing.smoothExtension_unit_periods (tracedResidual_smooth u p hu hp L hlim)
  intro t _ x i
  exact tracedResidual_periodic u p L hlim huper hpper t (mem_univ t) x i

/-- The force agrees with the actual activated residual throughout the
whole past, not just on an arbitrarily short terminal overlap. -/
theorem force_eq_pastResidual {t : ℝ} (ht : t < 1) (x : Space) :
    force u p hu hp L hlim (t, x) = PastExtension.pastResidual u p (t, x) := by
  calc
    _ = tracedResidual u p L (t, x) :=
      SpacetimeGluing.smoothExtension_eqOn_past
        (tracedResidual_smooth u p hu hp L hlim)
        (show (t, x) ∈ SpacetimeGluing.past 1 from ⟨ht.le, mem_univ x⟩)
    _ = _ := SpacetimeEndpoint.extendTrace_of_lt (z := (t, x)) ht

theorem force_eq_activated_residual {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x : Space) :
    force u p hu hp L hlim (t, x) =
      navierStokesResidual (activatedVelocity u) (activatedPressure p) t x := by
  rw [force_eq_pastResidual u p hu hp L hlim ht1 x]
  exact PastExtension.pastResidual_eq_activated u p ht0 x

theorem force_zero_from {t : ℝ} (ht : 2 ≤ t) (x : Space) :
    force u p hu hp L hlim (t, x) = 0 :=
  SpacetimeGluing.smoothExtension_zero_from
    (tracedResidual_smooth u p hu hp L hlim) (by linarith) x

theorem force_zero_nonpos {t : ℝ} (ht : t ≤ 0) (x : Space) :
    force u p hu hp L hlim (t, x) = 0 := by
  rw [force_eq_pastResidual u p hu hp L hlim (by linarith) x]
  exact PastExtension.pastResidual_zero_nonpos u p ht x

theorem force_time_support : CompactFutureTimeSupport (force u p hu hp L hlim) :=
  ⟨2, by norm_num, fun t ht x => force_zero_from u p hu hp L hlim ht x⟩

/-- Every full spacetime boundary derivative is exactly its supplied limit. -/
theorem force_boundary_jets (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (force u p hu hp L hlim) (1, x) = L x n := by
  calc
    _ = iteratedFDerivWithin ℝ n (tracedResidual u p L)
        (SpacetimeEndpoint.closedPast 1) (1, x) :=
      SpacetimeGluing.smoothExtension_iteratedFDeriv
        (tracedResidual_smooth u p hu hp L hlim) n
        ⟨mem_Iic.mpr (le_refl (1 : ℝ)), mem_univ x⟩
    _ = L x n := tracedResidual_boundary_jets u p hu hp L hlim n x

/-- Compact time support and global joint smoothness give arbitrary
polynomial decay of every actual full derivative tensor. -/
theorem force_derivative_decay
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m (force u p hu hp L hlim) (t, x)‖ ≤ C * (1 + t) ^ (-K) :=
  CompactForceDecay.iteratedFDeriv_decay (force u p hu hp L hlim)
    (force_smooth u p hu hp L hlim) (force_periodic u p hu hp L hlim huper hpper)
    (force_time_support u p hu hp L hlim) m K hK

/-- The same conclusion for every ordered choice of time/spatial coordinate
directions and every output component. The constant is uniform in these choices. -/
theorem force_mixed_derivative_decay
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
        |(iteratedFDeriv ℝ m (force u p hu hp L hlim) (t, x)
          (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
          C * (1 + t) ^ (-K) :=
  CompactForceDecay.mixed_coordinate_decay (force u p hu hp L hlim)
    (force_smooth u p hu hp L hlim) (force_periodic u p hu hp L hlim huper hpper)
    (force_time_support u p hu hp L hlim) m K hK

/-- The constructed force and activated fields satisfy the original explicit
candidate specification. No force or closed-side regularity is assumed. -/
theorem candidate_properties
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u) :
    CandidateProperties (activatedVelocity u) (activatedPressure p) (force u p hu hp L hlim) := by
  refine ⟨activatedVelocity_smooth u hu, activatedPressure_smooth p hp,
    (force_smooth u p hu hp L hlim).contDiffOn,
    activatedVelocity_periodic u _ huper, activatedPressure_periodic p _ hpper,
    ?_, activatedVelocity_zero_initial u, force_time_support u p hu hp L hlim,
    activatedVelocity_divergence_free u hu hdiv, ?_,
    activatedVelocity_speed_unbounded u hunbounded⟩
  · intro t _ x i
    exact force_periodic u p hu hp L hlim huper hpper t (mem_univ t) x i
  · intro t ht x
    exact (force_eq_activated_residual u p hu hp L hlim ht.1.le ht.2 x).symm

/-- All force conclusions belong to the same constructed witness. The
remaining hypotheses include the actual residual limits and singular velocity. -/
theorem exists_candidate_force
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u) :
    ∃ F : VelocityField,
      CandidateProperties (activatedVelocity u) (activatedPressure p) F ∧
      ContDiff ℝ ∞ F ∧ UnitSpatialPeriodsOn univ F ∧
      (∀ t : ℝ, 2 ≤ t → ∀ x : Space, F (t, x) = 0) ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) = L x n) ∧
      (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
          |(iteratedFDeriv ℝ m F (t, x)
            (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
            C * (1 + t) ^ (-K)) := by
  refine ⟨force u p hu hp L hlim,
    candidate_properties u p hu hp L hlim huper hpper hdiv hunbounded,
    force_smooth u p hu hp L hlim, force_periodic u p hu hp L hlim huper hpper,
    ?_, force_boundary_jets u p hu hp L hlim, ?_⟩
  · intro t ht x
    exact force_zero_from u p hu hp L hlim ht x
  · intro m K hK
    exact force_mixed_derivative_decay u p hu hp L hlim huper hpper m K hK

/-- Conditional reduction of the primary existential target to the stated
physical fields and locally uniform limits of all actual residual derivatives. -/
theorem candidateStatement_of_residual_limits
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u) : candidateStatement :=
  ⟨activatedVelocity u, activatedPressure p, force u p hu hp L hlim,
    candidate_properties u p hu hp L hlim huper hpper hdiv hunbounded⟩

end Construction

end NavierStokes.CandidateFromLimits
