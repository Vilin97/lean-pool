/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicResidualLimits
public import LeanPool.NavierStokesAndEuler.NavierStokes.DirectAngularDiagonal
import LeanPool.NavierStokesAndEuler.NavierStokes.CandidateFromLimits

/-!
# Spatial localization of a curl field and a direct angular field

The manuscript cuts direct angular means as vector fields, separately from
the potentials whose curls give the other components.  The construction here
keeps that distinction.  The existing spatial cutoff is axisymmetric; its
action on direct angular means can therefore be supplied by the angular-field
calculus.  No compactly supported potential for an arbitrary angular mean is
postulated.

The endpoint results below take the original mixed fields, their actual
one-sided extensions, and the joint residual limits as inputs.  They construct
the periodic fields and their residual limits.  They do not establish the
correction iteration or the existence of singular incoming fields.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedPeriodicAssembly

open ProblemStatement Set Filter
open scoped Topology ContDiff BigOperators

/-- The direct field is added after taking the curl. -/
def velocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialCurl.spatialCurl A z + v z

/-- Spatial localization keeps every potential-cutoff derivative. -/
def cutVelocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialLocalization.cutVelocity A z + SpatialLocalization.cutPotential v z

/-- Periodize the cut potential and the cut direct field separately. -/
def periodicVelocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialLocalization.periodicVelocity A z +
    PeriodicLocalization.periodize (SpatialLocalization.cutPotential v) z

/-- Original residual, defined pointwise by `navierStokesResidual (velocity A v) p z.1 z.2`. -/
def originalResidual (A v : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (velocity A v) p z.1 z.2

/-- Cut residual, defined pointwise by `navierStokesResidual (cutVelocity A v)
(SpatialLocalization.cutPressure p) z.1 z.2`. -/
def cutResidual (A v : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (cutVelocity A v)
    (SpatialLocalization.cutPressure p) z.1 z.2

/-- Periodic residual, defined pointwise by `navierStokesResidual (periodicVelocity A v)
(SpatialLocalization.periodicPressure p) z.1 z.2`. -/
def periodicResidual (A v : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (periodicVelocity A v)
    (SpatialLocalization.periodicPressure p) z.1 z.2

theorem periodicVelocity_smoothOn {A v : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicVelocity A v) (times ×ˢ (univ : Set Space)) :=
  (SpatialLocalization.periodicVelocity_smoothOn hA).add
    (PeriodicLocalization.contDiffOn_periodize (SpatialLocalization.cutPotential_supported v)
      ((SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hv))

theorem periodicVelocity_periodic (A v : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicVelocity A v) := by
  intro t ht x i
  simp only [periodicVelocity,
    SpatialLocalization.periodicVelocity_periodic A times t ht x i,
    PeriodicLocalization.unitSpatialPeriodsOn_periodize
      (SpatialLocalization.cutPotential v) times t ht x i]

theorem periodicVelocity_eventuallyEq_cut (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicVelocity A v =ᶠ[𝓝 z] cutVelocity A v :=
  (SpatialLocalization.periodicVelocity_eventuallyEq_cut A hz).add
    (PeriodicLocalization.periodize_eventuallyEq
      (SpatialLocalization.cutPotential_supported v) hz)

theorem cutVelocity_eventuallyEq (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ SpatialLocalization.plateau) :
    cutVelocity A v =ᶠ[𝓝 z] velocity A v :=
  (SolenoidalDiagonal.spatialCurl_eventuallyEq
    (SpatialLocalization.cutPotential_eventuallyEq A hz)).add
      (SpatialLocalization.cutPotential_eventuallyEq v hz)

theorem periodicVelocity_eventuallyEq (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ SpatialLocalization.plateau) :
    periodicVelocity A v =ᶠ[𝓝 z] velocity A v :=
  (periodicVelocity_eventuallyEq_cut A v (SpatialLocalization.plateau_subset_innerCube hz)).trans
    (cutVelocity_eventuallyEq A v hz)

theorem periodicVelocity_origin (A v : VelocityField) (t : ℝ) :
    periodicVelocity A v (t, 0) = velocity A v (t, 0) :=
  (periodicVelocity_eventuallyEq A v SpatialLocalization.zero_mem_plateau).self_of_nhds

theorem periodicResidual_eventuallyEq_cut (A v : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicResidual A v p =ᶠ[𝓝 z] cutResidual A v p :=
  ResidualRegularity.residual_eventuallyEq (periodicVelocity_eventuallyEq_cut A v hz)
    (SpatialLocalization.periodicPressure_eventuallyEq_cut p hz)

theorem cutResidual_eventuallyEq_original (A v : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ SpatialLocalization.plateau) :
    cutResidual A v p =ᶠ[𝓝 z] originalResidual A v p :=
  ResidualRegularity.residual_eventuallyEq (cutVelocity_eventuallyEq A v hz)
    (SpatialLocalization.cutPressure_eventuallyEq p hz)

theorem spatialDivergence_congr {u v : VelocityField} {z : SpaceTime}
    (he : u =ᶠ[𝓝 z] v) : spatialDivergence u z.1 z.2 = spatialDivergence v z.1 z.2 := by
  unfold spatialDivergence spatialDerivative
  rw [ResidualRegularity.space_fderiv_congr he]

theorem spatialDivergence_periodic {u : VelocityField} {times : Set ℝ}
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => spatialDivergence u z.1 z.2) := by
  intro t ht x i
  unfold spatialDivergence spatialDerivative
  have he := ResidualRegularity.space_fderiv_periods hu t ht x i
  dsimp only at he ⊢
  rw [he]

/-- Disjoint support permits checking the divergence on one local copy.
No convergence or differentiability of a formal infinite sum is assumed. -/
theorem periodize_divergence_free {v : VelocityField}
    (hs : PeriodicLocalization.SupportedInCube (1 / 4) v) (t : ℝ)
    (hd : ∀ x, spatialDivergence v t x = 0) (x : Space) :
    spatialDivergence (PeriodicLocalization.periodize v) t x = 0 := by
  have hp := spatialDivergence_periodic
    (PeriodicLocalization.unitSpatialPeriodsOn_periodize v univ)
  have he := PeriodicLocalization.periodize_eventuallyEq hs
    (z := (t, PeriodicResidualLimits.representative x))
    (PeriodicResidualLimits.representative_mem_innerCube x)
  calc
    _ = spatialDivergence (PeriodicLocalization.periodize v) t
        (PeriodicResidualLimits.representative x) :=
      ((CompactForceDecay.periodic_integerShift hp t
        (PeriodicResidualLimits.nearestIndex x)).sub_eq x).symm
    _ = spatialDivergence v t (PeriodicResidualLimits.representative x) :=
      spatialDivergence_congr he
    _ = 0 := hd _

theorem spatialDivergence_add {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) x)
    (hv : DifferentiableAt ℝ (fun y => v (t, y)) x) :
    spatialDivergence (fun z => u z + v z) t x =
      spatialDivergence u t x + spatialDivergence v t x := by
  simp only [spatialDivergence, spatialDerivative, fderiv_fun_add hu hv,
    _root_.add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-- The angular-field calculus supplies `hd` from axisymmetry.  The curl
component and the lattice periodization introduce no new divergence. -/
theorem periodicVelocity_divergence_free {A v : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (times ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ times, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    spatialDivergence (periodicVelocity A v) t x = 0 := by
  have hleft := SpatialCurl.contDiff_spatialSlice
    (SpatialLocalization.periodicVelocity_smoothOn hA) ht
  have hright := SpatialCurl.contDiff_spatialSlice
    (PeriodicLocalization.contDiffOn_periodize (SpatialLocalization.cutPotential_supported v)
      ((SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hv)) ht
  change spatialDivergence (fun z => SpatialLocalization.periodicVelocity A z +
    PeriodicLocalization.periodize (SpatialLocalization.cutPotential v) z) t x = 0
  rw [spatialDivergence_add
    (hleft.differentiable (by simp) x) (hright.differentiable (by simp) x),
    SpatialLocalization.periodicVelocity_divergence_free hA ht x,
    periodize_divergence_free (SpatialLocalization.cutPotential_supported v) t (hd t ht) x,
    add_zero]

theorem cutResidual_smoothOn {A v : VelocityField} {p : PressureField} {U : Set SpaceTime}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hv : ContDiffOn ℝ ∞ v U) (hp : ContDiffOn ℝ ∞ p U) :
    ContDiffOn ℝ ∞ (cutResidual A v p) U := by
  have hc : ContDiffOn ℝ ∞ (fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2) U :=
    (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn
  have hAc : ContDiffOn ℝ ∞ (SpatialLocalization.cutPotential A) U := hc.smul hA
  have hcurl : ContDiffOn ℝ ∞ (SpatialLocalization.cutVelocity A) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      (hAc.contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  exact ResidualRegularity.contDiffOn_residual hU (hcurl.add (hc.smul hv)) (hc.mul hp)

theorem cutResidual_eventuallyEq {A A' v v' : VelocityField} {p p' : PressureField}
    {z : SpaceTime} (hA : A =ᶠ[𝓝 z] A') (hv : v =ᶠ[𝓝 z] v') (hp : p =ᶠ[𝓝 z] p') :
    cutResidual A v p =ᶠ[𝓝 z] cutResidual A' v' p' := by
  have hAc : SpatialLocalization.cutPotential A =ᶠ[𝓝 z]
      SpatialLocalization.cutPotential A' := by
    filter_upwards [hA] with w hw
    simp only [SpatialLocalization.cutPotential, hw]
  have hvc : SpatialLocalization.cutPotential v =ᶠ[𝓝 z]
      SpatialLocalization.cutPotential v' := by
    filter_upwards [hv] with w hw
    simp only [SpatialLocalization.cutPotential, hw]
  have hpc : SpatialLocalization.cutPressure p =ᶠ[𝓝 z]
      SpatialLocalization.cutPressure p' := by
    filter_upwards [hp] with w hw
    simp only [SpatialLocalization.cutPressure, hw]
  exact ResidualRegularity.residual_eventuallyEq
    ((SolenoidalDiagonal.spatialCurl_eventuallyEq hAc).add hvc) hpc

/-- All three original components have genuine smooth local extensions. -/
def cutResidualExtension {A v : VelocityField} {p : PressureField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (ev : JointResidualLimits.OneSidedExtension v x)
    (ep : JointResidualLimits.OneSidedExtension p x) :
    JointResidualLimits.OneSidedExtension (cutResidual A v p) x where
  value := cutResidual eA.value ev.value ep.value
  domain := (eA.domain ∩ ev.domain) ∩ ep.domain
  isOpen := (eA.isOpen.inter ev.isOpen).inter ep.isOpen
  mem := ⟨⟨eA.mem, ev.mem⟩, ep.mem⟩
  smooth := cutResidual_smoothOn ((eA.isOpen.inter ev.isOpen).inter ep.isOpen)
    (eA.smooth.mono (fun _ h => h.1.1)) (ev.smooth.mono (fun _ h => h.1.2))
    (ep.smooth.mono inter_subset_right)
  agrees := by
    intro z hz
    have hO := (((eA.isOpen.inter ev.isOpen).inter ep.isOpen).inter
      (SpacetimeEndpoint.openPast_isOpen 1))
    apply (cutResidual_eventuallyEq (z := z) ?_ ?_ ?_).self_of_nhds
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact eA.agrees ⟨hw.1.1.1, hw.2⟩
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact ev.agrees ⟨hw.1.1.2, hw.2⟩
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact ep.agrees ⟨hw.1.2, hw.2⟩

theorem cutResidual_awayExtensions {A v : VelocityField} {p : PressureField}
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) :
    JointResidualLimits.AwayExtensions (cutResidual A v p) := by
  intro x hx
  exact ⟨cutResidualExtension (Classical.choice (eA x hx)) (Classical.choice (ev x hx))
    (Classical.choice (ep x hx))⟩

theorem cutResidual_vanishingJointJets {A v : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p)) :
    JointResidualLimits.VanishingJointJets (cutResidual A v p) := by
  intro n
  apply (hz n).congr'
  exact ((SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (cutResidual_eventuallyEq_original A v p (z := (1, 0))
      SpatialLocalization.zero_mem_plateau) n).filter_mono nhdsWithin_le_nhds).symm

theorem periodicResidual_periodic (A v : VelocityField) (p : PressureField) :
    UnitSpatialPeriodsOn univ (periodicResidual A v p) :=
  ResidualRegularity.residual_periods isOpen_univ
    (periodicVelocity_periodic A v univ) (SpatialLocalization.periodicPressure_periodic p univ)

theorem periodicResidual_jets_locally_cut (A v : VelocityField) (p : PressureField)
    (x : Space) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A v p) =ᶠ[𝓝 ((1 : ℝ), x)]
      (fun z => iteratedFDeriv ℝ n (cutResidual A v p)
        (z.1, z.2 - CompactForceDecay.integerShift (PeriodicResidualLimits.nearestIndex x))) := by
  have hp := CompactForceDecay.iteratedFDeriv_periods (periodicResidual_periodic A v p) n
  have hm : Continuous (fun z : SpaceTime =>
      z.2 - CompactForceDecay.integerShift (PeriodicResidualLimits.nearestIndex x)) :=
    continuous_snd.sub continuous_const
  have he : ∀ᶠ z : SpaceTime in 𝓝 ((1 : ℝ), x),
      z.2 - CompactForceDecay.integerShift (PeriodicResidualLimits.nearestIndex x) ∈
        PeriodicLocalization.innerCube (1 / 4) :=
    hm.continuousAt.preimage_mem_nhds ((PeriodicLocalization.isOpen_innerCube _).mem_nhds
      (PeriodicResidualLimits.representative_mem_innerCube x))
  filter_upwards [he] with z hz
  rw [← (CompactForceDecay.periodic_integerShift hp z.1
    (PeriodicResidualLimits.nearestIndex x)).sub_eq z.2]
  exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (periodicResidual_eventuallyEq_cut A v p hz) n).self_of_nhds

/-- Constructed tensor limits for every point, including all lattice copies
of the singular point.  No continuity of the chosen representative is used. -/
def boundaryLimits (A v : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (x : Space) :
    FormalMultilinearSeries ℝ SpaceTime Space :=
  JointResidualLimits.boundaryLimits (cutResidual A v p)
    (cutResidual_awayExtensions eA ev ep) (PeriodicResidualLimits.representative x)

@[simp] theorem boundaryLimits_zero (A v : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    boundaryLimits A v p eA ev ep 0 n = 0 := by
  simp only [boundaryLimits, PeriodicResidualLimits.representative_zero,
    JointResidualLimits.boundaryLimits_zero]

theorem boundaryLimits_joint {A v : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) (x : Space) :
    Tendsto (iteratedFDeriv ℝ n (periodicResidual A v p))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (boundaryLimits A v p eA ev ep x n)) := by
  have hlim := JointResidualLimits.boundaryLimits_joint
    (cutResidual_vanishingJointJets hz) (cutResidual_awayExtensions eA ev ep) n
    (PeriodicResidualLimits.representative x)
  have hc := hlim.comp (PeriodicResidualLimits.spatial_sub_tendsto_past
    (CompactForceDecay.integerShift (PeriodicResidualLimits.nearestIndex x)) x)
  exact hc.congr' ((periodicResidual_jets_locally_cut A v p x n).filter_mono
    nhdsWithin_le_nhds).symm

theorem boundaryLimits_continuous {A v : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    Continuous (fun x => boundaryLimits A v p eA ev ep x n) := by
  apply JointResidualLimits.continuous_of_joint_limits
    (p := 𝓝[<] (1 : ℝ)) (F := iteratedFDeriv ℝ n (periodicResidual A v p))
  intro x
  simpa only [JointResidualLimits.past_filter] using boundaryLimits_joint hz eA ev ep n x

theorem boundaryLimits_locallyUniform {A v : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n (periodicResidual A v p) (t, x))
      (fun x => boundaryLimits A v p eA ev ep x n) (𝓝[<] (1 : ℝ)) := by
  apply JointResidualLimits.locallyUniform_of_joint_limits
    (F := iteratedFDeriv ℝ n (periodicResidual A v p))
  intro x
  simpa only [JointResidualLimits.past_filter] using boundaryLimits_joint hz eA ev ep n x

theorem periodicVelocity_speed_unbounded {A v : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖velocity A v (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne (periodicVelocity A v) := by
  have hb : Tendsto (fun t : ℝ => ‖periodicVelocity A v (t, 0)‖) (𝓝[<] 1) atTop := by
    simpa only [periodicVelocity_origin] using haxis
  intro M _ δ hδ
  have hlow : Ioi (max 0 (1 - δ)) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt (by norm_num) (by linarith)))
  have hlarge := hb.eventually (eventually_gt_atTop M)
  have hbefore : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht, hMt, hlo⟩ := (hbefore.and (hlarge.and hlow)).exists
  exact ⟨t, 0, ⟨(le_max_left _ _).trans_lt hlo, ht⟩,
    (le_max_right _ _).trans_lt hlo, hMt⟩

/-- Apply the existing force construction to the actual mixed periodic
velocity.  All remaining analytic assumptions concern the incoming fields. -/
theorem exists_candidate_force {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖velocity A v (t, 0)‖) (𝓝[<] 1) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (TimeLocalization.activatedVelocity (periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      (∀ n : ℕ, ∀ x : Space,
        iteratedFDeriv ℝ n F (1, x) = boundaryLimits A v p eA ev ep x n) := by
  have hu : ContDiffOn ℝ ∞ (periodicVelocity A v) preSingularDomain :=
    periodicVelocity_smoothOn (hA.mono (fun _ h => ⟨h.1.2, h.2⟩))
      (hv.mono (fun _ h => ⟨h.1.2, h.2⟩))
  have hpc : ContDiffOn ℝ ∞ (SpatialLocalization.periodicPressure p) preSingularDomain :=
    SpatialLocalization.periodicPressure_smoothOn (hp.mono (fun _ h => ⟨h.1.2, h.2⟩))
  let L := boundaryLimits A v p eA ev ep
  have hlim := boundaryLimits_locallyUniform hz eA ev ep
  refine ⟨CandidateFromLimits.force _ _ hu hpc L hlim, ?_,
    CandidateFromLimits.force_smooth _ _ hu hpc L hlim,
    CandidateFromLimits.force_boundary_jets _ _ hu hpc L hlim⟩
  apply CandidateFromLimits.candidate_properties _ _ hu hpc L hlim
    (periodicVelocity_periodic A v _) (SpatialLocalization.periodicPressure_periodic p _) ?_
    (periodicVelocity_speed_unbounded haxis)
  intro t ht x
  exact periodicVelocity_divergence_free hA hv hd ht.2 x

/-- The actual angular stage sum, with the manuscript's implicit physical
similarity scale and the same cutoff schedule as the other components. -/
def angularDiagonal (h : ℝ) (a : ℕ → ℝ)
    (D : ℕ → DirectAngularDiagonal.AngularData DirectAngularDiagonal.preterminalSlow) :
    VelocityField :=
  DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)

/-- The direct angular sum is zero on the axis, without changing the
potential's axial value or requiring a radial integral cancellation. -/
theorem angularDiagonal_origin (h : ℝ) (a : ℕ → ℝ)
    (D : ℕ → DirectAngularDiagonal.AngularData DirectAngularDiagonal.preterminalSlow)
    (t : ℝ) : angularDiagonal h a D (t, 0) = 0 :=
  DirectAngularDiagonal.angularSum_axis a _ _ t 0 rfl rfl

/-- The angular hypotheses are only its actual smooth supported scalar
stages.  Its smoothness, localized divergence and zero axis value are proved
before applying the force construction.  Residual flatness and extensions of
the complete incoming fields remain separate analytic obligations. -/
theorem exists_force_for_angular_stages {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData DirectAngularDiagonal.preterminalSlow)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A (angularDiagonal h a D) p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions (angularDiagonal h a D))
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    ∃ F : VelocityField,
      CandidateProperties
        (TimeLocalization.activatedVelocity (periodicVelocity A (angularDiagonal h a D)))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      (∀ n : ℕ, ∀ x : Space,
        iteratedFDeriv ℝ n F (1, x) = boundaryLimits A (angularDiagonal h a D) p eA ev ep x n) := by
  have hv : ContDiffOn ℝ ∞ (angularDiagonal h a D) (SpacetimeEndpoint.openPast 1) :=
    (DirectAngularDiagonal.actual_diagonal_smooth hh hh1 D ha).mono (fun _ hx => hx.1)
  have hd : ∀ t < 1, ∀ x,
      spatialDivergence (SpatialLocalization.cutPotential (angularDiagonal h a D)) t x = 0 :=
    DirectAngularDiagonal.actual_spatialCut_diagonal_divergence hh hh1 D ha
  apply exists_candidate_force hA hv hp hd hz eA ev ep
  simpa only [velocity, angularDiagonal_origin, add_zero] using haxis

end NavierStokes.MixedPeriodicAssembly
