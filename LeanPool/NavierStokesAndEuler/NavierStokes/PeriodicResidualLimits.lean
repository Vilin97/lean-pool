/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.JointResidualLimits
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialLocalization
public import LeanPool.NavierStokesAndEuler.NavierStokes.CandidateFromLimits
public import Mathlib.Algebra.Order.Round

@[expose] public section

/-!
# Actual residual limits after spatial localization and periodization

The inputs concern the original potential and pressure: smoothness in the
open past, actual local one-sided extensions off the origin, and joint
vanishing of the actual residual jets at the origin. The boundary tensors
of the periodized residual are constructed, including at every nonzero
lattice copy of the origin. No residual identity or residual limit after
periodization is assumed.
-/

noncomputable section

namespace NavierStokes.PeriodicResidualLimits

open ProblemStatement Set Filter
open scoped Topology ContDiff

/-- The residual of the original, actual spatial curl. -/
noncomputable def originalResidual (A : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (SpatialCurl.spatialCurl A) p z.1 z.2

/-- The residual after cutting the potential, including all cutoff terms. -/
noncomputable def cutResidual (A : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (SpatialLocalization.cutVelocity A)
    (SpatialLocalization.cutPressure p) z.1 z.2

/-- The residual of the actual lattice-periodized potential and pressure. -/
noncomputable def periodicResidual (A : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (SpatialLocalization.periodicVelocity A)
    (SpatialLocalization.periodicPressure p) z.1 z.2

theorem cutResidual_smoothOn {A : VelocityField} {p : PressureField} {U : Set SpaceTime}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hp : ContDiffOn ℝ ∞ p U) :
    ContDiffOn ℝ ∞ (cutResidual A p) U := by
  have hAc : ContDiffOn ℝ ∞ (SpatialLocalization.cutPotential A) U :=
    (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hA
  have huc : ContDiffOn ℝ ∞ (SpatialLocalization.cutVelocity A) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      (hAc.contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  exact ResidualRegularity.contDiffOn_residual hU huc
    ((SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.mul hp)

theorem cutResidual_eventuallyEq {A B : VelocityField} {p q : PressureField}
    {z : SpaceTime} (hA : A =ᶠ[𝓝 z] B) (hp : p =ᶠ[𝓝 z] q) :
    cutResidual A p =ᶠ[𝓝 z] cutResidual B q := by
  have hAc : SpatialLocalization.cutPotential A =ᶠ[𝓝 z]
      SpatialLocalization.cutPotential B := by
    filter_upwards [hA] with w hw
    simp only [SpatialLocalization.cutPotential, hw]
  have hpc : SpatialLocalization.cutPressure p =ᶠ[𝓝 z]
      SpatialLocalization.cutPressure q := by
    filter_upwards [hp] with w hw
    simp only [SpatialLocalization.cutPressure, hw]
  exact ResidualRegularity.residual_eventuallyEq
    (SolenoidalDiagonal.spatialCurl_eventuallyEq hAc) hpc

/-- Cutoff and actual differentiation turn extensions of the two inputs
into a local extension of their full nonlinear residual. -/
noncomputable def cutResidualExtension {A : VelocityField} {p : PressureField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (ep : JointResidualLimits.OneSidedExtension p x) :
    JointResidualLimits.OneSidedExtension (cutResidual A p) x where
  value := cutResidual eA.value ep.value
  domain := eA.domain ∩ ep.domain
  isOpen := eA.isOpen.inter ep.isOpen
  mem := ⟨eA.mem, ep.mem⟩
  smooth := cutResidual_smoothOn (eA.isOpen.inter ep.isOpen)
    (eA.smooth.mono inter_subset_left) (ep.smooth.mono inter_subset_right)
  agrees := by
    intro z hz
    have hO := (eA.isOpen.inter ep.isOpen).inter (SpacetimeEndpoint.openPast_isOpen 1)
    apply (cutResidual_eventuallyEq (z := z) ?_ ?_).self_of_nhds
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact eA.agrees ⟨hw.1.1, hw.2⟩
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact ep.agrees ⟨hw.1.2, hw.2⟩

theorem cutResidual_awayExtensions {A : VelocityField} {p : PressureField}
    (hA : JointResidualLimits.AwayExtensions A)
    (hp : JointResidualLimits.AwayExtensions p) :
    JointResidualLimits.AwayExtensions (cutResidual A p) := by
  intro x hx
  exact ⟨cutResidualExtension (Classical.choice (hA x hx)) (Classical.choice (hp x hx))⟩

theorem cutResidual_eventuallyEq_original (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ SpatialLocalization.plateau) :
    cutResidual A p =ᶠ[𝓝 z] originalResidual A p :=
  ResidualRegularity.residual_eventuallyEq
    (SolenoidalDiagonal.spatialCurl_eventuallyEq
      (SpatialLocalization.cutPotential_eventuallyEq A hz))
    (SpatialLocalization.cutPressure_eventuallyEq p hz)

/-- All cutoff-residual jets have the original joint zero limit because
the cutoff is identically one on an actual neighborhood of the origin. -/
theorem cutResidual_vanishingJointJets {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p)) :
    JointResidualLimits.VanishingJointJets (cutResidual A p) := by
  intro n
  apply (hz n).congr'
  exact ((SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (cutResidual_eventuallyEq_original A p (z := (1, 0))
      SpatialLocalization.zero_mem_plateau) n).filter_mono nhdsWithin_le_nhds).symm

/-! ## Exact translation and disjoint-support identities -/

theorem periodicResidual_periodic (A : VelocityField) (p : PressureField) :
    UnitSpatialPeriodsOn univ (periodicResidual A p) :=
  ResidualRegularity.residual_periods isOpen_univ
    (SpatialLocalization.periodicVelocity_periodic A univ)
    (SpatialLocalization.periodicPressure_periodic p univ)

theorem periodicResidual_jet_periodic (A : VelocityField) (p : PressureField) (n : ℕ) :
    UnitSpatialPeriodsOn univ (iteratedFDeriv ℝ n (periodicResidual A p)) :=
  CompactForceDecay.iteratedFDeriv_periods (periodicResidual_periodic A p) n

theorem periodicResidual_jet_integerShift (A : VelocityField) (p : PressureField)
    (n : ℕ) (k : Fin 3 → ℤ) (t : ℝ) (x : Space) :
    iteratedFDeriv ℝ n (periodicResidual A p) (t, x + CompactForceDecay.integerShift k) =
      iteratedFDeriv ℝ n (periodicResidual A p) (t, x) :=
  CompactForceDecay.periodic_integerShift (periodicResidual_jet_periodic A p n) t k x

theorem periodicResidual_jet_sub_integerShift (A : VelocityField) (p : PressureField)
    (n : ℕ) (k : Fin 3 → ℤ) (t : ℝ) (x : Space) :
    iteratedFDeriv ℝ n (periodicResidual A p) (t, x - CompactForceDecay.integerShift k) =
      iteratedFDeriv ℝ n (periodicResidual A p) (t, x) :=
  (CompactForceDecay.periodic_integerShift
    (periodicResidual_jet_periodic A p n) t k).sub_eq x

/-- This equality uses the no-overlap support theorem for the actual
periodized potential and pressure before differentiating the residual. -/
theorem periodicResidual_jets_eq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) z =
      iteratedFDeriv ℝ n (cutResidual A p) z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (SpatialLocalization.periodic_residual_eventuallyEq_cut A p hz) n).self_of_nhds

/-- A chosen fundamental-cube representative; its discontinuities will not
be assumed to preserve continuity of the constructed boundary tensors. -/
noncomputable def nearestIndex (x : Space) : Fin 3 → ℤ := fun i => round (x i)

noncomputable def representative (x : Space) : Space :=
  x - CompactForceDecay.integerShift (nearestIndex x)

theorem representative_mem_innerCube (x : Space) :
    representative x ∈ PeriodicLocalization.innerCube (1 / 4) := by
  intro i
  have h := abs_sub_round (x i)
  change |(representative x) i| < 1 - 1 / 4
  simp only [representative, PiLp.sub_apply, CompactForceDecay.integerShift_apply, nearestIndex]
  linarith

@[simp] theorem representative_zero : representative (0 : Space) = 0 := by
  ext i
  simp [representative, nearestIndex, CompactForceDecay.integerShift_apply]

theorem spatial_sub_tendsto_past (a x : Space) :
    Tendsto (fun z : SpaceTime => (z.1, z.2 - a))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x - a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact (continuous_fst.prodMk (continuous_snd.sub
    continuous_const)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨hz.1, mem_univ _⟩

/-- Near any point, every jet is exactly a translated cutoff-residual jet.
In particular this handles a whole neighborhood of each nonzero lattice copy. -/
theorem periodicResidual_jets_locally_cut (A : VelocityField) (p : PressureField)
    (x : Space) (n : ℕ) :
    iteratedFDeriv ℝ n (periodicResidual A p) =ᶠ[𝓝 ((1 : ℝ), x)]
      (fun z => iteratedFDeriv ℝ n (cutResidual A p)
        (z.1, z.2 - CompactForceDecay.integerShift (nearestIndex x))) := by
  have hm : Continuous (fun z : SpaceTime =>
      z.2 - CompactForceDecay.integerShift (nearestIndex x)) :=
    continuous_snd.sub continuous_const
  have he : ∀ᶠ z : SpaceTime in 𝓝 ((1 : ℝ), x),
      z.2 - CompactForceDecay.integerShift (nearestIndex x) ∈
        PeriodicLocalization.innerCube (1 / 4) :=
    hm.continuousAt.preimage_mem_nhds
      ((PeriodicLocalization.isOpen_innerCube _).mem_nhds (representative_mem_innerCube x))
  filter_upwards [he] with z hz
  rw [← periodicResidual_jet_sub_integerShift A p n (nearestIndex x) z.1 z.2]
  exact periodicResidual_jets_eq_cut A p hz n

/-! ## The constructed boundary series -/

noncomputable def boundaryLimits (A : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (x : Space) :
    FormalMultilinearSeries ℝ SpaceTime Space :=
  JointResidualLimits.boundaryLimits (cutResidual A p)
    (cutResidual_awayExtensions eA ep) (representative x)

@[simp] theorem boundaryLimits_zero (A : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    boundaryLimits A p eA ep 0 n = 0 := by
  simp only [boundaryLimits, representative_zero, JointResidualLimits.boundaryLimits_zero]

theorem boundaryLimits_joint {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) (x : Space) :
    Tendsto (iteratedFDeriv ℝ n (periodicResidual A p))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 (boundaryLimits A p eA ep x n)) := by
  have hlim := JointResidualLimits.boundaryLimits_joint
    (cutResidual_vanishingJointJets hz) (cutResidual_awayExtensions eA ep) n (representative x)
  have hc := hlim.comp (spatial_sub_tendsto_past
    (CompactForceDecay.integerShift (nearestIndex x)) x)
  exact hc.congr' ((periodicResidual_jets_locally_cut A p x n).filter_mono
    nhdsWithin_le_nhds).symm

theorem boundaryLimits_continuous {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    Continuous (fun x => boundaryLimits A p eA ep x n) := by
  apply JointResidualLimits.continuous_of_joint_limits
    (p := 𝓝[<] (1 : ℝ)) (F := iteratedFDeriv ℝ n (periodicResidual A p))
  intro x
  simpa only [JointResidualLimits.past_filter] using boundaryLimits_joint hz eA ep n x

/-- The locally uniform limits are a conclusion of joint convergence;
neither uniform convergence nor continuity of the chosen representatives is input. -/
theorem boundaryLimits_locallyUniform {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n (periodicResidual A p) (t, x))
      (fun x => boundaryLimits A p eA ep x n) (𝓝[<] (1 : ℝ)) := by
  apply JointResidualLimits.locallyUniform_of_joint_limits
    (F := iteratedFDeriv ℝ n (periodicResidual A p))
  intro x
  simpa only [JointResidualLimits.past_filter] using boundaryLimits_joint hz eA ep n x

theorem boundaryLimits_uniformOn_compact {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ)
    {K : Set Space} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ n (periodicResidual A p) (t, x))
      (fun x => boundaryLimits A p eA ep x n) (𝓝[<] (1 : ℝ)) K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp (boundaryLimits_locallyUniform hz eA ep n))
    K hK

@[simp] theorem representative_integerShift (k : Fin 3 → ℤ) :
    representative (CompactForceDecay.integerShift k) = 0 := by
  ext i
  simp [representative, nearestIndex, CompactForceDecay.integerShift_apply]

theorem integerShift_eq_lattice (k : PeriodicLocalization.Lattice) :
    CompactForceDecay.integerShift k = PeriodicLocalization.lattice k := by
  ext i
  simp only [CompactForceDecay.integerShift_apply, PeriodicLocalization.lattice_apply]

/-- Every lattice copy of the distinguished origin has the same zero jets. -/
@[simp] theorem boundaryLimits_lattice (A : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (k : PeriodicLocalization.Lattice) (n : ℕ) :
    boundaryLimits A p eA ep (PeriodicLocalization.lattice k) n = 0 := by
  rw [← integerShift_eq_lattice]
  simp only [boundaryLimits, representative_integerShift, JointResidualLimits.boundaryLimits_zero]

theorem boundaryLimits_independent {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA eA' : JointResidualLimits.AwayExtensions A)
    (ep ep' : JointResidualLimits.AwayExtensions p) :
    boundaryLimits A p eA ep = boundaryLimits A p eA' ep' := by
  funext x n
  let := JointResidualLimits.past_filter_neBot x
  exact tendsto_nhds_unique (boundaryLimits_joint hz eA ep n x)
    (boundaryLimits_joint hz eA' ep' n x)

theorem boundaryLimits_add_integerShift {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (k : Fin 3 → ℤ) (n : ℕ) (x : Space) :
    boundaryLimits A p eA ep (x + CompactForceDecay.integerShift k) n =
      boundaryLimits A p eA ep x n := by
  let y := x + CompactForceDecay.integerShift k
  let := JointResidualLimits.past_filter_neBot y
  have hshift : Tendsto (fun z : SpaceTime => (z.1, z.2 - CompactForceDecay.integerShift k))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, y)) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) := by
    simpa only [y, add_sub_cancel_right] using
      spatial_sub_tendsto_past (CompactForceDecay.integerShift k) y
  have ht := (boundaryLimits_joint hz eA ep n x).comp hshift
  have hty : Tendsto (iteratedFDeriv ℝ n (periodicResidual A p))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, y)) (𝓝 (boundaryLimits A p eA ep x n)) := by
    apply ht.congr'
    filter_upwards [] with z
    exact periodicResidual_jet_sub_integerShift A p n k z.1 z.2
  exact tendsto_nhds_unique (boundaryLimits_joint hz eA ep n y) hty

theorem periodicResidual_smooth {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1)) :
    ContDiffOn ℝ ∞ (periodicResidual A p) (SpacetimeEndpoint.openPast 1) :=
  ResidualRegularity.contDiffOn_residual (SpacetimeEndpoint.openPast_isOpen 1)
    (SpatialLocalization.periodicVelocity_smoothOn hA)
    (SpatialLocalization.periodicPressure_smoothOn hp)

theorem boundaryLimits_smooth {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => boundaryLimits A p eA ep x n) :=
  SpacetimeEndpoint.boundary_tensors_contDiff (J := ftaylorSeries ℝ (periodicResidual A p))
    (JointResidualLimits.actual_derivative_recurrence (periodicResidual_smooth hA hp))
    (boundaryLimits_locallyUniform hz eA ep) n

theorem extendedJets_compatible {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ)
    (z : SpaceTime) (h : z ∈ SpacetimeEndpoint.closedPast 1) :
    HasFDerivWithinAt
      (fun y => SpacetimeEndpoint.extendJets 1 (ftaylorSeries ℝ (periodicResidual A p))
        (boundaryLimits A p eA ep) y n)
      (SpacetimeEndpoint.extendJets 1 (ftaylorSeries ℝ (periodicResidual A p))
        (boundaryLimits A p eA ep) z (n + 1)).curryLeft (SpacetimeEndpoint.closedPast 1) z :=
  SpacetimeEndpoint.extendedJets_hasFDerivWithinAt
    (J := ftaylorSeries ℝ (periodicResidual A p))
    (JointResidualLimits.actual_derivative_recurrence (periodicResidual_smooth hA hp))
    (boundaryLimits_locallyUniform hz eA ep) n z h

theorem boundaryLimits_hasFDerivAt {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) (x : Space) :
    HasFDerivAt (fun y => boundaryLimits A p eA ep y n)
      ((boundaryLimits A p eA ep x (n + 1)).curryLeft.comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
  have hd := extendedJets_compatible hA hp hz eA ep n (1, x) ⟨le_refl (1 : ℝ), mem_univ x⟩
  have hi : HasFDerivAt (fun y : Space => ((1 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x :=
    (hasFDerivAt_const (1 : ℝ) x).prodMk (hasFDerivAt_id x)
  have hc := hd.comp x (hi.hasFDerivWithinAt (s := univ))
    (fun y _ => show ((1 : ℝ), y) ∈ SpacetimeEndpoint.closedPast 1 from
      ⟨le_refl (1 : ℝ), mem_univ y⟩)
  simpa only [Function.comp_def, SpacetimeEndpoint.extendJets, SpacetimeEndpoint.extendTrace_at]
    using hc.hasFDerivAt_of_univ

/-- Fill the terminal trace with the derived tensors. Only relative
smoothness on the closed past is asserted for this auxiliary extension. -/
noncomputable def extendedResidual (A : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) : VelocityField :=
  SpacetimeEndpoint.extendTrace 1 (periodicResidual A p)
    (fun x => (boundaryLimits A p eA ep x 0).curry0)

theorem extendedResidual_agrees (A : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) :
    EqOn (extendedResidual A p eA ep) (periodicResidual A p) (SpacetimeEndpoint.openPast 1) :=
  fun _ hz => SpacetimeEndpoint.extendTrace_of_lt hz.1

theorem extendedResidual_smooth {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) :
    ContDiffOn ℝ ∞ (extendedResidual A p eA ep) (SpacetimeEndpoint.closedPast 1) :=
  SpacetimeEndpoint.contDiffOn_joint_extension (J := ftaylorSeries ℝ (periodicResidual A p))
    (fun _ _ => rfl)
    (JointResidualLimits.actual_derivative_recurrence (periodicResidual_smooth hA hp))
    (boundaryLimits_locallyUniform hz eA ep)

theorem extendedResidual_boundary_jets {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ n (extendedResidual A p eA ep)
      (SpacetimeEndpoint.closedPast 1) (1, x) = boundaryLimits A p eA ep x n :=
  SpacetimeEndpoint.boundary_jets_eq_limits (J := ftaylorSeries ℝ (periodicResidual A p))
    (fun _ _ => rfl)
    (JointResidualLimits.actual_derivative_recurrence (periodicResidual_smooth hA hp))
    (boundaryLimits_locallyUniform hz eA ep) n x

/-- Time activation preserves these same limits at every spatial point. -/
theorem localizedResidual_joint {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) (x : Space) :
    Tendsto (iteratedFDeriv ℝ n
      (fun z => navierStokesResidual (SpatialLocalization.localizedVelocity A)
        (SpatialLocalization.localizedPressure p) z.1 z.2))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 (boundaryLimits A p eA ep x n)) := by
  apply (boundaryLimits_joint hz eA ep n x).congr'
  have he := ResidualRegularity.residual_eventuallyEq
    (TimeLocalization.activatedVelocity_eventuallyEq_late
      (SpatialLocalization.periodicVelocity A) (by norm_num : (3 : ℝ) / 4 < 1) x)
    (TimeLocalization.activatedPressure_eventuallyEq_late
      (SpatialLocalization.periodicPressure p) (by norm_num : (3 : ℝ) / 4 < 1) x)
  exact ((SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he n).filter_mono
    nhdsWithin_le_nhds).symm

theorem localizedResidual_locallyUniform {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    TendstoLocallyUniformly
      (fun t x => iteratedFDeriv ℝ n
        (fun z => navierStokesResidual (SpatialLocalization.localizedVelocity A)
          (SpatialLocalization.localizedPressure p) z.1 z.2) (t, x))
      (fun x => boundaryLimits A p eA ep x n) (𝓝[<] (1 : ℝ)) := by
  apply JointResidualLimits.locallyUniform_of_joint_limits
  intro x
  simpa only [JointResidualLimits.past_filter] using localizedResidual_joint hz eA ep n x

/-- The entire family required by `CandidateFromLimits` is now derived
from the original input fields and their local analytic data. -/
theorem exists_residual_limits {A : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p) :
    ∃ L : Space → FormalMultilinearSeries ℝ SpaceTime Space,
      (∀ k : PeriodicLocalization.Lattice, ∀ n : ℕ, L (PeriodicLocalization.lattice k) n = 0) ∧
      (∀ n : ℕ, TendstoLocallyUniformly
        (fun t x => iteratedFDeriv ℝ n (periodicResidual A p) (t, x))
        (fun x => L x n) (𝓝[<] (1 : ℝ))) :=
  ⟨boundaryLimits A p eA ep, boundaryLimits_lattice A p eA ep,
    boundaryLimits_locallyUniform hz eA ep⟩

/-! ## Direct candidate bridge with only original local analytic inputs -/

theorem periodicVelocity_speed_unbounded {A : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖)
      (𝓝[<] 1) atTop) : SpeedUnboundedAtOne (SpatialLocalization.periodicVelocity A) :=
  (TimeLocalization.activatedVelocity_speed_unbounded_iff
    (SpatialLocalization.periodicVelocity A)).mp
      (SpatialLocalization.localizedVelocity_speed_unbounded A haxis)

/-- A conditional candidate for the actual localized fields. No periodic
residual estimates, force, boundary tensors, or divergence assumption are inputs.
The potential extension input is essential and is not inferred from velocity regularity. -/
theorem exists_candidate_force {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖)
      (𝓝[<] 1) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (SpatialLocalization.localizedVelocity A)
        (SpatialLocalization.localizedPressure p) F ∧
      ContDiff ℝ ∞ F ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) = boundaryLimits A p eA ep x n) := by
  have hu : ContDiffOn ℝ ∞ (SpatialLocalization.periodicVelocity A) preSingularDomain :=
    SpatialLocalization.periodicVelocity_smoothOn
      (hA.mono (fun _ hz => ⟨hz.1.2, hz.2⟩))
  have hpc : ContDiffOn ℝ ∞ (SpatialLocalization.periodicPressure p) preSingularDomain :=
    SpatialLocalization.periodicPressure_smoothOn
      (hp.mono (fun _ hz => ⟨hz.1.2, hz.2⟩))
  let L := boundaryLimits A p eA ep
  have hlim := boundaryLimits_locallyUniform hz eA ep
  refine ⟨CandidateFromLimits.force _ _ hu hpc L hlim, ?_,
    CandidateFromLimits.force_smooth _ _ hu hpc L hlim,
    CandidateFromLimits.force_boundary_jets _ _ hu hpc L hlim⟩
  apply CandidateFromLimits.candidate_properties _ _ hu hpc L hlim
    (SpatialLocalization.periodicVelocity_periodic A _)
    (SpatialLocalization.periodicPressure_periodic p _) ?_
    (periodicVelocity_speed_unbounded haxis)
  intro t ht x
  exact SpatialLocalization.periodicVelocity_divergence_free hA ht.2 x

theorem candidateStatement_of_potential_data {A : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖)
      (𝓝[<] 1) atTop) : candidateStatement := by
  obtain ⟨F, hF, _⟩ := exists_candidate_force hA hp hz eA ep haxis
  exact ⟨SpatialLocalization.localizedVelocity A, SpatialLocalization.localizedPressure p, F, hF⟩

end NavierStokes.PeriodicResidualLimits
