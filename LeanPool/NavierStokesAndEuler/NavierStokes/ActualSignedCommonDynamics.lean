/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ClosedNativeWaveIdentities
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData

/-!
# Actual common signed-wave equations

The native closed-cell equations are joined through the literal common
copy construction. The complement is handled by actual input zero germs.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedCommonDynamics

open Set Function Filter WeightedClasses HarmonicCalculus CorrectionState CorrectionStep
open CorrectionInitialization ActualSignedStageControls
open ActualSignedOutputBounds (copies)
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {B N0 : ℕ}

theorem angular_direction (B : ℕ) : (directions B).angular = ((0 : Point), (1 : ℝ)) := rfl

/-- Slope, given by `((parameters l).angularFrequency n : ℝ) / (parameters l).base.frequency n`. -/
noncomputable def slope (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  ((parameters l).angularFrequency n : ℝ) / (parameters l).base.frequency n

theorem phase_smooth (l : SignedLabel B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((parameters l).base.phase n) fullStrip.domain :=
  ActualPrimaryCoherence.piece_phase_smooth ActualPrimaryBounds.region l.2 l.1 n

theorem frequency_ne (l : SignedLabel B N0) (n : ℕ) : (parameters l).base.frequency n ≠ 0 :=
  (ActualPrimary.chartCoefficients_frequency_pos l.2 l.1 n).ne'

theorem angular_ne (l : SignedLabel B N0) (n : ℕ) : (parameters l).angularFrequency n ≠ 0 :=
  PrimaryGeometryAssembly.angularMode_ne_zero ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

theorem frequency_slope (l : SignedLabel B N0) (n : ℕ) :
    (parameters l).base.frequency n * slope l n = ((parameters l).angularFrequency n : ℝ) :=
  mul_div_cancel₀ _ (frequency_ne l n)

theorem angularInputs (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (k : Frequency) :
    SignedWaveUpdate.AngularInputs fullStrip (directions B) (parameters l).base
      (matrix l k) (target l k) request (mask l k) (fundamental l k)
      (normalMotion l k) (action l k) (cutoff l k) (slope l) where
  radius := (ActualPrimary.chartCoefficients_angular l.2 l.1).radius
  radial_base := (ActualPrimary.chartCoefficients_angular l.2 l.1).radialBase
  frequency_base := (ActualPrimary.chartCoefficients_angular l.2 l.1).frequencyBase
  axial_base := (ActualPrimary.chartCoefficients_angular l.2 l.1).axialBase
  radial_profile := by
    change CopyAngularInvariance.Invariant ((0 : Point), 1)
      (fun x : FullPoint => (ActualPrimary.commonContext B).operators.radialProfile x.1)
    exact PrimaryResidualClass.invariant_fst _
  phase n := by
    rw [angular_direction]
    intro x t
    simp only [parameters, ActualPrimary.chartCoefficients, ActualPrimary.absolutePhase,
      Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, mul_one]
    unfold slope parameters ActualPrimary.chartCoefficients
    ring
  phase_smooth := phase_smooth l
  matrix n := by
      intro x t; simp only [angular_direction, ActualSignedStageControls.matrix, nativePoint_angle]
  primary_target n := by intro x t; simp only [angular_direction, target, nativePoint_angle]
  signed_target := hangle
  mask n := by intro x t; simp only [angular_direction, mask, nativePoint_angle]
  fundamental n := by intro x t; simp only [angular_direction, fundamental, nativePoint_angle]
  normal_motion n := by intro x t; simp only [angular_direction, normalMotion, nativePoint_angle]
  action n := by intro x t; simp only [angular_direction, action, nativePoint_angle]
  cutoff n := by intro x t; simp only [angular_direction, cutoff, nativePoint_angle]

theorem angularData (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ClosedNativeWaveIdentities.AngularData ((copies request l).raw k) fullStrip (directions B)
      (cutoff l k) n := by
  let h := angularInputs request hangle l k
  exact ⟨h.radius n, h.radial_base n, h.frequency_base n, h.axial_base n,
    h.radialField n, ⟨slope l n, h.phase n⟩, h.amplitude l.2 n, h.pressure l.2 n, h.cutoff n⟩

theorem geometry (n : ℕ) :
    CurlClassBounds.CylindricalGeometry fullStrip.domain (fun x : FullPoint => x.1.1)
      ((directions B).radialField n) (fun _ => (directions B).angular)
      ((directions B).axialField fullStrip n) :=
  LocalizedCurlRealization.geometry_restrict
    (ActualPrimaryCoherence.piece_geometry ActualPrimaryBounds.region B n)
    fullStrip.isOpen_domain (ActualPrimaryCoherence.piece_domain_positive
        ActualPrimaryBounds.region)

theorem geometryAt (n : ℕ) {x : FullPoint} (hx : x ∈ fullStrip.domain) :
    ClosedNativeWaveIdentities.GeometryAt (fun x : FullPoint => x.1.1)
      ((directions B).radialField n) (fun _ => (directions B).angular)
      ((directions B).axialField fullStrip n) x := by
  let h := geometry (B := B) n
  exact ⟨h.radius_smooth.contDiffAt (h.isOpen.mem_nhds hx), h.radius_ne x hx,
    h.radial_smooth.contDiffAt (h.isOpen.mem_nhds hx),
    h.angular_smooth.contDiffAt (h.isOpen.mem_nhds hx),
    h.axial_smooth.contDiffAt (h.isOpen.mem_nhds hx),
    h.radial_radius x hx, h.angular_radius x hx, h.axial_radius x hx,
    h.radial_angular x hx, h.radial_axial x hx, h.angular_axial x hx⟩

theorem rawJets {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    ClosedNativeWaveIdentities.RawJetsAt ((copies request l).raw k) fullStrip
      (directions B) (cutoff l k) n x := by
  have hb := ActualSignedOutputBounds.background_inputs (B := B) (N0 := N0) request
  have hs := ActualPrimaryDynamics.base_smooth l.2 l.1 n
    (ActualPrimaryCoherence.piece_domain_positive ActualPrimaryBounds.region hx)
  obtain ⟨ha, hp⟩ := raw_coefficients_jets hR
  refine ⟨hb.radial_profile.smooth n (l,k) x hx hc,
    (phase_smooth l n).contDiffAt (fullStrip.isOpen_domain.mem_nhds hx),
    contDiffAt_fst.fst, hs.1.differentiableAt (by simp), hs.2.1.differentiableAt (by simp),
    hs.2.2.differentiableAt (by simp), ha.smooth l n k x hx hc,
    (hp.smooth l n k x hx hc).differentiableAt (by simp), (cutoff_smooth l n k).contDiffAt,
    (geometry (B := B) n).radius_ne x hx, ?_⟩
  intro hz
  have hbound := (ActualSignedStageControls.normal_range (l := l) (n := n) (k := k) hx hc).1
  change (ActualPrimary.chartCoefficients l.2 l.1).normal fullStrip (directions B) n x = 0 at hz
  rw [hz, norm_zero] at hbound
  exact (not_le_of_gt (ActualPrimaryBounds.normalFloor_pos B N0)) hbound

theorem local_equation {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (hfrozen : SignedWaveUpdate.FrozenAlong (directions B).fast request)
    {l : SignedLabel B N0} {n : ℕ} {k : Frequency} {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ phaseCell l n k) :
    ((copies request l).corrected fullStrip (directions B) k).harmonicResidual fullStrip
        (directions B) n x +
      (fun j => (copies request l).source n x j * carrier ((parameters l).base.frequency n)
          ((parameters l).base.phase n) x) =
    (fun j => ((copies request l).localGood fullStrip (directions B) n k x j +
      (copies request l).localGaussian (directions B) n k x j) *
      carrier ((parameters l).base.frequency n) ((parameters l).base.phase n) x) :=
  (rawJets hR hx hc).cancellation (angularData request hangle l n k)
    ((geometry (B := B) n).radial_radius x hx) (copies request l).source
    (by simpa only [copies, PeriodizedSignedParameters.copyData, Pi.zero_apply, neg_zero] using
      raw_principal_zero hR hfrozen hx hc)

theorem common_equation {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (hfrozen : SignedWaveUpdate.FrozenAlong (directions B).fast request)
    (l : SignedLabel B N0) (n : ℕ) {x : FullPoint} (hx : x ∈ fullStrip.domain) :
    ((copies request l).commonCorrected fullStrip (directions B)).harmonicResidual fullStrip
        (directions B) n x =
      (fun j => ((copies request l).globalGood fullStrip (directions B) n x j +
        (copies request l).globalGaussian (directions B) n x j) *
        carrier ((parameters l).base.frequency n) ((parameters l).base.phase n) x) := by
  let a := copies request l
  have hzsource (m : ℕ) (y : FullPoint) : a.source m =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have he := a.common_cancellation (cells l) (cutoff_support l) fullStrip (directions B)
    (fun m k y hy _ => by
      rcases ActualWaveRegularityData.signed_phaseCell_or_zero l m k hy with hc | hcut | hmask
      · exact local_equation hR hangle hfrozen hy hc
      · have hz := a.localized_zero_germs hcut
        have hg : a.localGaussian (directions B) m k =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [a.localTail_zero_germ (directions B) hcut] with z hz
          rw [a.localGaussian_eq, hz]
          simp only [a, copies, PeriodizedSignedParameters.copyData, smul_zero, add_zero]
        exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2 hg (hzsource m y)
      · have hz := ActualSignedOutputBounds.localized_zero_of_mask request l hmask
        have hu : a.amplitude m k =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [hmask] with z hz
          exact (PeriodizedSignedParameters.raw_zero_of_mask (p := parameters l)
            (s := ActualPrimaryBounds.strip) request m k z hz).1
        exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2
          (a.localGaussian_zero_of_fields (directions B) hu (hzsource m y)) (hzsource m y)) n hx
  have hz : (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x)
      = 0 := by
    ext j
    exact zero_mul _
  simp only [hz, add_zero] at he
  exact he

theorem common_curl_and_divergence {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (l : SignedLabel B N0) (n : ℕ) {x : FullPoint} (hx : x ∈ fullStrip.domain) :
    (CurlClassBounds.cylindricalCurl ((parameters l).base.radius n)
      ((directions B).radialField n) (fun _ => (directions B).angular)
      ((directions B).axialField fullStrip n) ((copies request l).common.curlPotential fullStrip
          (directions B) n) x =
      vectorMode ((parameters l).base.frequency n) ((parameters l).base.phase n)
        (((copies request l).commonCorrected fullStrip (directions B)).amplitude n) x) ∧
    cylindricalDivergence ((parameters l).base.radius n) ((directions B).radialField n)
      (fun _ => (directions B).angular) ((directions B).axialField fullStrip n)
      (vectorMode ((parameters l).base.frequency n) ((parameters l).base.phase n)
        (((copies request l).commonCorrected fullStrip (directions B)).amplitude n)) x = 0 := by
  have hn m k y (hy : y ∈ fullStrip.domain) :
      (CurlClassBounds.cylindricalCurl ((parameters l).base.radius m)
        ((directions B).radialField m) (fun _ => (directions B).angular)
        ((directions B).axialField fullStrip m) (((copies request l).localized k).curlPotential
            fullStrip (directions B) m) y =
        vectorMode ((parameters l).base.frequency m) ((parameters l).base.phase m)
          (((copies request l).corrected fullStrip (directions B) k).amplitude m) y) ∧
      cylindricalDivergence ((parameters l).base.radius m) ((directions B).radialField m)
        (fun _ => (directions B).angular) ((directions B).axialField fullStrip m)
        (vectorMode ((parameters l).base.frequency m) ((parameters l).base.phase m)
          (((copies request l).corrected fullStrip (directions B) k).amplitude m)) y = 0 := by
    rcases ActualSignedOutputBounds.phaseCell_or_localized_zero request l m k hy with hc | hz
    · exact ⟨ClosedNativeWaveIdentities.native_realizes_curl_at m k y (rawJets hR hy hc)
          (frequency_ne l m) ((raw_tangent_germ request hy hc).self_of_nhds),
        ClosedNativeWaveIdentities.native_divergence_zero_at m k y (rawJets hR hy hc)
          (geometryAt (B := B) m hy) (frequency_ne l m) (raw_tangent_germ request hy hc)⟩
    · exact LocalizedCurlRealization.native_identities_of_zero_germ (copies request l) fullStrip
        (directions B) hz.1
  exact ⟨(copies request l).common_realizes_curl (cells l) (cutoff_support l) fullStrip (directions
      B)
      (fun m k y hy _ => (hn m k y hy).1) n hx,
    (copies request l).common_divergence_zero (cells l) (cutoff_support l) fullStrip (directions B)
      (fun m k y hy _ => (hn m k y hy).2) n hx⟩

theorem phase_split (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) (x : Point) (θ : ℝ) :
    (parameters l).base.frequency n * (parameters l).base.phase n (x,θ) =
      (parameters l).base.frequency n * (parameters l).base.phase n (x,0) +
        ((parameters l).angularFrequency n : ℝ) * θ := by
  rw [CopyAngularInvariance.affinePhase_eq_zeroSlice
    (Φ := (parameters l).base.phase n) (m := slope l n)
    (by simpa only [angular_direction] using (angularInputs request hangle l 0).phase n) x θ,
    mul_add, ← mul_assoc, frequency_slope]

theorem common_pressure_invariant (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : Point), 1) ((copies request l).common.pressure n) := by
  exact (copies request l).common_pressure_invariant _
    (fun n k => (angularInputs request hangle l k).cutoff n)
    (fun n k => (angularInputs request hangle l k).pressure l.2 n) n

theorem corrected_invariant (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : Point), 1)
      (((copies request l).commonCorrected fullStrip (directions B)).amplitude n) := by
  let h := angularInputs request hangle l 0
  exact (copies request l).commonCorrected_invariant fullStrip (directions B) _
    (fun n k => (angularInputs request hangle l k).cutoff n)
    (fun n k => (angularInputs request hangle l k).amplitude l.2 n) h.radius h.radialField
    (fun _ => CopyAngularInvariance.Invariant.const _) (fun n => ⟨slope l n, h.phase n⟩) n

theorem good_invariant (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : Point), 1)
      ((copies request l).globalGood fullStrip (directions B) n) := by
  let h := angularInputs request hangle l 0
  exact (copies request l).globalGood_invariant fullStrip (directions B)
    (fun n k => (angularInputs request hangle l k).cutoff n)
    (fun n k => (angularInputs request hangle l k).amplitude l.2 n)
    (fun n k => (angularInputs request hangle l k).pressure l.2 n)
    h.radius h.radial_base h.frequency_base h.axial_base h.radialField
    (fun _ => CopyAngularInvariance.Invariant.const _) (fun n => ⟨slope l n, h.phase n⟩) n

theorem gaussian_invariant (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : Point), 1) ((copies request l).globalGaussian (directions
        B) n) :=
  (copies request l).globalGaussian_invariant (directions B) _
    (fun n k => (angularInputs request hangle l k).cutoff n)
    (fun n k => (angularInputs request hangle l k).amplitude l.2 n)
    (fun _ => CopyAngularInvariance.Invariant.const _) n

theorem exact_represents (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) :
    let z := (copies request l).commonCorrected fullStrip (directions B)
    ((parameters l).exactBlock ActualPrimaryBounds.strip request).oscillation =
      (fun n x i => (vectorMode ((parameters l).base.frequency n) ((parameters l).base.phase n)
        (z.amplitude n) x i).re) ∧
    ((parameters l).exactBlock ActualPrimaryBounds.strip request).oscillatoryPressure =
      (fun n x => (mode ((parameters l).base.frequency n) ((parameters l).base.phase n)
        (z.pressure n) x).re) :=
  SignedWaveUpdate.blockOfCoefficients_represents _ (parameters l).angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice (corrected_invariant request hangle
        l n) x θ)
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice (common_pressure_invariant request
        hangle l n) x θ)
    (phase_split request hangle l)

theorem good_represents (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) :
    ((parameters l).goodBlock ActualPrimaryBounds.strip request).oscillation = fun n x i =>
      ((copies request l).globalGood fullStrip (directions B) n x i *
        carrier ((parameters l).base.frequency n) ((parameters l).base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients FullPoint :=
    {(parameters l).base with
      amplitude := (copies request l).globalGood fullStrip (directions B)
      pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z (parameters l).angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice (good_invariant request hangle l n)
        x θ)
    (fun _ _ _ => rfl) (phase_split request hangle l)).1

theorem gaussian_represents (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) :
    ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).oscillation = fun n x i =>
      ((copies request l).globalGaussian (directions B) n x i *
        carrier ((parameters l).base.frequency n) ((parameters l).base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients FullPoint :=
    {(parameters l).base with
      amplitude := (copies request l).globalGaussian (directions B)
      pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z (parameters l).angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice (gaussian_invariant request hangle l
        n) x θ)
    (fun _ _ _ => rfl) (phase_split request hangle l)).1

theorem frame_match (l : SignedLabel B N0) :
    WaveFrameMatch (ActualPrimary.commonContext B) fullStrip (directions B) (parameters l).base :=
        by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, rfl, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro n
    exact PrimaryResidualClass.directions_radial (ActualPrimary.commonContext B) n
  · intro n
    exact PrimaryResidualClass.directions_axial ActualPrimaryBounds.strip
        (ActualPrimary.commonContext B) rfl n
  · intro n
    exact PrimaryResidualClass.directions_time ActualPrimaryBounds.strip
        (ActualPrimary.commonContext B) rfl n

theorem context_radial_smooth (B n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame (ActualPrimary.commonContext B) n).radial
      ActualPrimaryBounds.strip.domain :=
  (HarmonicMeanInteraction.slowGeometry (ActualPrimary.commonContext B)
    (ActualInitialization.operators B) (ActualInitialization.radius_pos B)).radial_class.smooth n

theorem context_linear_identity {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (hfrozen : SignedWaveUpdate.FrozenAlong (directions B).fast request)
    (l : SignedLabel B N0) (a : HarmonicBlock Point)
    (hc : SameCarrier a ((parameters l).exactBlock ActualPrimaryBounds.strip request))
    (n : ℕ) (x : FullPoint) (hx : x.1 ∈ ActualPrimaryBounds.strip.domain) :
    linearBlockField (ActualPrimary.commonContext B) a
      ((parameters l).exactBlock ActualPrimaryBounds.strip request) n x =
        ((parameters l).goodBlock ActualPrimaryBounds.strip request).oscillation n x +
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).oscillation n x := by
  let z := (copies request l).commonCorrected fullStrip (directions B)
  have hb := ActualSignedOutputBounds.common_bounds hR
  have hphase := phase_smooth l n
  have hdom : fullStrip.domain = HarmonicResidual.liftDomain ActualPrimaryBounds.strip.domain :=
    productStrip_domain ActualPrimaryBounds.strip
  rw [hdom] at hphase
  have hv (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => z.amplitude n y i)
      (HarmonicResidual.liftDomain ActualPrimaryBounds.strip.domain) := by
    simpa only [hdom] using (CurlClassBounds.class_component (hb.corrected.each l) i).smooth n
  have hp : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain
      ActualPrimaryBounds.strip.domain) := by
    have hs := (hb.pressure.each l).smooth n
    simp only [hdom] at hs
    exact hs
  have hvrep : (HarmonicWaveInteraction.withCarrier a ((parameters l).exactBlock
      ActualPrimaryBounds.strip request)).oscillation n =
      fun y i => (vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i).re := by
    rw [withCarrier_of_same hc]
    exact congrFun (exact_represents request hangle l).1 n
  have hprep : (HarmonicWaveInteraction.withCarrier a ((parameters l).exactBlock
      ActualPrimaryBounds.strip request)).oscillatoryPressure n =
      fun y => (mode (z.frequency n) (z.phase n) (z.pressure n) y).re := by
    rw [withCarrier_of_same hc]
    exact congrFun (exact_represents request hangle l).2 n
  rw [linearBlockField_eq_modeResidual ActualPrimaryBounds.strip.isOpen_domain
    (ActualPrimary.commonContext B) a ((parameters l).exactBlock ActualPrimaryBounds.strip request)
    fullStrip (directions B) z ((parameters l).frame_common ActualPrimaryBounds.strip request
        (frame_match l))
    n (ActualInitialization.base_bounds B).smooth (ActualInitialization.radialDirection_smooth B n)
    (ActualInitialization.axialDirection_smooth B n) hphase hv hp hvrep hprep ⟨hx,trivial⟩]
  rw [good_represents request hangle l, gaussian_represents request hangle l]
  funext i
  have he := congrArg Complex.re (congrFun (common_equation hR hangle hfrozen l n hx) i)
  simpa only [add_mul, Complex.add_re, Pi.add_apply] using he

theorem full_divergence_zero {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) (n : ℕ) (x : FullPoint) (hx : x.1 ∈ ActualPrimaryBounds.strip.domain) :
    cylindricalDivergence (fun q => (ActualPrimary.commonContext B).operators.radius q.1)
      (radialDirection (ActualPrimary.commonContext B) n) angularDirection
      (axialDirection (ActualPrimary.commonContext B) n)
      (fun q i => (((parameters l).exactBlock ActualPrimaryBounds.strip request).oscillation n q i
          : ℂ)) x = 0 := by
  let z := (copies request l).commonCorrected fullStrip (directions B)
  have hb := ActualSignedOutputBounds.common_bounds hR
  have hdiff (i : Fin 3) : DifferentiableAt ℝ
      (fun y => vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i) x :=
    ((HarmonicCalculus.contDiffOn_mode (z.frequency n) (phase_smooth l n)
      ((CurlClassBounds.class_component (hb.corrected.each l) i).smooth n)).contDiffAt
        (fullStrip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hd := (common_curl_and_divergence hR l n hx).2
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have he := ParticularWaveAssembly.divergence_map L (z.radius n) ((directions B).radialField n)
    (fun _ => (directions B).angular) ((directions B).axialField fullStrip n) hdiff
  change cylindricalDivergence (z.radius n) ((directions B).radialField n)
    (fun _ => (directions B).angular) ((directions B).axialField fullStrip n)
      (vectorMode (z.frequency n) (z.phase n) (z.amplitude n)) x = 0 at hd
  rw [hd] at he
  have hθ : angularDirection (D := Point) = fun _ => (directions B).angular := rfl
  rw [(exact_represents request hangle l).1, ← (frame_match l).radius n,
    ← (frame_match l).radial n, ← (frame_match l).axial n, hθ]
  simp only [L, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.reCLM_apply, map_zero] at he
  exact he

theorem modeSolenoidal {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (l : SignedLabel B N0) :
    HarmonicWaveInteraction.ModeSolenoidal ActualPrimaryBounds.strip (ActualPrimary.commonContext B)
      ((parameters l).exactBlock ActualPrimaryBounds.strip request) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full
    (ActualPrimary.commonContext B) ((parameters l).exactBlock ActualPrimaryBounds.strip request)
  · intro n
    exact (phase_smooth l n).comp (SignedWaveUpdate.zeroSection (D := Point)).contDiff.contDiffOn
      (fun _ hx => hx)
  · exact angular_ne l
  · intro n i j
    exact (((ActualSignedOutputBounds.block_bounds hR).2.1 i j).each l).smooth n
  · exact full_divergence_zero hR hangle l

/-- The actual context-linear remainder is obtained from the common PDE
identity and the already proved native good-term estimates. -/
theorem linearGood_bounds {β : ℝ} {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) β (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q))
    (hangle : ∀ n, CopyAngularInvariance.Invariant ((0 : Point), 1) (request n))
    (hfrozen : SignedWaveUpdate.FrozenAlong (directions B).fast request)
    (a : SignedLabel B N0 → HarmonicBlock Point)
    (hc : ∀ l, SameCarrier (a l) ((parameters l).exactBlock ActualPrimaryBounds.strip request)) :
    UniformHarmonicInteraction.UniformVelocity ActualPrimaryBounds.strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) (β + 1 - 3 * ChartScales.kappa)
      (fun l => HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B)
        (a l) ((parameters l).exactBlock ActualPrimaryBounds.strip request)
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).velocity) := by
  let z : SignedLabel B N0 → HarmonicBlock Point := fun l =>
    ErrorHarmonics.zeroBlock (a l).frequency (a l).phase (a l).angularFrequency 0
  have hb := ActualSignedOutputBounds.block_bounds hR
  have hphase l n : ContDiffOn ℝ ∞ ((a l).phase n) ActualPrimaryBounds.strip.domain := by
    rw [← (hc l).phase]
    exact (phase_smooth l n).comp (SignedWaveUpdate.zeroSection (D := Point)).contDiff.contDiffOn
      (fun _ hx => hx)
  have hka l n : (a l).angularFrequency n ≠ 0 := by
    rw [← (hc l).angular]
    exact angular_ne l n
  have hgood : UniformHarmonicInteraction.UniformVelocity ActualPrimaryBounds.strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) (β + 1 - 3 * ChartScales.kappa)
      (fun l => (parameters l).goodBlock ActualPrimaryBounds.strip request) :=
    fun i j _ => hb.2.2.2.2 i j
  have he := linearGoodBlock_cancel_uniform (ActualPrimary.commonContext B) a
    (fun l => (parameters l).exactBlock ActualPrimaryBounds.strip request) z
    (fun l => (parameters l).goodBlock ActualPrimaryBounds.strip request)
    (fun l => ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).velocity)
    (context_radial_smooth B) (fun _ => contDiffOn_const) (ActualInitialization.base_bounds
        B).smooth
    (fun l n i j => ((hb.2.1 i j).each l).smooth n)
    (fun l n j => ((hb.2.2.1 j).each l).smooth n)
    hphase hka (fun l n i => ErrorHarmonics.zeroBlock_symmetric _ _ _ _ n i)
    (fun _ => (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1) hgood ?_
  · intro i j hj
    simpa [z, ErrorHarmonics.zeroBlock, HarmonicFields.constantCoefficient, Finsupp.single_apply,
      hj, Ne.symm hj] using he i j hj
  · intro l n x hx θ i
    have hgc : SameCarrier (a l) ((parameters l).goodBlock ActualPrimaryBounds.strip request) :=
      ⟨(hc l).frequency, (hc l).phase, (hc l).angular⟩
    have hec : SameCarrier (a l) ((parameters l).gaussianBlock ActualPrimaryBounds.strip request) :=
      ⟨(hc l).frequency, (hc l).phase, (hc l).angular⟩
    have hh := congrFun (context_linear_identity hR hangle hfrozen l (a l) (hc l) n (x,θ) hx) i
    rw [withCarrier_of_same hgc]
    have heval : (HarmonicFields.field
        (((parameters l).gaussianBlock ActualPrimaryBounds.strip request).velocity n i)
        ((a l).frequency n) ((a l).phase n) ((a l).angularFrequency n) (x,θ)).re =
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).oscillation n (x,θ) i := by
      simp only [HarmonicBlock.oscillation, hec.frequency, hec.phase, hec.angular]
    rw [heval]
    simp only [z, HarmonicWaveInteraction.withCarrier, ErrorHarmonics.zeroBlock,
      HarmonicBlock.oscillation, HarmonicResidual.field_constant, Pi.zero_apply, Pi.add_apply,
      Complex.ofReal_zero, Complex.zero_re, add_zero] at hh ⊢
    exact hh

theorem actual_request_jets (G : SignedMeanGain.Geometry) (hs : G.strip = ActualPrimaryBounds.strip)
    (u : State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b
        (ActualPrimary.commonContext B) u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass G.strip α (u.axialResidual (ActualPrimary.commonContext B))) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord
        (ActualPrimary.commonContext B) u n x q) := by
  have hr := fullRequest_jets_from_residuals G (ActualPrimary.commonContext B) u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  simp only [hs] at hr ⊢
  exact hr

/-- The exact signed harmonic block from the current residual is
solenoidal. No output divergence or global native-control record is used. -/
theorem actual_modeSolenoidal (G : SignedMeanGain.Geometry) (hs : G.strip =
    ActualPrimaryBounds.strip)
    (u : State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b
        (ActualPrimary.commonContext B) u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass G.strip α (u.axialResidual (ActualPrimary.commonContext B)))
    (l : SignedLabel B N0) :
    HarmonicWaveInteraction.ModeSolenoidal ActualPrimaryBounds.strip (ActualPrimary.commonContext B)
      ((parameters l).exactBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest G.strip G.patch G.coord (ActualPrimary.commonContext B) u))
            :=
  modeSolenoidal (actual_request_jets G hs u α H hfixed hθ hz)
    (LocalSignedRequest.fullRequest_angle_frozen G.strip G.patch G.coord
        (ActualPrimary.commonContext B) u) l

/-- The signed linear gain needed by the actual correction cycle.
Only the incoming residual bounds, reconstruction, and carrier match
are supplied. The Gaussian block is the literal computed one. -/
theorem actual_linearGood_bounds (G : SignedMeanGain.Geometry) (hs : G.strip =
    ActualPrimaryBounds.strip)
    (u : State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b
        (ActualPrimary.commonContext B) u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass G.strip α (u.axialResidual (ActualPrimary.commonContext B)))
    (a : SignedLabel B N0 → HarmonicBlock Point)
    (hc : ∀ l, SameCarrier (a l) ((parameters l).exactBlock ActualPrimaryBounds.strip
      (LocalSignedRequest.fullRequest G.strip G.patch G.coord (ActualPrimary.commonContext B) u))) :
    UniformHarmonicInteraction.UniformVelocity ActualPrimaryBounds.strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) (α - 3 * ChartScales.kappa)
      (fun l => HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B) (a l)
        ((parameters l).exactBlock ActualPrimaryBounds.strip
          (LocalSignedRequest.fullRequest G.strip G.patch G.coord (ActualPrimary.commonContext B)
              u))
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip
          (LocalSignedRequest.fullRequest G.strip G.patch G.coord (ActualPrimary.commonContext B)
              u)).velocity) := by
  simpa only [sub_add_cancel] using linearGood_bounds (actual_request_jets G hs u α H hfixed hθ hz)
    (LocalSignedRequest.fullRequest_angle_frozen G.strip G.patch G.coord
        (ActualPrimary.commonContext B) u)
    (request_frozen G.strip G.patch G.coord (ActualPrimary.commonContext B) u) a hc

end NavierStokes.ActualSignedCommonDynamics
