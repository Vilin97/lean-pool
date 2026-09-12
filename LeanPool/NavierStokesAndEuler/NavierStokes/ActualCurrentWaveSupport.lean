/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ValidDyadicBandCover
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage

/-!
# Support of the actual current-band waves

The refined source carrier contains the fixed profile annulus.  Its strict
exterior supplies zero germs of the literal current-band Volterra outputs.
The physical support argument uses the continuous Cartesian radius divided
by the square root of the physical similarity scale.  In particular, it
does not differentiate a polar chart at the axis or use an excluded dyadic
face of a fixed reference formula.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCurrentWaveSupport

open Set Function Filter ProblemStatement CorrectionInitialization
open scoped Topology BigOperators


/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

/-- The profile radius in physical coordinates, independent of the valid
dyadic chart used to evaluate a wave. -/
noncomputable def profileRadius (h : ℝ) (w : SpaceTime) : ℝ :=
  AnnularEndpoint.radius w / Real.sqrt (PhysicalWaveSum.physicalQ h w)

theorem profileRadius_continuousAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : ContinuousAt (profileRadius h) w :=
  AnnularEndpoint.radius_continuous.continuousAt.div
    (Real.continuous_sqrt.continuousAt.comp
      (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt)
    (Real.sqrt_pos.mpr (PhysicalWaveSum.physicalQ_pos hh hh1 ht)).ne'

theorem profileRadius_zero_of_axis (h : ℝ) {w : SpaceTime}
    (ha : PhysicalGraphBounds.radialProjection w = 0) : profileRadius h w = 0 := by
  simp [profileRadius, AnnularEndpoint.radius, ha, PolarCharts.radius]

theorem profileRadius_sq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) :
    profileRadius h w ^ 2 / 2 = (SlowBorelBase.cartesianChart h w).2.1 := by
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  unfold profileRadius
  rw [div_pow, Real.sq_sqrt hq.le]
  change PolarCharts.radius (PhysicalGraphBounds.radialProjection w) ^ 2 /
    PhysicalWaveSum.physicalQ h w / 2 =
      ((w.2 0 ^ 2 + w.2 1 ^ 2) / 2) / PhysicalWaveSum.physicalQ h w
  rw [PolarCharts.radius_sq]
  change (w.2 0 ^ 2 + w.2 1 ^ 2) / PhysicalWaveSum.physicalQ h w / 2 = _
  ring

/-- The sharp profile-radius support is exactly the nominal active
annulus in the physical similarity variable `X`. -/
theorem profileRadius_mem_iff_active {w : SpaceTime} (ht : w.1 < 1) :
    profileRadius ActualPrimary.h w ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ↔
    (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∈
      Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
  have hsq := profileRadius_sq ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half ht
  have hr : 0 ≤ profileRadius ActualPrimary.h w :=
    div_nonneg (AnnularEndpoint.radius_nonneg w) (Real.sqrt_nonneg _)
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hasq : PrimaryTargetBounds.leftRadius ActualPrimary.nominal ^ 2 =
      2 * NominalConeAssembly.activeLeft ActualPrimary.nominal :=
    Real.sq_sqrt (mul_nonneg (by norm_num)
      (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal).le)
  have hbsq : PrimaryTargetBounds.rightRadius ActualPrimary.nominal ^ 2 =
      2 * NominalConeAssembly.activeRight ActualPrimary.nominal :=
    Real.sq_sqrt (mul_nonneg (by norm_num)
      (LeadingStressWeights.activeRight_pos ActualPrimary.nominal).le)
  constructor
  · intro hs
    have hl := (sq_le_sq₀ ha.le hr).mpr hs.1
    have hu := (sq_le_sq₀ hr hb.le).mpr hs.2
    constructor <;> linarith
  · intro hs
    constructor
    · apply (sq_le_sq₀ ha.le hr).mp
      linarith [hs.1]
    · apply (sq_le_sq₀ hr hb.le).mp
      linarith [hs.2]

/-- The normalized radius of the actual scaled graph agrees with the
band-independent physical ratio, also at the axis. -/
theorem graph_profileRadius_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (ht : w.1 < 1) :
    (PhysicalMeanJetBounds.graph h n d w).1 /
      VariableGaugeMean.qLength (2 * h) (PhysicalMeanJetBounds.graph h n d w).2.1 =
        profileRadius h w := by
  have hleft := ActualPolarCoverage.graph_profileRadius_sq hh hh1 n d ht
  have hright := profileRadius_sq hh hh1 ht
  have hl : 0 ≤ (PhysicalMeanJetBounds.graph h n d w).1 /
      VariableGaugeMean.qLength (2 * h) (PhysicalMeanJetBounds.graph h n d w).2.1 :=
    div_nonneg (ActualPolarCoverage.graph_radius_nonneg h n d w)
      (PhysicalMeanJetBounds.graph_length_pos hh hh1 n d ht).le
  have hr : 0 ≤ profileRadius h w :=
    div_nonneg (AnnularEndpoint.radius_nonneg w) (Real.sqrt_nonneg _)
  nlinarith

section BandSupport

variable {E : Type*} [NormedAddCommGroup E]

/-- A support assertion only on the open validity region of each band.
It makes no assertion about the totalized formula at an excluded face. -/
def BandAnnulus (h a b : ℝ) (N : ℕ) (f : ℕ → SpaceTime → E) : Prop :=
  ∀ n, N ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n, f n w ≠ 0 →
    profileRadius h w ∈ Icc a b

theorem BandAnnulus.zero_of_exterior {h a b : ℝ} {N n : ℕ}
    {f : ℕ → SpaceTime → E} (hs : BandAnnulus h a b N f) (hn : N ≤ n)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hr : profileRadius h w ∉ Icc a b) : f n w = 0 := by
  by_contra hf
  exact hr (hs n hn w hw hf)

theorem BandAnnulus.zero_germ {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N n : ℕ} {f : ℕ → SpaceTime → E} (hs : BandAnnulus h a b N f)
    (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hr : profileRadius h w ∉ Icc a b) : f n =ᶠ[𝓝 w] fun _ => 0 := by
  have hc := profileRadius_continuousAt hh hh1 hw.1
  filter_upwards [(ValidDyadicBandCover.band_open hh hh1 n).mem_nhds hw,
    hc (isClosed_Icc.isOpen_compl.mem_nhds hr)] with y hy hyr
  exact hs.zero_of_exterior hn hy hyr

theorem BandAnnulus.axis_zero_germ {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) {N n : ℕ} {f : ℕ → SpaceTime → E}
    (hs : BandAnnulus h a b N f) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    f n =ᶠ[𝓝 w] fun _ => 0 := by
  apply hs.zero_germ hh hh1 hn hw
  rw [profileRadius_zero_of_axis h haxis]
  exact fun hc => (not_le_of_gt ha) hc.1

theorem BandAnnulus.map_zero {F : Type*} [NormedAddCommGroup F]
    {h a b : ℝ} {N : ℕ} {f : ℕ → SpaceTime → E}
    (hs : BandAnnulus h a b N f) (T : ℕ → SpaceTime → E → F)
    (hT : ∀ n w, T n w 0 = 0) :
    BandAnnulus h a b N (fun n w => T n w (f n w)) := by
  intro n hn w hw hne
  apply hs n hn w hw
  intro hz
  exact hne (by change T n w (f n w) = 0; rw [hz, hT])

theorem BandAnnulus.add {h a b : ℝ} {N : ℕ} {f g : ℕ → SpaceTime → E}
    (hf : BandAnnulus h a b N f) (hg : BandAnnulus h a b N g) :
    BandAnnulus h a b N (fun n w => f n w + g n w) := by
  intro n hn w hw hne
  by_cases hz : f n w = 0
  · apply hg n hn w hw
    intro hgz
    exact hne (by change f n w + g n w = 0; rw [hz, hgz, add_zero])
  · exact hf n hn w hw hz

theorem BandAnnulus.finset_sum {ι : Type*} {h a b : ℝ} {N : ℕ}
    {f : ι → ℕ → SpaceTime → E} (s : ℕ → Finset ι)
    (hs : ∀ i, BandAnnulus h a b N (f i)) :
    BandAnnulus h a b N (fun n w => ∑ i ∈ s n, f i n w) := by
  intro n hn w hw hne
  by_contra hr
  apply hne
  apply Finset.sum_eq_zero
  intro i _hi
  exact (hs i).zero_of_exterior hn hw hr

theorem BandAnnulus.field_zero_germ {h a b qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {N : ℕ} {f : ℕ → SpaceTime → E}
    (hs : BandAnnulus h a b N f) (hf : ValidDyadicBandCover.Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N) {w : SpaceTime}
    (hw : w ∈ CutStageEstimates.physicalSublevel h qbig)
    (hr : profileRadius h w ∉ Icc a b) :
    ValidDyadicBandCover.field h N f =ᶠ[𝓝 w] fun _ => 0 :=
  ValidDyadicBandCover.field_zero_germ hh hh1 hf hqbig hw
    (fun _n hn hband => hs.zero_germ hh hh1 hn hband hr)

theorem BandAnnulus.field_support {h a b qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {N : ℕ} {f : ℕ → SpaceTime → E}
    (hs : BandAnnulus h a b N f) (hf : ValidDyadicBandCover.Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h b qbig
      (ValidDyadicBandCover.field h N f) := by
  intro w ht hq hne
  obtain ⟨n, hn, hband, _⟩ := ValidDyadicBandCover.exists_band hh hh1 N ht
    (hq.le.trans hqbig)
  have hfn : f n w ≠ 0 := by
    rwa [ValidDyadicBandCover.field_eq hf hn hband] at hne
  have hr := (hs n hn w hband hfn).2
  exact (div_le_iff₀ (Real.sqrt_pos.mpr
    (PhysicalWaveSum.physicalQ_pos hh hh1 ht))).mp hr

end BandSupport

theorem BandAnnulus.field_axisZeroOn {h a b qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) {N : ℕ}
    {f : ℕ → VelocityField} (hs : BandAnnulus h a b N f)
    (hf : ValidDyadicBandCover.Compatible h N f) (hqbig : qbig ≤ ChartScales.Q N) :
    GermCandidateAssembly.AxisZeroOn (MixedAxisPreservation.localDomain h qbig)
      (ValidDyadicBandCover.field h N f) := by
  intro w hw haxis
  apply hs.field_zero_germ hh hh1 hf hqbig hw
  rw [profileRadius_zero_of_axis h haxis]
  exact fun hc => (not_le_of_gt ha) hc.1

/-- The common outer constant used by the actual physical stage assembly
is larger than the fixed profile outer radius. -/
theorem rightRadius_le_actualOuterConstant :
    PrimaryTargetBounds.rightRadius ActualPrimary.nominal ≤
      PhysicalStageSupport.actualOuterConstant := by
  rw [PhysicalStageSupport.actualOuterConstant_eq]
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hs : 1 ≤ Real.sqrt 2 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  nlinarith

section RefinedExterior

variable {B N0 : ℕ}

theorem not_mem_refinedCarrier_of_radius (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1)
    (hr : ActualCoreSupport.radialRatio x ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    x ∉ ActualCoreSupport.refinedCarrier l n :=
  fun hx => hr ((ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hx).2.1

/-- Strict radial exterior of the actual refined input carrier.  All
outputs are the same current-band copy solve used by the iteration. -/
theorem particular_radial_zero_germs
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (b : CorrectionState.HarmonicBlock Point) (G A : HarmonicResidual.BlockCoefficients Point)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier l) b G A)
    (j : ℤ) (s : WeightedClasses.StripData
      ((CorrectionStep.CycleSlow × ℝ) × TorusInverse.Plane)) (n : ℕ)
    {z : (CorrectionStep.CycleSlow × ℝ) × TorusInverse.Plane}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hr : ActualCoreSupport.radialRatio
      (ActualCarrierTransport.associatedPoint z.1.1 z.2) ∉
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
    let a := p.copyData (StateReindex.context CorrectionStep.cycleAssoc.symm c)
      (StateReindex.state CorrectionStep.cycleAssoc.symm u)
      (StateReindex.block CorrectionStep.cycleAssoc.symm b)
      (StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm G)
      (StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm A) j
    (a.common.amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    ((a.commonCorrected s p.directions).amplitude n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) ∧
    (a.globalGaussian p.directions n =ᶠ[𝓝 z] fun _ => 0) :=
  ActualCycleAssembly.refined_particular_zero_germs hN l c u b G A hs j s n hz
    (not_mem_refinedCarrier_of_radius l n (show 0 < z.1.1.2.1 from hz.1) hr)

end RefinedExterior

section CurrentCoordinates

theorem nativePoint_radius (n : ℕ) (w : SpaceTime) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 =
      (ChartScales.Q n) ^ (-(1 / 2 : ℝ)) * AnnularEndpoint.radius w := by
  simp only [ActualCurrentParticularPhysical.nativePoint, PhysicalParticularWave.nativeMap,
    PhysicalParticularWave.waveEquiv_apply, PhysicalResidualBridge.ScaledGraph.map,
    ActualCurrentParticularPhysical.cylinderPoint, AxisymmetricResidual.pack_zero,
    PhysicalResidualBridge.commonGraph, AnnularEndpoint.radius]

theorem nativePoint_slow (n : ℕ) (w : SpaceTime) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 =
      ((1 - w.1) / ChartScales.Q n,
        (ChartScales.Q n) ^ (-CoordinateAlgebra.D ActualPrimary.h) * w.2 2) := by
  simp only [ActualCurrentParticularPhysical.nativePoint, PhysicalParticularWave.nativeMap,
    PhysicalParticularWave.waveEquiv_apply, PhysicalResidualBridge.ScaledGraph.map,
    ActualCurrentParticularPhysical.cylinderPoint, AxisymmetricResidual.pack_two]
  change
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
        (CommonWindow.index ActualPrimary.h n)).velocityScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
        (CommonWindow.index ActualPrimary.h n)).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
        (CommonWindow.index ActualPrimary.h n)).epsilon * (1 - w.1),
     (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
        (CommonWindow.index ActualPrimary.h n)).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h
        (CommonWindow.index ActualPrimary.h n)).epsilon * w.2 2) = _
  rw [PhysicalResidualBridge.commonGraph_slowTimeScale (ChartScales.Q_pos n),
    PhysicalResidualBridge.commonGraph_axialScale (ChartScales.Q_pos n)]
  simp only [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

theorem nativePoint_slow_eq_graph (n : ℕ) (w : SpaceTime) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 =
      (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).2.1 := by
  rw [nativePoint_slow, PhysicalMeanJetBounds.graph_slow]

theorem nativePoint_coordinateQ (n : ℕ) {w : SpaceTime} (ht : w.1 < 1) :
    SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 =
        PhysicalWaveSum.physicalQ ActualPrimary.h w / ChartScales.Q n := by
  rw [nativePoint_slow_eq_graph]
  exact PhysicalMeanJetBounds.graph_q_eq ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 ht

theorem nativePoint_parameterDomain (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1 ∈
      ActualCarrierTransport.parameterDomain := by
  change 0 < (ActualCurrentParticularPhysical.nativePoint n w).1.1.2.1 ∧
    SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 ∈ Ioo (1 / 2 : ℝ) 2
  refine ⟨?_, ?_⟩
  · rw [nativePoint_slow]
    exact div_pos (sub_pos.mpr hw.1) (ChartScales.Q_pos n)
  · rw [nativePoint_coordinateQ n hw.1]
    exact (ValidDyadicBandCover.mem_band_iff.mp hw).2

theorem nativePoint_radius_eq_graph (n : ℕ) (w : SpaceTime) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 =
      (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 := by
  rw [nativePoint_radius, PhysicalMeanJetBounds.graph_radius]
  exact (PhysicalMeanJetBounds.cartesianRadius_smul
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (-(1 / 2 : ℝ))).le
    (PhysicalGraphBounds.radialProjection w)).symm

theorem nativePoint_profileRadius (n : ℕ) {w : SpaceTime} (ht : w.1 < 1) :
    ActualCoreSupport.radialRatio
      (ActualCarrierTransport.associatedPoint
        (ActualCurrentParticularPhysical.nativePoint n w).1.1
        (ActualCurrentParticularPhysical.nativePoint n w).2) =
      profileRadius ActualPrimary.h w := by
  change (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 /
    VariableGaugeMean.qLength (2 * ActualPrimary.h)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 = _
  rw [nativePoint_radius_eq_graph, nativePoint_slow_eq_graph]
  exact graph_profileRadius_eq ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 ht

end CurrentCoordinates

section CurrentFields

variable {B N0 : ℕ}

theorem current_raw_pressure_zero_germs
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {z : ActualCurrentParticularPhysical.Native}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hr : ActualCoreSupport.radialRatio
      (ActualCarrierTransport.associatedPoint z.1.1 z.2) ∉
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    ((ActualCurrentParticularPhysical.copyData x l j).common.amplitude n =ᶠ[𝓝 z]
      fun _ => 0) ∧
    ((ActualCurrentParticularPhysical.copyData x l j).common.pressure n =ᶠ[𝓝 z]
      fun _ => 0) := by
  have hz' := particular_radial_zero_germs hN (l.2,l.1) (ActualPrimary.commonContext B)
    x.state (x.coefficients.blocks l) (x.coefficients.gaussian l)
    (x.coefficients.aliasCoefficients l) hs j
    (CorrectionStep.ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
    n hz hr
  exact ⟨hz'.1, hz'.2.2.1⟩

theorem current_raw_pressure_annulus
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {z : ActualCurrentParticularPhysical.Native}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain) :
    ((ActualCurrentParticularPhysical.copyData x l j).common.amplitude n z ≠ 0 →
      ActualCoreSupport.radialRatio (ActualCarrierTransport.associatedPoint z.1.1 z.2) ∈
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) ∧
    ((ActualCurrentParticularPhysical.copyData x l j).common.pressure n z ≠ 0 →
      ActualCoreSupport.radialRatio (ActualCarrierTransport.associatedPoint z.1.1 z.2) ∈
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) := by
  constructor
  · intro hne
    by_contra hr
    exact hne (current_raw_pressure_zero_germs hN x l hs j n hz hr).1.eq_of_nhds
  · intro hne
    by_contra hr
    exact hne (current_raw_pressure_zero_germs hN x l hs j n hz hr).2.eq_of_nhds

theorem current_native_zero_germs
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {z : ActualCurrentParticularPhysical.Native}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hr : ActualCoreSupport.radialRatio
      (ActualCarrierTransport.associatedPoint z.1.1 z.2) ∉
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (ActualCurrentParticularPhysical.nativePotential x l j n =ᶠ[𝓝 z] fun _ => 0) ∧
    (ActualCurrentParticularPhysical.nativePressure x l j n =ᶠ[𝓝 z] fun _ => 0) := by
  obtain ⟨ha, hp⟩ := current_raw_pressure_zero_germs hN x l hs j n hz hr
  constructor
  · filter_upwards [ha] with y hy
    rw [ActualCurrentParticularPhysical.nativePotential_eq]
    ext i
    simp [CurlClassBounds.vectorPotential, HarmonicCalculus.vectorMode,
      CurlClassBounds.coefficient, CurlClassBounds.normalCoefficient,
      CurlClassBounds.normalCross, HarmonicCalculus.mode, hy]
  · filter_upwards [hp] with y hy
    simp [ActualCurrentParticularPhysical.nativePressure, HarmonicCalculus.mode, hy]

/-- The full refined carrier is retained, including its original slow
mask and native dyadic cutoff, rather than just its radial projection. -/
theorem current_native_zero_germs_off_carrier
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {z : ActualCurrentParticularPhysical.Native}
    (hz : z.1.1 ∈ ActualCarrierTransport.parameterDomain)
    (hn : ActualCarrierTransport.associatedPoint z.1.1 z.2 ∉
      ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    (ActualCurrentParticularPhysical.nativePotential x l j n =ᶠ[𝓝 z] fun _ => 0) ∧
    (ActualCurrentParticularPhysical.nativePressure x l j n =ᶠ[𝓝 z] fun _ => 0) := by
  have hg := ActualCycleAssembly.refined_particular_zero_germs hN (l.2,l.1)
    (ActualPrimary.commonContext B) x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) hs j
    (CorrectionStep.ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
    n hz hn
  have ha : (ActualCurrentParticularPhysical.copyData x l j).common.amplitude n =ᶠ[𝓝 z]
      fun _ => 0 := hg.1
  have hp : (ActualCurrentParticularPhysical.copyData x l j).common.pressure n =ᶠ[𝓝 z]
      fun _ => 0 := hg.2.2.1
  constructor
  · filter_upwards [ha] with y hy
    rw [ActualCurrentParticularPhysical.nativePotential_eq]
    ext i
    simp [CurlClassBounds.vectorPotential, HarmonicCalculus.vectorMode,
      CurlClassBounds.coefficient, CurlClassBounds.normalCoefficient,
      CurlClassBounds.normalCross, HarmonicCalculus.mode, hy]
  · filter_upwards [hp] with y hy
    simp [ActualCurrentParticularPhysical.nativePressure, HarmonicCalculus.mode, hy]

theorem modes_zero_of_native
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0) (j : ℤ) (n : ℕ) (w : SpaceTime)
    (ha : ActualCurrentParticularPhysical.nativePotential x l j n
      (ActualCurrentParticularPhysical.nativePoint n w) = 0)
    (hp : ActualCurrentParticularPhysical.nativePressure x l j n
      (ActualCurrentParticularPhysical.nativePoint n w) = 0) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n w = 0 ∧
      ActualCurrentParticularPhysical.localPressureMode x l j n w = 0 := by
  constructor
  · rw [ActualCurrentParticularPhysical.localPotentialMode_eq, ha]
    ext i
    fin_cases i <;> simp [PhysicalCurlCovariance.realVector, AxisymmetricResidual.pack]
  · change (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
      (ActualCurrentParticularPhysical.nativePressure x l j n
        (ActualCurrentParticularPhysical.nativePoint n w)).re = 0
    rw [hp]
    simp

theorem current_modes_zero_off_carrier
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hn : ActualCarrierTransport.associatedPoint
      (ActualCurrentParticularPhysical.nativePoint n w).1.1
      (ActualCurrentParticularPhysical.nativePoint n w).2 ∉
        ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n w = 0 ∧
      ActualCurrentParticularPhysical.localPressureMode x l j n w = 0 := by
  have hg := current_native_zero_germs_off_carrier hN x l hs j n
    (nativePoint_parameterDomain n hw) hn
  exact modes_zero_of_native x l j n w hg.1.eq_of_nhds hg.2.eq_of_nhds

theorem current_modes_support
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n) :
    (ActualCurrentParticularPhysical.localPotentialMode x l j n w ≠ 0 →
      ActualCarrierTransport.associatedPoint
        (ActualCurrentParticularPhysical.nativePoint n w).1.1
        (ActualCurrentParticularPhysical.nativePoint n w).2 ∈
          ActualCoreSupport.refinedCarrier (l.2,l.1) n) ∧
    (ActualCurrentParticularPhysical.localPressureMode x l j n w ≠ 0 →
      ActualCarrierTransport.associatedPoint
        (ActualCurrentParticularPhysical.nativePoint n w).1.1
        (ActualCurrentParticularPhysical.nativePoint n w).2 ∈
          ActualCoreSupport.refinedCarrier (l.2,l.1) n) := by
  constructor
  · intro hne
    by_contra hn
    exact hne (current_modes_zero_off_carrier hN x l hs j n hw hn).1
  · intro hne
    by_contra hn
    exact hne (current_modes_zero_off_carrier hN x l hs j n hw hn).2

/-- Pointwise zero passes through the actual normal coefficient, phase,
Cartesian frame rotation and physical scaling.  No continuity of a chosen
polar angle is needed here. -/
theorem current_modes_zero
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hr : profileRadius ActualPrimary.h w ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n w = 0 ∧
      ActualCurrentParticularPhysical.localPressureMode x l j n w = 0 := by
  have hr' : ActualCoreSupport.radialRatio
      (ActualCarrierTransport.associatedPoint
        (ActualCurrentParticularPhysical.nativePoint n w).1.1
        (ActualCurrentParticularPhysical.nativePoint n w).2) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
    rwa [nativePoint_profileRadius n hw.1]
  obtain ⟨ha, hp⟩ := current_native_zero_germs hN x l hs j n
    (nativePoint_parameterDomain n hw) hr'
  exact modes_zero_of_native x l j n w ha.eq_of_nhds hp.eq_of_nhds

theorem current_mode_annulus
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (l : ActualCurrentParticularPhysical.Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)) (j : ℤ) (N : ℕ) :
    BandAnnulus ActualPrimary.h (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) N
      (ActualCurrentParticularPhysical.localPotentialMode x l j) ∧
    BandAnnulus ActualPrimary.h (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) N
      (ActualCurrentParticularPhysical.localPressureMode x l j) := by
  constructor
  · intro n _hn w hw hne
    by_contra hr
    exact hne (current_modes_zero hN x l hs j n hw hr).1
  · intro n _hn w hw hne
    by_contra hr
    exact hne (current_modes_zero hN x l hs j n hw hr).2

/-- Every actual finite label and harmonic sum retains the same sharp
annulus; this statement has no copy-count or mode-count factor. -/
theorem current_annulus
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)) (N : ℕ) :
    BandAnnulus ActualPrimary.h (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) N
      (ActualCurrentParticularPhysical.localPotential x) ∧
    BandAnnulus ActualPrimary.h (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) N
      (ActualCurrentParticularPhysical.localPressure x) := by
  constructor
  · exact BandAnnulus.finset_sum x.coefficients.labels (fun l =>
      BandAnnulus.finset_sum (fun _ => ParticularWaveAssembly.modes x.coefficients.residualBand)
        (fun j => (current_mode_annulus hN x l (hs l) j N).1))
  · exact BandAnnulus.finset_sum x.coefficients.labels (fun l =>
      BandAnnulus.finset_sum (fun _ => ParticularWaveAssembly.modes x.coefficients.residualBand)
        (fun j => (current_mode_annulus hN x l (hs l) j N).2))

theorem current_local_active_zero
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hX : (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∉
      Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    ActualCurrentParticularPhysical.localPotential x n w = 0 ∧
      ActualCurrentParticularPhysical.localPressure x n w = 0 := by
  have hr : profileRadius ActualPrimary.h w ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) :=
    fun hp => hX ((profileRadius_mem_iff_active hw.1).mp hp)
  have hh := current_annulus hN x hs 0
  exact ⟨hh.1.zero_of_exterior (Nat.zero_le n) hw hr,
    hh.2.zero_of_exterior (Nat.zero_le n) hw hr⟩

theorem current_local_axis_germs
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    (ActualCurrentParticularPhysical.localPotential x n =ᶠ[𝓝 w] fun _ => 0) ∧
      (ActualCurrentParticularPhysical.localPressure x n =ᶠ[𝓝 w] fun _ => 0) := by
  have hh := current_annulus hN x hs 0
  exact ⟨hh.1.axis_zero_germ ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos
          ActualPrimary.nominal)
      (Nat.zero_le n) hw haxis,
    hh.2.axis_zero_germ ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos
          ActualPrimary.nominal)
      (Nat.zero_le n) hw haxis⟩

section Glued

variable (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CorrectionStep.CycleState (ActualCurrentParticularPhysical.Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    {N : ℕ} {qbig : ℝ}
    (hA : ValidDyadicBandCover.Compatible ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPotential x))
    (hP : ValidDyadicBandCover.Compatible ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPressure x))
    (hqbig : qbig ≤ ChartScales.Q N)

include hN hs hA hP hqbig

/-- Sharp active-annulus zero germs of the actual representative.  These
are stronger than the common outer-support bound used at the terminal plane. -/
theorem current_field_active_germs {w : SpaceTime}
    (hw : w ∈ CutStageEstimates.physicalSublevel ActualPrimary.h qbig)
    (hX : (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∉
      Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    (ValidDyadicBandCover.field ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPotential x) =ᶠ[𝓝 w] fun _ => 0) ∧
    (ValidDyadicBandCover.field ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPressure x) =ᶠ[𝓝 w] fun _ => 0) := by
  have hr : profileRadius ActualPrimary.h w ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) :=
    fun hp => hX ((profileRadius_mem_iff_active hw.1).mp hp)
  have hh := current_annulus hN x hs N
  exact ⟨hh.1.field_zero_germ ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hA hqbig hw hr,
    hh.2.field_zero_germ ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hP hqbig hw hr⟩

theorem current_field_active_zero {w : SpaceTime}
    (hw : w ∈ CutStageEstimates.physicalSublevel ActualPrimary.h qbig)
    (hX : (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∉
      Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)) :
    ValidDyadicBandCover.field ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPotential x) w = 0 ∧
    ValidDyadicBandCover.field ActualPrimary.h N
      (ActualCurrentParticularPhysical.localPressure x) w = 0 := by
  have hh := current_field_active_germs hN x hs hA hP hqbig hw hX
  exact ⟨hh.1.eq_of_nhds, hh.2.eq_of_nhds⟩

theorem current_field_support :
    MixedDiagonalExtensions.SublevelShrinkingSupport ActualPrimary.h
      PhysicalStageSupport.actualOuterConstant qbig
      (ValidDyadicBandCover.field ActualPrimary.h N
        (ActualCurrentParticularPhysical.localPotential x)) ∧
    MixedDiagonalExtensions.SublevelShrinkingSupport ActualPrimary.h
      PhysicalStageSupport.actualOuterConstant qbig
      (ValidDyadicBandCover.field ActualPrimary.h N
        (ActualCurrentParticularPhysical.localPressure x)) := by
  have hh := current_annulus hN x hs N
  exact ⟨PhysicalStageSupport.support_mono
      (hh.1.field_support ActualPrimary.outgoing.data.h_pos
        ActualPrimary.outgoing.data.h_lt_half hA hqbig) rightRadius_le_actualOuterConstant,
    PhysicalStageSupport.support_mono
      (hh.2.field_support ActualPrimary.outgoing.data.h_pos
        ActualPrimary.outgoing.data.h_lt_half hP hqbig) rightRadius_le_actualOuterConstant⟩

omit hP in
theorem current_field_axisZeroOn :
    GermCandidateAssembly.AxisZeroOn (MixedAxisPreservation.localDomain ActualPrimary.h qbig)
      (ValidDyadicBandCover.field ActualPrimary.h N
        (ActualCurrentParticularPhysical.localPotential x)) :=
  (current_annulus hN x hs N).1.field_axisZeroOn ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    hA hqbig

end Glued

end CurrentFields

end NavierStokes.ActualCurrentWaveSupport
