/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularMeanGain
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePeriodicity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularDynamics
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularGaussian

@[expose] public section

/-!
# Particular-wave data for the actual correction cycle

The record below names the particular half of the cycle's analytic data.
Its producer uses the literal fixed-parameter solve and incoming invariant.
-/

noncomputable section

namespace NavierStokes.ActualParticularCycleData

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open scoped ContDiff Topology BigOperators


abbrev Point := ActualInitialization.Point
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

noncomputable abbrev parameters (B N0 : ℕ) := ActualCycleParameters.fixedParameters B N0

noncomputable abbrev block {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (parameters B N0).particularBlock x.coefficients (ActualPrimary.commonContext B) x.state

noncomputable abbrev gaussianBlock {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (parameters B N0).particularGaussianBlock x.coefficients (ActualPrimary.commonContext B) x.state

abbrev Invariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop :=
  CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope
    ActualCoreSupport.refinedCarrier σ x

/-- The literal particular increment's analytic outputs. No signed-wave
estimate is required to prepare its mean and the subsequent signed request. -/
structure Data {B N0 : ℕ} (x : CycleState (Index B N0)) (σ : ℝ) : Prop where
  amplitude : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1/2+σ) (fun l n z => (block x l).velocity n i j z)
  pressure : ∀ j, LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1+σ) (fun l n z => (block x l).pressure n j z)
  coefficients : ∀ l n i, HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain
    ((block x l).velocity n i)
  pressureCoefficients : ∀ l n, HarmonicResidual.SmoothCoefficients
    ActualInitialization.geometry.domain
    ((block x l).pressure n)
  gaussianCoefficients : ∀ l n i, HarmonicResidual.SmoothCoefficients
    ActualInitialization.geometry.domain
    ((gaussianBlock x l).velocity n i)
  solenoidal : ∀ l, HarmonicWaveInteraction.ModeSolenoidal ActualInitialization.strip
    (ActualPrimary.commonContext B) (block x l)
  gaussian : ∀ β i j, LabelSumBounds.UniformClass ActualInitialization.strip
    (fun _ _ z => Real.sqrt (ActualInitialization.strip.zeta z)) β
    (fun l n z => (gaussianBlock x l).velocity n i j z)
  field : WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  pressureField : ∀ n, ContDiffOn ℝ ∞
    ((parameters B N0).particularPressure x.coefficients (ActualPrimary.commonContext B) x.state n)
    (ActualInitialization.geometry.domain ×ˢ (univ : Set ℝ))
  periodic : OscillationPeriodic ActualPrimary.standardRegion.carrier
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  support : WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b
    ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
  linear : ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1+σ-3*ChartScales.kappa)
    (fun l n z =>
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).velocity n i j z +
      (HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B)
        (x.coefficients.blocks l) (block x l) (gaussianBlock x l).velocity).velocity n i j z)

namespace Data

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

/-- The actual geometric support supplies the remaining first-wave mean
inputs; this does not use any signed increment. -/
theorem inputs (d : Data x σ) (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualParticularMeanGain.Inputs x σ where
  amplitude := d.amplitude
  smooth := d.field
  periodic := d.periodic
  supported := d.support
  old_support := ActualCycleAssembly.old_supported x H hN
    ActualCoreSupport.refinedCarrier_subset_broad
  particular_support := ActualCycleAssembly.particular_supported_of_inputSupport x hN
    (ActualCycleAssembly.cycle_particular_inputSupport hN x (ActualPrimary.commonContext B)
      (fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport l)
        (ActualCoreSupport.refinedCarrier_subset_broad l)))

end Data

section NativeData

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

noncomputable def nativeData (x : CycleState (Index B N0)) (l : Index B N0) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j

theorem preservesCarriers (H : Invariant σ x) :
    ActualParticularDynamics.PreservesCarriers (ActualCycleParameters.particularState x) :=
  fun l => H.carrier (l.2,l.1)

theorem native_inputSupport (H : Invariant σ x) :
    ActualParticularStageControls.InputSupport (ActualCycleParameters.particularState x) :=
  fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport (l.2,l.1))
    (ActualCoreSupport.refinedCarrier_subset_broad (l.2,l.1))

theorem nativeData_eq_data (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    nativeData x l j = ActualParticularStageControls.data
      (ActualCycleParameters.particularState x) (l.2,l.1) j := by
  unfold ActualParticularStageControls.data
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem native_phase (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    (nativeData x l j).background.phase =
      (ActualParticularStageControls.background (l.2,l.1)).phase := by
  rw [nativeData_eq_data H]
  exact ActualParticularDynamics.data_phase (preservesCarriers H) (l.2,l.1) j

theorem native_source_pull (l : Index B N0) (j : ℤ) (n : ℕ) :
    (nativeData x l j).source n = fun z =>
      ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
        j n (ActualCarrierTransport.associatedPoint z.1.1 z.2) :=
  ActualParticularStageControls.currentSource_pull (ActualCycleParameters.particularState x)
    (l.2,l.1) j n

theorem native_source_smooth (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).source n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) := by
  rw [native_source_pull]
  apply (ActualCycleCoherence.source_smooth H ActualCoreSupport.refinedCarrier_closed
    (fun l n _ hz hc => ActualCycleCoherence.core_radius_pos l n hz hc) l j n).comp
  · exact (show ContDiff ℝ ∞ (fun z : ActualParticularStageControls.Native =>
      ActualCarrierTransport.associatedPoint z.1.1 z.2) by
        exact cycleAssoc.symm.contDiff.comp
          (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn
  · intro z hz
    exact hz.1

theorem native_source_exterior (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).source n z = 0 := by
  rw [native_source_pull]
  apply (HarmonicSourceSupport.residualSource_zero_germ_on (ActualPrimary.commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    ActualInitialization.geometry.domain_open (ActualCoreSupport.refinedCarrier_closed l)
    (H.inputSupport l) j n hz.1 ?_).self_of_nhds
  intro hc
  exact hr ((ActualCoreSupport.mem_refinedCarrier_iff l n hz.1.1).mp hc).2.1

theorem native_inactive (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    (nativeData x l j).common.amplitude n =ᶠ[𝓝 z] fun _ => 0 := by
  exact (ActualCycleAssembly.refined_particular_zero_germs hN l (ActualPrimary.commonContext B)
    x.state (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients
      l)
    (H.inputSupport l) j ActualWaveRegularityData.particularFullStrip n hz.1
      (fun hc => hn (ActualCycleCoherence.core_ordered l n hz.1 hc))).1

theorem native_source_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).source n z = 0 :=
  ActualWaveRegularityData.particular_zero_on_radial_faces
    (native_source_smooth H l j n).continuousOn
    (fun _ hz hr => native_source_exterior H l j n hz hr) hz hr

theorem native_raw_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    (k : TorusInverse.Frequency) {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).amplitude n k z = 0 := by
  change ParticularWaveBounds.complexCopyVelocity
    (ParticularWaveAssembly.angleTangent ((ActualParticularStageControls.canonicalParameters
      (l.2,l.1)).tangent j n))
    ((nativeData x l j).source n) ((ActualParticularStageControls.canonicalParameters
      (l.2,l.1)).geometry n)
    ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).length_pos n).le k z = 0
  apply ParticularWaveBounds.complexCopyVelocity_zero_of_path
  intro v _hv
  exact native_source_boundary H l j n hz hr

theorem native_pressure_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    (k : TorusInverse.Frequency) {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).pressure n k z = 0 := by
  let t := ParticularWaveAssembly.angleTangent
    ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).tangent j n)
  let g := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).geometry n
  let L := (ActualParticularStageControls.canonicalParameters (l.2,l.1)).length n
  have hL : 0 ≤ L := ((ActualParticularStageControls.canonicalParameters (l.2,l.1)).length_pos n).le
  let f := (nativeData x l j).source n
  have hpath (v : ℝ) (_hv : v ∈ Icc 0 L) : f (z.1, g.path k z.2 v) = 0 :=
    native_source_boundary H l j n hz hr
  have hcurrent : f z = 0 := native_source_boundary H l j n hz hr
  change ParticularWaveBounds.complexCopyPressure t f g hL k
    ((nativeData x l j).background.frequency n) z = 0
  unfold ParticularWaveBounds.complexCopyPressure
  have hr0 := ParticularWaveBounds.copyPressure_zero_of_path (ParticularWaveBounds.realData t f)
    g hL k ((nativeData x l j).background.frequency n) z.1 z.2
    (fun v hv => by
      change ParticularWaveBounds.realPart (f (z.1,g.path k z.2 v)) = 0
      rw [hpath v hv, map_zero])
    (by change ParticularWaveBounds.realPart (f z) = 0; rw [hcurrent, map_zero])
  have hi0 := ParticularWaveBounds.copyPressure_zero_of_path (ParticularWaveBounds.imagData t f)
    g hL k ((nativeData x l j).background.frequency n) z.1 z.2
    (fun v hv => by
      change ParticularWaveBounds.imagPart (f (z.1,g.path k z.2 v)) = 0
      rw [hpath v hv, map_zero])
    (by change ParticularWaveBounds.imagPart (f z) = 0; rw [hcurrent, map_zero])
  rw [hr0, hi0, mul_zero, add_zero]

theorem native_common_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).common.amplitude n z = 0 ∧ (nativeData x l j).common.pressure n z = 0 := by
  constructor
  · change (∑' k, (nativeData x l j).cutoff n k z • (nativeData x l j).amplitude n k z) = 0
    simp only [native_raw_boundary H l j n _ hz hr, smul_zero, tsum_zero]
  · change (∑' k, ((nativeData x l j).cutoff n k z : ℂ) * (nativeData x l j).pressure n k z) = 0
    simp only [native_pressure_boundary H l j n _ hz hr, mul_zero, tsum_zero]

theorem native_gaussian_boundary (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (nativeData x l j).globalGaussian (ActualParticularStageControls.canonicalParameters
      (l.2,l.1)).directions n z = 0 := by
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, PeriodizedWaveBounds.CopyData.globalTail,
    PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail,
    native_raw_boundary H l j n _ hz hr, native_source_boundary H l j n hz hr,
    smul_zero, tsum_zero, add_zero]

theorem native_residual (H : Invariant σ x) :
    UniformHarmonicInteraction.UniformVelocity
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)
      ActualParticularStageControls.meanEnvelope (1/2+σ)
      (fun l => HarmonicResidual.residualBlock (ActualPrimary.commonContext B)
        (ActualCycleParameters.particularState x).state
        ((ActualCycleParameters.particularState x).coefficients.blocks l)
        ((ActualCycleParameters.particularState x).coefficients.gaussian l)
        ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l)) := by
  intro i j hj
  have hh := (H.residual i j hj).reindex
    (fun l : ActualParticularStageControls.Label B N0 => (l.2,l.1))
  refine ⟨?_, hh.smooth, ?_⟩
  · intro l n z hz
    simp only [ActualParticularStageControls.meanEnvelope_eq_primary]
    exact hh.weight_nonneg l n z hz
  · intro m
    obtain ⟨C,hC,p,hb⟩ := hh.bounds m
    refine ⟨C,hC,p,?_⟩
    intro l n z hz q hq
    have he := hb l n z hz q hq
    simp only [majorant, ActualParticularStageControls.meanEnvelope_eq_primary] at he ⊢
    exact he

theorem native_source_class (H : Invariant σ x) (j : ℤ) (hj : j ≠ 0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope (1/2+σ)
      (ActualParticularStageControls.currentSource (ActualCycleParameters.particularState x) j) :=
  ActualParticularStageControls.current_source_class _ (native_residual H) j hj

theorem native_envelope_le_one (l : Index B N0) (n : ℕ) (z : ActualParticularStageControls.Native) :
    ActualParticularStageControls.nativeEnvelope (l.2,l.1) n z ≤ 1 :=
  ActualPrimaryBounds.envelope_le_one (l.2,l.1) n (0,z.2)

theorem native_raw_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z))
      (1/2+σ) (nativeData x l j).common.amplitude := by
  have ha := (ActualParticularStageControls.common_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN j hj (native_source_class H j hj)).1.each (l.2,l.1)
  rw [← nativeData_eq_data H l j] at ha
  exact ha.mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    (fun n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (native_envelope_le_one l n z))

theorem native_pressure_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
  N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z))
      ((1/2+σ)+1/2) (nativeData x l j).common.pressure := by
  have hp := (ActualParticularStageControls.common_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN j hj (native_source_class H j hj)).2.2.1.each (l.2,l.1)
  rw [← nativeData_eq_data H l j] at hp
  exact hp.mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    (fun n z _ => mul_le_of_le_one_right (Real.sqrt_nonneg _) (native_envelope_le_one l n z))

theorem native_gaussian_class (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
  N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (β : ℝ) :
    MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) β
      ((nativeData x l j).globalGaussian (ActualParticularStageControls.canonicalParameters
        (l.2,l.1)).directions) := by
  have hg := (ActualParticularGaussian.globalGaussian_all_gains _
    (fun l => ActualCycleParameters.current_frequency x (l.2,l.1) (H.carrier (l.2,l.1)))
    (native_inputSupport H) hN j hj (native_source_class H j hj) β).each (l.2,l.1)
  rwa [← nativeData_eq_data H l j] at hg

theorem native_raw_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).common.amplitude n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1) n).1

theorem native_pressure_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
  N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).common.pressure n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_pressure_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).2) n).1

theorem native_gaussian_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤
  N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).globalGaussian
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :=
  (ActualWaveRegularityData.particular_full_regular_of_class (native_gaussian_class H hN l j hj 0)
    (fun n _ hz hr => native_gaussian_boundary H l j n hz hr) n).1

theorem native_corrected_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold
  ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (((nativeData x l j).commonCorrected ActualWaveRegularityData.particularFullStrip
      (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions).amplitude n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :=
  ActualWaveRegularityData.particular_corrected_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1) n

theorem source_inactive (H : Invariant σ x) (l : Index B N0) (n : ℕ)
    (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain) :
    ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j
        n z = 0 :=
  (HarmonicSourceSupport.residualSource_zero_germ_on (ActualPrimary.commonContext B) x.state
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    ActualInitialization.geometry.domain_open (ActualCoreSupport.refinedCarrier_closed l)
    (H.inputSupport l) j n hz (fun hc => hn (ActualCycleCoherence.core_ordered l n hz
      hc))).self_of_nhds

theorem native_source_periodic (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (l : Index B N0) (j : ℤ) (n : ℕ) (z : ActualParticularStageControls.Native)
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    CommonCoverSolve.PeriodicAt ((nativeData x l j).source n) z.1 :=
  ActualCyclePeriodicity.copies_source_periodic H T
    (fun l n hn j _ hz => source_inactive H l n hn j hz) l j n z hz

noncomputable def nativeMode (x : CycleState (Index B N0)) (l : Index B N0) (j : ℤ) :=
  ActualWaveRegularity.modeOscillation (nativeData x l j)
    ActualWaveRegularityData.particularFullStrip
    (ActualParticularStageControls.canonicalParameters (l.2,l.1)).directions
    ActualWaveRegularity.particularChart

theorem native_mode_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (j : ℤ) (hj : j ≠ 0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_raw_class H hN l j hj)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1)

theorem native_mode_support (H : Invariant σ x) (l : Index B N0) (j : ℤ) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_support (l.2,l.1) _ _ _ _ _ j
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).1)

theorem native_mode_periodic (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (j : ℤ) :
    OscillationPeriodic ActualPrimary.standardRegion.carrier (nativeMode x l j) :=
  ActualWaveRegularityData.particular_mode_periodic (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j) (native_source_periodic H T l j)
    (fun n hn _ hz => native_inactive H hN l n hn j hz)

theorem block_eq_modes (H : Invariant σ x) (l : Index B N0) :
    (block x l).oscillation = LabelSumBounds.fieldSum
      (fun _ => ParticularWaveAssembly.modes x.coefficients.residualBand) (nativeMode x l) :=
  ActualWaveRegularity.particularBlock_eq_modes (parameters B N0) x.coefficients
    (ActualPrimary.commonContext B) x.state l
    (fun n => (ActualParticularDynamics.native_angular (ActualCycleParameters.particularState x)
      (l.2,l.1) 1 n 0).radius)
    (fun n => (ActualParticularDynamics.native_angular (ActualCycleParameters.particularState x)
      (l.2,l.1) 1 n 0).radial_field)
    (H.frequency l)

theorem block_regular (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain (block x l).oscillation ∧
    OscillationPeriodic ActualPrimary.standardRegion.carrier (block x l).oscillation ∧
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (block x l).oscillation := by
  rw [block_eq_modes H l]
  exact ActualWaveRegularity.finset_regular _ _ (fun j hj =>
    ⟨native_mode_smooth H hN l j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1,
      native_mode_periodic H T hN l j, native_mode_support H l j⟩)

theorem field_regular (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
        ∧
    OscillationPeriodic ActualPrimary.standardRegion.carrier
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
        ∧
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      ((parameters B N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state)
        :=
  ⟨ActualWaveRegularity.finite_smooth _ _ (fun l => (block_regular H T hN l).1),
    ActualWaveRegularity.finite_periodic _ _ (fun l => (block_regular H T hN l).2.1),
    ActualWaveRegularity.finite_support _ _ (fun l => (block_regular H T hN l).2.2)⟩

end NativeData

section FiniteCoefficients

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem pair_smooth {U : Set D} {f : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (ErrorHarmonics.conjugatePair j f) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x => ErrorHarmonics.conjugatePair j f m x) U
  simp only [ParticularWaveAssembly.pair_apply]
  have hleft : ContDiffOn ℝ ∞ (fun x => if m = j then f x / 2 else 0) U := by
    split_ifs
    · exact hf.div_const _
    · exact contDiffOn_const
  have hright : ContDiffOn ℝ ∞ (fun x => if -m = j then f x / 2 else 0) U := by
    split_ifs
    · exact hf.div_const _
    · exact contDiffOn_const
  exact hleft.add (Complex.conjCLE.contDiff.comp_contDiffOn hright)

theorem assembled_velocity_smooth {U : Set D} (N : ℕ) (k : ℕ → ℝ)
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℤ → ℕ → D → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (hv : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n, ContDiffOn ℝ ∞ (v j n) U)
    (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients U
      ((ParticularWaveAssembly.assembledBlock N k Φ kp v p).velocity n i) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x =>
    (∑ j ∈ ParticularWaveAssembly.modes N, ErrorHarmonics.conjugatePair j (fun y => v j n y i)) m
      x) U
  have he : (fun x => (∑ j ∈ ParticularWaveAssembly.modes N,
      ErrorHarmonics.conjugatePair j (fun y => v j n y i)) m x) =
      (fun x => ∑ j ∈ ParticularWaveAssembly.modes N,
        ErrorHarmonics.conjugatePair j (fun y => v j n y i) m x) := by
    funext x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  rw [he]
  apply ContDiffOn.sum
  intro j hj
  exact pair_smooth (contDiffOn_pi.mp (hv j hj n) i) j m

theorem assembled_pressure_smooth {U : Set D} (N : ℕ) (k : ℕ → ℝ)
    (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℤ → ℕ → D → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → D → ℂ)
    (hp : ∀ j ∈ ParticularWaveAssembly.modes N, ∀ n, ContDiffOn ℝ ∞ (p j n) U)
    (n : ℕ) :
    HarmonicResidual.SmoothCoefficients U
      ((ParticularWaveAssembly.assembledBlock N k Φ kp v p).pressure n) := by
  intro m
  change ContDiffOn ℝ ∞ (fun x =>
    (∑ j ∈ ParticularWaveAssembly.modes N, ErrorHarmonics.conjugatePair j (p j n)) m x) U
  have he : (fun x => (∑ j ∈ ParticularWaveAssembly.modes N,
      ErrorHarmonics.conjugatePair j (p j n)) m x) =
      (fun x => ∑ j ∈ ParticularWaveAssembly.modes N,
        ErrorHarmonics.conjugatePair j (p j n) m x) := by
    funext x
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  rw [he]
  apply ContDiffOn.sum
  intro j hj
  exact pair_smooth (hp j hj n) j m

end FiniteCoefficients

section Outputs

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

noncomputable def associatedDomain : Set (CycleSlow × TorusInverse.Plane) :=
  ActualCarrierTransport.parameterDomain ×ˢ Set.univ

theorem native_slice_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ActualParticularStageControls.Native → E}
    (hf : ContDiffOn ℝ ∞ f (ActualWaveRegularity.nativeDomain
      ActualWaveRegularity.particularChart ActualPrimary.standardRegion)) :
    ContDiffOn ℝ ∞ (fun z => f (ParticularWaveAssembly.angleShuffle (z,0))) associatedDomain := by
  apply hf.comp
    (ParticularWaveAssembly.angleShuffle.contDiff.comp (contDiff_id.prodMk
      contDiff_const)).contDiffOn
  intro z hz
  exact ⟨hz.1, mem_univ _⟩

theorem coefficients_smooth (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain ((block x l).velocity
      n i) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
    (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.updateBlock ActualParticularStageControls.associatedStrip a.context a.state a.carrierBlock
        a.gaussianInput a.aliasInput x.coefficients.residualBand).velocity n i) := by
    apply assembled_velocity_smooth
    intro j hj m
    exact native_slice_smooth (native_corrected_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem pressure_coefficients_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain ((block x l).pressure
      n) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
    (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.updateBlock ActualParticularStageControls.associatedStrip a.context a.state a.carrierBlock
        a.gaussianInput a.aliasInput x.coefficients.residualBand).pressure n) := by
    apply assembled_pressure_smooth
    intro j hj m
    exact native_slice_smooth (native_pressure_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem gaussian_coefficients_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients ActualInitialization.geometry.domain
      ((gaussianBlock x l).velocity n i) := by
  let a := ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
    (l.2,l.1)
  let p := ActualParticularStageControls.canonicalParameters (l.2,l.1)
  have hh : HarmonicResidual.SmoothCoefficients associatedDomain
      ((p.gaussianBlock a.context a.state a.carrierBlock a.gaussianInput a.aliasInput
        x.coefficients.residualBand).velocity n i) := by
    apply assembled_velocity_smooth
    intro j hj m
    exact native_slice_smooth (native_gaussian_smooth H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 m)
  intro q
  exact (hh q).comp cycleAssoc.contDiff.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)

theorem block_eq_output (H : Invariant σ x) (l : Index B N0) :
    block x l = ActualParticularStageControls.outputBlock (ActualCycleParameters.particularState x)
      x.coefficients.residualBand (l.2,l.1) := by
  unfold ActualParticularStageControls.outputBlock ActualParticularStageControls.associatedUpdate
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

noncomputable def goodBlock (x : CycleState (Index B N0)) (l : Index B N0) :=
  ActualParticularStageControls.outputGood (ActualCycleParameters.particularState x)
    x.coefficients.residualBand (l.2,l.1)

theorem amplitude_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1/2+σ) (fun l n z => (block x l).velocity n i j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).1 i j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have ht : LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1/2+σ) (fun l n z => (ActualParticularStageControls.outputBlock
        (ActualCycleParameters.particularState x) x.coefficients.residualBand (l.2,l.1)).velocity n
          i j z) := by
    simp only [LabelSumBounds.UniformWaveClass,
      ActualParticularStageControls.meanEnvelope_eq_primary] at hh ⊢
    exact hh
  apply ht.congr
  intro l n z _
  exact congrArg (fun b : HarmonicBlock Point => b.velocity n i j z) (block_eq_output H l).symm

theorem pressure_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ) (fun l n z => (block x l).pressure n j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).2.1 j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have he : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  have ht : LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ) (fun l n z => (ActualParticularStageControls.outputBlock
        (ActualCycleParameters.particularState x) x.coefficients.residualBand (l.2,l.1)).pressure n
          j z) := by
    simp only [LabelSumBounds.UniformWaveClass,
      ActualParticularStageControls.meanEnvelope_eq_primary, he] at hh ⊢
    exact hh
  apply ht.congr
  intro l n z _
  exact congrArg (fun b : HarmonicBlock Point => b.pressure n j z) (block_eq_output H l).symm

theorem good_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass ActualInitialization.strip ActualInitialization.envelope
      (1+σ-3*ChartScales.kappa) (fun l n z => (goodBlock x l).velocity n i j z) := by
  have hh := ((ActualParticularStageControls.assembled_bounds _ (preservesCarriers H)
    (native_inputSupport H) hN (native_residual H) x.coefficients.residualBand).2.2 i j).reindex
    (fun l : Index B N0 => (l.2,l.1))
  have he : (1/2:ℝ)+σ+1/2 = 1+σ := by ring
  simp only [LabelSumBounds.UniformWaveClass,
    ActualParticularStageControls.meanEnvelope_eq_primary, he] at hh ⊢
  exact hh

theorem gaussian_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (β : ℝ) (i : Fin 3) (m : ℤ) :
    LabelSumBounds.UniformClass ActualInitialization.strip
      (fun _ _ z => Real.sqrt (ActualInitialization.strip.zeta z)) β
      (fun l n z => (gaussianBlock x l).velocity n i m z) := by
  have hg := ActualParticularGaussian.gaussianBlock_all_gains _
    (fun l => ActualCycleParameters.current_frequency x (l.2,l.1) (H.carrier (l.2,l.1)))
    (native_inputSupport H) hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1) β i m
  have hh := (MeanBoundsReindex.uniformClass_return (s := ActualInitialization.strip)
    (w := fun (_ : ActualParticularStageControls.Label B N0) _ z =>
      Real.sqrt (ActualInitialization.strip.zeta z)) cycleAssoc hg).reindex
    (fun l : Index B N0 => (l.2,l.1))
  apply hh.congr
  intro l n z _
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem solenoidal (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) : HarmonicWaveInteraction.ModeSolenoidal ActualInitialization.strip
      (ActualPrimary.commonContext B) (block x l) := by
  rw [block_eq_output H l]
  exact ActualParticularDynamics.cycle_modeSolenoidal (preservesCarriers H) (native_inputSupport H)
    hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1) (l.2,l.1)

theorem good_carrier (x : CycleState (Index B N0)) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l) (goodBlock x l) := ⟨rfl,rfl,rfl⟩

theorem good_real (x : CycleState (Index B N0)) (l : Index B N0) :
    ErrorHarmonics.RealBlock (goodBlock x l) := by
  constructor
  · intro n i j z
    exact (ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i j (cycleAssoc z)
  · intro n j z
    exact (ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2 n j (cycleAssoc z)

theorem gaussian_eq_cycle (H : Invariant σ x) (l : Index B N0) :
    gaussianBlock x l = StateReindex.block cycleAssoc
      (ActualParticularDynamics.actualGaussian (ActualCycleParameters.particularState x) (l.2,l.1)
        x.coefficients.residualBand) := by
  unfold ActualParticularDynamics.actualGaussian
  rw [ActualParticularStageControls.parameters_eq_canonical _ _
    (ActualCycleParameters.current_frequency x l (H.carrier l))]
  rfl

theorem field_cancellation (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0)
    (n : ℕ) (z : Point × ℝ) (hz : z.1 ∈ ActualInitialization.strip.domain) :
    linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l) (block x l) n z +
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).oscillation n z =
      (goodBlock x l).oscillation n z + (gaussianBlock x l).oscillation n z := by
  have hh := ActualParticularDynamics.cycle_context_linear_cancellation
    (preservesCarriers H) (native_inputSupport H) hN x.coefficients.residualBand
    (fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1)
    (l.2,l.1) (H.sourceBand l) n z hz
  change linearBlockField (ActualPrimary.commonContext B) (x.coefficients.blocks l)
      (ActualParticularStageControls.outputBlock (ActualCycleParameters.particularState x)
        x.coefficients.residualBand (l.2,l.1)) n z +
      (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l)).oscillation n z =
      (goodBlock x l).oscillation n z + (StateReindex.block cycleAssoc
        (ActualParticularDynamics.actualGaussian (ActualCycleParameters.particularState x) (l.2,l.1)
          x.coefficients.residualBand)).oscillation n z at hh
  rwa [← block_eq_output H l, ← gaussian_eq_cycle H l] at hh

theorem linear_bounds (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass ActualInitialization.strip
      ActualInitialization.envelope (1+σ-3*ChartScales.kappa)
      (fun l n z =>
        (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
          (x.coefficients.blocks l) (x.coefficients.gaussian l)
          (x.coefficients.aliasCoefficients l)).velocity n i j z +
        (HarmonicWaveInteraction.linearGoodBlock (ActualPrimary.commonContext B)
          (x.coefficients.blocks l) (block x l) (gaussianBlock x l).velocity).velocity n i j z) :=
            by
  apply linearGoodBlock_cancel_uniform (ActualPrimary.commonContext B) x.coefficients.blocks (block
    x)
    (fun l => HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (goodBlock x) (fun l => (gaussianBlock x l).velocity)
  · intro n
    exact contDiffOn_const.add ((contDiffOn_const.mul
      ((ActualInitialization.operators B).radialProfile.smooth 0)).smul contDiffOn_const)
  · intro n
    exact contDiffOn_const
  · exact (ActualInitialization.base_bounds B).smooth
  · intro l n i j
    exact (coefficients_smooth H hN l n i j).mono ActualInitialization.geometry.strip_subset
  · intro l n j
    exact (pressure_coefficients_smooth H hN l n j).mono ActualInitialization.geometry.strip_subset
  · exact H.phase
  · exact H.angular
  · intro l n i
    exact HarmonicResidual.residualBlock_conjugate _ _ _ _ _ n i
  · intro l n i
    exact (good_real x l).1 n i
  · intro i j _
    exact good_bounds H hN i j
  · intro l n z hz θ i
    have hs : SameCarrier (x.coefficients.blocks l)
        (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) x.state
          (x.coefficients.blocks l) (x.coefficients.gaussian l)
          (x.coefficients.aliasCoefficients l)) := ⟨rfl,rfl,rfl⟩
    rw [withCarrier_of_same hs, withCarrier_of_same (good_carrier x l)]
    change _ + _ = _ + (gaussianBlock x l).oscillation n (z,θ) i
    exact congrArg (fun f : Fin 3 → ℝ => f i) (field_cancellation H hN l n (z,θ) hz)

section PressureAssembly

open HarmonicCalculus LinearWaveBounds PeriodizedWaveBounds ParticularWaveAssembly
open ParticularWaveBounds CopyAngularInvariance ActualWaveRegularity

/-- Pressure is assembled from the same actual modes as velocity. -/
theorem particularBlock_pressure_eq_modes {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι)
    (hf : ∀ n, (v.blocks l).frequency n ≠ 0) :
    (p.particularBlock v c u l).oscillatoryPressure = fun n z =>
      ∑ j ∈ modes v.residualBand,
        (mode ((particularCopyData p v c u l j).background.frequency n)
          ((particularCopyData p v c u l j).background.phase n)
          ((particularCopyData p v c u l j).common.pressure n) (particularChart z)).re := by
  have ha (j : ℤ) (n : ℕ) :
      CopyAngularInvariance.Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
        ((particularCopyData p v c u l j).common.pressure n) := by
    apply CopyData.common_pressure_invariant
    · intro m k
      exact nativeCutoff_invariant ((0 : CycleSlow), (1 : ℝ)) _ _ k
    · intro m k
      exact complexCopyPressure_invariant (angleTangent_invariant _) (angleLift_invariant _)
        _ ((p.particular l).length_pos m).le k _
  funext n z
  unfold CycleParameters.particularBlock
  rw [StateReindex.block_pressure]
  change ((p.particular l).updateBlock _ _ _ _ _ _ _).oscillatoryPressure n
    (cycleAssoc z.1, z.2) = _
  rw [ParticularParameters.updateBlock, assembledBlock_pressure_value]
  apply Finset.sum_congr rfl
  intro j _hj
  have hi := invariant_angleShuffle (ha j n) (cycleAssoc z.1) z.2
  have hc := actualCarrier_character (p.particular l).background
    (StateReindex.block cycleAssoc.symm (v.blocks l)) j hf n (cycleAssoc z.1, z.2)
  change Complex.re (_ * _) = Complex.re
    (((particularCopyData p v c u l j).common.pressure n
      (angleShuffle (cycleAssoc z.1, z.2))) *
      carrier ((actualCarrier (p.particular l).background
        (StateReindex.block cycleAssoc.symm (v.blocks l)) j).frequency n)
        ((actualCarrier (p.particular l).background
          (StateReindex.block cycleAssoc.symm (v.blocks l)) j).phase n)
        (angleShuffle (cycleAssoc z.1, z.2)))
  rw [hc, hi]
  rfl

theorem pressure_field_smooth (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((parameters B N0).particularPressure x.coefficients
      (ActualPrimary.commonContext B) x.state n)
      (ActualInitialization.geometry.domain ×ˢ (univ : Set ℝ)) := by
  change ContDiffOn ℝ ∞ (fun z => ∑ l ∈ x.coefficients.labels n,
    (block x l).oscillatoryPressure n z) _
  apply ContDiffOn.sum
  intro l _hl
  change ContDiffOn ℝ ∞ (((parameters B N0).particularBlock x.coefficients
    (ActualPrimary.commonContext B) x.state l).oscillatoryPressure n) _
  rw [particularBlock_pressure_eq_modes _ _ _ _ _ (H.frequency l)]
  apply ContDiffOn.sum
  intro j hj
  exact ActualWaveRegularityData.particular_mode_pressure_smooth (l.2,l.1) _ _ _ _ _ j
    (native_phase H l j)
    (native_pressure_class H hN l j ((mem_modes _ _).mp hj).1)
    (fun n _ hz hr => (native_common_boundary H l j n hz hr).2) n

end PressureAssembly

/-- Every field is derived for the literal particular construction from
the incoming analytic invariant and its separately tracked periods. -/
theorem actual_data (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (_hσ : 1/5 ≤ σ) : Data x σ where
  amplitude := amplitude_bounds H hN
  pressure := pressure_bounds H hN
  coefficients := coefficients_smooth H hN
  pressureCoefficients := pressure_coefficients_smooth H hN
  gaussianCoefficients := gaussian_coefficients_smooth H hN
  solenoidal := solenoidal H hN
  gaussian := gaussian_bounds H hN
  field := (field_regular H T hN).1
  pressureField := pressure_field_smooth H hN
  periodic := (field_regular H T hN).2.1
  support := (field_regular H T hN).2.2
  linear := linear_bounds H hN

theorem actual_inputs (H : Invariant σ x) (T : ActualCyclePeriodicity.Periodic x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1/5 ≤ σ) :
    ActualParticularMeanGain.Inputs x σ :=
  (actual_data H T hN hσ).inputs H hN

end Outputs

end NavierStokes.ActualParticularCycleData
