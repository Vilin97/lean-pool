/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ValidDyadicBandCover
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularPotentialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentWaveSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePreservation
import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentParticularPhysicalCoherence

/-!
# The actual particular waves on valid physical charts

The physical representative uses only the literal current-band solve.
Its compatibility is obtained from the corresponding current-source
transport laws.  No value of a reference solve on an excluded face is
used to define the physical representative.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualValidBandWaves

open Set Filter Function ProblemStatement
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators


variable {B N0 : ℕ}

/-- The actual finite current-band potential, in the initializer's label order. -/
noncomputable def localPotential
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (n : ℕ) : VelocityField :=
  ActualCurrentParticularPhysical.localPotential (ActualCycleParameters.particularState x) n

/-- Local pressure, given by `ActualCurrentParticularPhysical.localPressure
(ActualCycleParameters.particularState x) n`. -/
noncomputable def localPressure
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (n : ℕ) : PressureField :=
  ActualCurrentParticularPhysical.localPressure (ActualCycleParameters.particularState x) n

/-- One representative of the actual current-band potential formulas. -/
noncomputable def potential
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (N : ℕ) : VelocityField :=
  ValidDyadicBandCover.field h N (localPotential x)

/-- Pressure, given by `ValidDyadicBandCover.field h N (localPressure x)`. -/
noncomputable def pressure
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (N : ℕ) : PressureField :=
  ValidDyadicBandCover.field h N (localPressure x)

/-- Glued potential: an abbreviation for `@potential`. -/
noncomputable abbrev gluedPotential := @potential
/-- Glued pressure: an abbreviation for `@pressure`. -/
noncomputable abbrev gluedPressure := @pressure

/-- The same physical polar angle is used in both bands.  The comparison
therefore retains the complete fast fiber instead of choosing new angles. -/
theorem nativePoint_bandMap (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    ActualParticularCoherence.bandMap n m (ActualCurrentParticularPhysical.nativePoint n w) =
      ActualCurrentParticularPhysical.nativePoint m w := by
  have hp : 0 < (ActualCurrentParticularPhysical.cylinderPoint w).2 0 := by
    simpa only [ActualCurrentParticularPhysical.cylinderPoint, AxisymmetricResidual.pack_zero]
        using hr
  unfold ActualCurrentParticularPhysical.nativePoint PhysicalParticularWave.nativeMap
  rw [ActualParticularCoherence.bandMap_apply n m k hi,
    ← PhysicalParticularWave.waveEquiv_cylinderChange]
  congr 1
  simpa only [hi] using PhysicalParticularWave.cylinderChange_graph
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) h (CommonWindow.index h n) k hp

theorem nativePoint_parameterChange (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q m)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1 =
      (ActualCurrentParticularPhysical.nativePoint m w).1.1 := by
  have he := nativePoint_bandMap n m k hi w hr
  rw [ActualParticularCoherence.bandMap_apply n m k hi] at he
  exact congrArg (fun z : PhysicalParticularWave.WaveSpace => z.1.1) he

theorem nativePoint_slowChange (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    GaugeStateCoherence.bandSlowEquiv h n m
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 =
      (ActualCurrentParticularPhysical.nativePoint m w).1.1.2 := by
  have hs : (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q m)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1).2 =
      GaugeStateCoherence.bandSlowEquiv h n m
        (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 :=
    congrArg (fun z : CorrectionStep.CyclePoint => z.2.1)
      (ActualReferenceRebase.associatedChart_stateChart n m 0
        ((ActualCurrentParticularPhysical.nativePoint n w).1.1, 0))
  exact hs.symm.trans (congrArg Prod.snd (nativePoint_parameterChange n m k hi w hr))

theorem nativePoint_overlap (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 ∈
      ActualInitialCoherence.overlap n m := by
  refine ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hn, ?_⟩
  change GaugeStateCoherence.bandSlowEquiv h n m
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 ∈ standardRegion.carrier
  rw [nativePoint_slowChange n m k hi w hr]
  exact ActualCurrentWaveSupport.nativePoint_parameterDomain m hm

private theorem sum_eq_of_agree_and_zero {ι E : Type*} [AddCommMonoid E]
    (s t : Finset ι) (f g : ι → E) (he : ∀ i, f i = g i)
    (hf : ∀ i, i ∉ s → f i = 0) (hg : ∀ i, i ∉ t → g i = 0) :
    ∑ i ∈ s, f i = ∑ i ∈ t, g i := by
  classical
  calc
    ∑ i ∈ s, f i = ∑ i ∈ s ∪ t, f i :=
      Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
    _ = ∑ i ∈ s ∪ t, g i := Finset.sum_congr rfl (fun i _ => he i)
    _ = ∑ i ∈ t, g i :=
      (Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg i hi)).symm

section Incoming

variable {σ : ℝ} {x : CorrectionStep.CycleState (ActualInitialization.Index B N0)}
    {S : ActualInitialization.Index B N0 → ℕ → Set LocalSignedRequest.Point}
    (H : CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (C : ActualCycleCoherence.Coherent x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)

include H

theorem current_frequency (l : ActualParticularStageControls.Label B N0) (n : ℕ) :
    ((ActualCycleParameters.particularState x).coefficients.blocks l).frequency n =
      ChartScales.carrier h n :=
  ActualCycleParameters.current_frequency x (l.2, l.1) (H.carrier (l.2, l.1)) n

include hcore in
theorem refined_support (l : ActualParticularStageControls.Label B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1))
      ((ActualCycleParameters.particularState x).coefficients.blocks l)
      ((ActualCycleParameters.particularState x).coefficients.gaussian l)
      ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l) :=
  ActualCycleAssembly.inputSupport_mono (H.inputSupport (l.2, l.1)) (hcore (l.2, l.1))

theorem nativePotential_eq_actual (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePotential (ActualCycleParameters.particularState x) l j n
        =
      ActualParticularPotentialCoherence.potential (ActualCycleParameters.particularState x) l j n
          := by
  rw [ActualParticularPotentialCoherence.potential_eq_copyData]
  unfold ActualCurrentParticularPhysical.nativePotential
  rw [ActualCurrentParticularPhysical.copyData_eq_actual _ _ _ (current_frequency H l)]

theorem nativePressure_eq_actual (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePressure (ActualCycleParameters.particularState x) l j n =
      ActualParticularPotentialCoherence.pressureMode (ActualCycleParameters.particularState x) l j
          n := by
  rw [ActualParticularPotentialCoherence.pressureMode_eq_copyData]
  unfold ActualCurrentParticularPhysical.nativePressure
  rw [ActualCurrentParticularPhysical.copyData_eq_actual _ _ _ (current_frequency H l)]

include C hN hcore in
theorem modes_zero_of_inactive (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hl : l ∉ (ActualCycleParameters.particularState x).coefficients.labels n) :
    ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState x) l
        j n w = 0 ∧
      ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x) l
          j n w = 0 := by
  apply ActualCurrentWaveSupport.current_modes_zero_off_carrier hN
    (ActualCycleParameters.particularState x) l (refined_support H hcore l) j n hw
  intro hc
  have ha := ActualCyclePreservation.core_active (l.2, l.1) n
    (ActualCurrentWaveSupport.nativePoint_parameterDomain n hw) hc
  have hb : (l.2, l.1) ∈ x.coefficients.labels n := by rwa [C.labels]
  exact hl ((ActualCycleParameters.particularState_mem x n (l.2, l.1)).mpr hb)

include C hS hcore in
theorem modes_eq_ordered (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (hj : j ≠ 0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState x) l
        j n w =
        ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState
            x) l j m w ∧
      ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x) l
          j n w =
        ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x)
            l j m w := by
  have hs := ActualCycleCoherence.particular_source_inputs H hS hcore l
  have ht : ∀ s ∈ ActualInitialCoherence.overlap n m, 0 < s.1 :=
    fun s hs => standardRegion.time_pos s hs.1
  have hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m)
      (ActualInitialCoherence.overlap n m) standardRegion.carrier := fun _ hs => hs.2
  have hz := nativePoint_overlap n m k hi hn hm hr
  have ha := ActualParticularPotentialCoherence.potential_band
    (ActualCycleParameters.particularState x) l hs (current_frequency H l)
    (ActualInitialCoherence.overlap_open n m) ht n m k hi hmap
    (C.reference_state n m k hi) (C.reference_block l n m k hi)
    j hj (ActualCurrentParticularPhysical.nativePoint n w) hz
  have hp := ActualParticularPotentialCoherence.pressureMode_band
    (ActualCycleParameters.particularState x) l hs (current_frequency H l)
    (ActualInitialCoherence.overlap_open n m) ht n m k hi hmap
    (C.reference_state n m k hi) (C.reference_block l n m k hi)
    j hj (ActualCurrentParticularPhysical.nativePoint n w) hz
  rw [nativePoint_bandMap n m k hi w hr, ← nativePotential_eq_actual H l j n,
    ← nativePotential_eq_actual H l j m] at ha
  rw [nativePoint_bandMap n m k hi w hr, ← nativePressure_eq_actual H l j n,
    ← nativePressure_eq_actual H l j m] at hp
  exact ⟨CurrentParticularPhysicalCoherence.localPotentialMode_eq_of_native _ l j n m w ha,
    CurrentParticularPhysicalCoherence.localPressureMode_eq_of_native _ l j n m w hp⟩

include C hN hS hcore in
theorem local_fields_eq_ordered (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    localPotential x n w = localPotential x m w ∧ localPressure x n w = localPressure x m w := by
  have he := fun (l : ActualParticularStageControls.Label B N0) (j : ℤ)
    (hj : j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand) =>
      modes_eq_ordered H C hS hcore l j
        ((ParticularWaveAssembly.mem_modes x.coefficients.residualBand j).mp hj).1 n m k hi hn hm hr
  have hzn := fun l hl j => modes_zero_of_inactive H C hN hcore l j n hn hl
  have hzm := fun l hl j => modes_zero_of_inactive H C hN hcore l j m hm hl
  constructor
  · apply sum_eq_of_agree_and_zero
    · intro l
      exact Finset.sum_congr rfl (fun j hj => (he l j hj).1)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzn l hl j).1)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzm l hl j).1)
  · apply sum_eq_of_agree_and_zero
    · intro l
      exact Finset.sum_congr rfl (fun j hj => (he l j hj).2)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzn l hl j).2)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzm l hl j).2)

include C hN hS hcore in
theorem local_fields_eq (n m : ℕ) {w : SpaceTime}
    (hn : w ∈ ValidDyadicBandCover.band h n) (hm : w ∈ ValidDyadicBandCover.band h m) :
    localPotential x n w = localPotential x m w ∧ localPressure x n w = localPressure x m w := by
  by_cases hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)
  · rcases le_total (CommonWindow.index h n) (CommonWindow.index h m) with hle | hle
    · exact local_fields_eq_ordered H C hN hS hcore n m
        (CommonWindow.index h m - CommonWindow.index h n) (Nat.add_sub_of_le hle) hn hm hr
    · have hh := local_fields_eq_ordered H C hN hS hcore m n
        (CommonWindow.index h n - CommonWindow.index h m) (Nat.add_sub_of_le hle) hm hn hr
      exact ⟨hh.1.symm, hh.2.symm⟩
  · have haxis : PhysicalGraphBounds.radialProjection w = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm ((PolarCharts.norm_le_radius _).trans (le_of_not_gt hr)) (norm_nonneg _)
    have hzn := ActualCurrentWaveSupport.current_local_axis_germs hN
      (ActualCycleParameters.particularState x) (refined_support H hcore) n hn haxis
    have hzm := ActualCurrentWaveSupport.current_local_axis_germs hN
      (ActualCycleParameters.particularState x) (refined_support H hcore) m hm haxis
    exact ⟨hzn.1.eq_of_nhds.trans hzm.1.eq_of_nhds.symm,
      hzn.2.eq_of_nhds.trans hzm.2.eq_of_nhds.symm⟩

include C hN hS hcore in
theorem compatible (N : ℕ) :
    ValidDyadicBandCover.Compatible h N (localPotential x) ∧
      ValidDyadicBandCover.Compatible h N (localPressure x) := by
  constructor
  · intro n m w hw
    exact (local_fields_eq H C hN hS hcore n.val m.val hw.1 hw.2).1
  · intro n m w hw
    exact (local_fields_eq H C hN hS hcore n.val m.val hw.1 hw.2).2

include C hN hS hcore in
theorem potential_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    potential x N =ᶠ[𝓝 w] localPotential x n :=
  ValidDyadicBandCover.field_germ outgoing.data.h_pos outgoing.data.h_lt_half
    (compatible H C hN hS hcore N).1 hn hw

include C hN hS hcore in
theorem pressure_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    pressure x N =ᶠ[𝓝 w] localPressure x n :=
  ValidDyadicBandCover.field_germ outgoing.data.h_pos outgoing.data.h_lt_half
    (compatible H C hN hS hcore N).2 hn hw

include C hN hS hcore in
theorem fields_eq (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    potential x N w = localPotential x n w ∧ pressure x N w = localPressure x n w :=
  ⟨(potential_germ H C hN hS hcore N n hn hw).eq_of_nhds,
    (pressure_germ H C hN hS hcore N n hn hw).eq_of_nhds⟩

include C hN hS hcore in
theorem potential_curl_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    SpatialCurl.spatialCurl (potential x N) =ᶠ[𝓝 w] SpatialCurl.spatialCurl (localPotential x n) :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (potential_germ H C hN hS hcore N n hn hw)

include C hN hS hcore in
theorem jets_eq (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (m : ℕ) :
    iteratedFDeriv ℝ m (potential x N) w = iteratedFDeriv ℝ m (localPotential x n) w ∧
      iteratedFDeriv ℝ m (pressure x N) w = iteratedFDeriv ℝ m (localPressure x n) w := by
  have hc := compatible H C hN hS hcore N
  exact ⟨ValidDyadicBandCover.field_jet_eq outgoing.data.h_pos outgoing.data.h_lt_half hc.1 hn hw m,
    ValidDyadicBandCover.field_jet_eq outgoing.data.h_pos outgoing.data.h_lt_half hc.2 hn hw m⟩

include C hN hS hcore in
theorem active_zero_germs {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N)
    {w : SpaceTime} (hw : w ∈ CutStageEstimates.physicalSublevel h qbig)
    (hX : (SlowBorelBase.cartesianChart h w).2.1 ∉
      Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal)) :
    (potential x N =ᶠ[𝓝 w] fun _ => 0) ∧ (pressure x N =ᶠ[𝓝 w] fun _ => 0) := by
  have hc := compatible H C hN hS hcore N
  exact ActualCurrentWaveSupport.current_field_active_germs hN
    (ActualCycleParameters.particularState x) (refined_support H hcore) hc.1 hc.2 hqbig hw hX

include C hN hS hcore in
theorem shrinking_support {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        qbig (potential x N) ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        qbig (pressure x N) := by
  have hc := compatible H C hN hS hcore N
  exact ActualCurrentWaveSupport.current_field_support hN
    (ActualCycleParameters.particularState x) (refined_support H hcore) hc.1 hc.2 hqbig

include C hN hS hcore in
theorem axis_zero {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    GermCandidateAssembly.AxisZeroOn (MixedAxisPreservation.localDomain h qbig) (potential x N) :=
  ActualCurrentWaveSupport.current_field_axisZeroOn hN
    (ActualCycleParameters.particularState x) (refined_support H hcore)
    (compatible H C hN hS hcore N).1 hqbig

include hcore in
theorem refined_invariant : ActualParticularCycleData.Invariant σ x :=
  { H with inputSupport := fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport l) (hcore
      l) }

include hN hcore in
theorem local_fields_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (localPotential x n) (ValidDyadicBandCover.band h n) ∧
      ContDiffOn ℝ ∞ (localPressure x n) (ValidDyadicBandCover.band h n) := by
  have hs (w : SpaceTime) (hw : w ∈ ValidDyadicBandCover.band h n) :
      ContDiffAt ℝ ∞ (localPotential x n) w ∧ ContDiffAt ℝ ∞ (localPressure x n) w := by
    by_cases haxis : PhysicalGraphBounds.radialProjection w = 0
    · have hz := ActualCurrentWaveSupport.current_local_axis_germs hN
        (ActualCycleParameters.particularState x) (refined_support H hcore) n hw haxis
      exact ⟨contDiffAt_const.congr_of_eventuallyEq hz.1, contDiffAt_const.congr_of_eventuallyEq
          hz.2⟩
    · exact ActualCurrentParticularPhysical.localFields_contDiffAt_of_invariant
        (refined_invariant H hcore) hN n (norm_pos_iff.mpr haxis)
        (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
          (PhysicalGraphBounds.radialProjection w))
        (ActualCurrentParticularPhysical.chosenChart_valid haxis)
        ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, Set.mem_univ _⟩
  exact ⟨fun w hw => (hs w hw).1.contDiffWithinAt, fun w hw => (hs w hw).2.contDiffWithinAt⟩

include C hN hS hcore in
theorem fields_smooth {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ (potential x N) (CutStageEstimates.physicalSublevel h qbig) ∧
      ContDiffOn ℝ ∞ (pressure x N) (CutStageEstimates.physicalSublevel h qbig) := by
  have hc := compatible H C hN hS hcore N
  exact ⟨ValidDyadicBandCover.field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hc.1 hqbig
      (fun n _ => (local_fields_smooth H hN hcore n).1),
    ValidDyadicBandCover.field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hc.2 hqbig
      (fun n _ => (local_fields_smooth H hN hcore n).2)⟩

end Incoming

end NavierStokes.ActualValidBandWaves
