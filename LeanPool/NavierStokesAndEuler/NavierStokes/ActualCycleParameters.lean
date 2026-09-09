/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleGeometry

/-!
# Literal cycle parameters on the initialized labels

The current cycle uses the same primary choice, moving strip, pressure
gauge, index and rank patch as its initialization.  The particular solver
orders the sign before the spatial label; initialization and the signed
solver order it after the spatial label.  The equivalence below transports
the actual finite coefficient family, rather than choosing new labels.

This module constructs the parameters and proves their data identities.
It does not assume or assert the analytic preservation of a correction
cycle.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCycleParameters

open Set Function CorrectionState CorrectionStep CorrectionInitialization
open scoped BigOperators

/-! ## Exact transport of the stored coefficient family -/

/-- Reindex coefficients, bundling `labels`, `blocks`, `gaussian`, `aliasCoefficients` and the
required compatibility proofs. -/
noncomputable def reindexCoefficients {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) : CycleCoefficients κ where
  labels n := (v.labels n).map e.symm.toEmbedding
  blocks l := v.blocks (e l)
  gaussian l := v.gaussian (e l)
  aliasCoefficients l := v.aliasCoefficients (e l)
  residualBand := v.residualBand

/-- Reindex state, bundling `state`, `coefficients`, `axisymmetricAlias`. -/
noncomputable def reindexState {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : CycleState κ where
  state := x.state
  coefficients := reindexCoefficients e x.coefficients
  axisymmetricAlias := x.axisymmetricAlias

/-- Reindex parameters, bundling `gauge`, `strip`, `patch`, `coordinate` and the required
compatibility proofs. -/
noncomputable def reindexParameters {ι κ : Type} (e : κ ≃ ι)
    (p : CycleParameters ι) : CycleParameters κ where
  gauge := p.gauge
  strip := p.strip
  patch := p.patch
  coordinate := p.coordinate
  timeExponent := p.timeExponent
  commonIndex := p.commonIndex
  axial := p.axial
  particular l := p.particular (e l)
  signed l := p.signed (e l)
  rank := p.rank

@[simp] theorem reindexCoefficients_mem {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) (n : ℕ) (l : κ) :
    l ∈ (reindexCoefficients e v).labels n ↔ e l ∈ v.labels n := by
  classical
  simp [reindexCoefficients]

@[simp] theorem reindexState_state {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : (reindexState e x).state = x.state := rfl

@[simp] theorem reindexState_axis {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : (reindexState e x).axisymmetricAlias = x.axisymmetricAlias := rfl

@[simp] theorem reindexState_band {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) :
    (reindexState e x).coefficients.residualBand = x.coefficients.residualBand := rfl

theorem reindexCoefficients_symm {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) :
    reindexCoefficients e.symm (reindexCoefficients e v) = v := by
  classical
  rcases v with ⟨labels, blocks, gaussian, aliasCoefficients, residualBand⟩
  simp only [reindexCoefficients]
  congr 1
  · funext n
    ext l
    simp
  · funext l
    simp
  · funext l
    simp
  · funext l
    simp

theorem reindexState_symm {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : reindexState e.symm (reindexState e x) = x := by
  rcases x with ⟨state, coefficients, axis⟩
  simp only [reindexState, reindexCoefficients_symm]

theorem reindexCoefficients_sum {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : ι → E) :
    (∑ l ∈ (reindexCoefficients e v).labels n, f (e l)) = ∑ l ∈ v.labels n, f l := by
  classical
  simp [reindexCoefficients]

theorem reindexState_representation {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι)
    (H : CycleRepresentation x.coefficients x.state x.axisymmetricAlias) :
    CycleRepresentation (reindexState e x).coefficients (reindexState e x).state
      (reindexState e x).axisymmetricAlias := by
  constructor
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.velocity n z i
  · intro n z
    simpa [reindexState, reindexCoefficients] using H.pressure n z
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.gaussian n z i
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.aliasError n z i

theorem reindexState_bands {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) (H : CoefficientBands x.coefficients) :
    CoefficientBands (reindexState e x).coefficients :=
  ⟨fun l => H.velocityPressure (e l), fun l => H.gaussian (e l),
    fun l => H.aliasError (e l)⟩

/-! ## The two label orders describe the same primary choice -/

/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0
/-- Particular index: an abbreviation for `ActualParticularStageControls.Label B N0`. -/
abbrev ParticularIndex (B N0 : ℕ) := ActualParticularStageControls.Label B N0

/-- Swap, given by `Equiv.prodComm _ _`. -/
noncomputable def swap (B N0 : ℕ) : Index B N0 ≃ ParticularIndex B N0 :=
  Equiv.prodComm _ _

@[simp] theorem swap_apply {B N0 : ℕ} (l : Index B N0) : swap B N0 l = (l.2, l.1) := rfl

@[simp] theorem swap_symm_apply {B N0 : ℕ} (l : ParticularIndex B N0) :
    (swap B N0).symm l = (l.2, l.1) := rfl

/-- Particular state, given by `reindexState (swap B N0).symm x`. -/
noncomputable def particularState {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CycleState (ParticularIndex B N0) := reindexState (swap B N0).symm x

@[simp] theorem particularState_state {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (particularState x).state = x.state := rfl

theorem particularState_blocks {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.blocks (swap B N0 l) = x.coefficients.blocks l := rfl

theorem particularState_gaussian {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.gaussian (swap B N0 l) = x.coefficients.gaussian l := rfl

theorem particularState_alias {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.aliasCoefficients (swap B N0 l) =
      x.coefficients.aliasCoefficients l := rfl

theorem particularState_mem {B N0 : ℕ} (x : CycleState (Index B N0))
    (n : ℕ) (l : Index B N0) :
    swap B N0 l ∈ (particularState x).coefficients.labels n ↔ l ∈ x.coefficients.labels n := by
  simpa only [particularState, reindexState, Equiv.symm_apply_apply] using
    reindexCoefficients_mem (swap B N0).symm x.coefficients n (swap B N0 l)

theorem particularState_roundtrip {B N0 : ℕ} (x : CycleState (Index B N0)) :
    reindexState (swap B N0) (particularState x) = x :=
  reindexState_symm (swap B N0).symm x

/-! ## The actual four-stage parameter constructor -/

/-- Parameters, constructed using `CycleParameters.ofGeometry`. -/
noncomputable def parameters {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CycleParameters (Index B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (fun l => ActualParticularStageControls.parameters (particularState x) (swap B N0 l))
    ActualSignedStageControls.parameters ActualPrimary.rankData

/-- The same literal builder expressed in the particular solver's label
order.  This has no additional geometric or analytic choices. -/
noncomputable def parametersInParticularOrder {B N0 : ℕ}
    (x : CycleState (ParticularIndex B N0)) : CycleParameters (ParticularIndex B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (ActualParticularStageControls.parameters x)
    (fun l => ActualSignedStageControls.parameters ((swap B N0).symm l)) ActualPrimary.rankData

theorem parameters_swap {B N0 : ℕ} (x : CycleState (Index B N0)) :
    reindexParameters (swap B N0).symm (parameters x) =
      parametersInParticularOrder (particularState x) := rfl

@[simp] theorem parameters_gauge {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).gauge = ActualPrimary.commonGauge := rfl

@[simp] theorem parameters_strip {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).strip = ActualInitialization.strip := rfl

@[simp] theorem parameters_patch {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).patch = ActualInitialization.patch := rfl

@[simp] theorem parameters_coordinate {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).coordinate = 2 * ActualPrimary.h := rfl

@[simp] theorem parameters_timeExponent {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).timeExponent = ActualPrimary.h := rfl

@[simp] theorem parameters_commonIndex {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).commonIndex = CommonWindow.index ActualPrimary.h := rfl

@[simp] theorem parameters_axial {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).axial = ActualInitialization.axial := rfl

@[simp] theorem parameters_rank {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).rank = ActualPrimary.rankData := rfl

@[simp] theorem parameters_particular {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (parameters x).particular l =
      ActualParticularStageControls.parameters (particularState x) (swap B N0 l) := rfl

@[simp] theorem parameters_signed {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (parameters x).signed l = ActualSignedStageControls.parameters l := rfl

theorem parameters_indexBounds {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CommonBaseContext.IndexBounds ActualPrimary.h (parameters x).commonIndex
      (CommonWindow.gap ActualPrimary.h) :=
  CommonWindow.indexBounds ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le

theorem parameters_geometry_operators {B N0 : ℕ} (_x : CycleState (Index B N0)) :
    ActualInitialization.geometry.operators = (ActualPrimary.commonContext B).operators := rfl

theorem parameters_compatible {B N0 : ℕ} (x : CycleState (Index B N0)) :
    ActualCycleExcluded.Compatible ActualCycleGeometry.similarityData (parameters x)
      (ActualPrimary.commonContext B) :=
  ActualCycleGeometry.compatible B
    (fun l => ActualParticularStageControls.parameters (particularState x) (swap B N0 l))
    ActualSignedStageControls.parameters

/-- The physical band floor belongs to the already selected primary
choice and does not change with the current correction state. -/
noncomputable def bandFloor (B N0 : ℕ) : ℕ := (ActualPrimary.choice B N0).prepared.N

/-- Source band, given by `BaseChartJets.cellBand l.1`. -/
noncomputable def sourceBand {B N0 : ℕ} (l : Index B N0) : ℕ := BaseChartJets.cellBand l.1

theorem bandFloor_ge (B N0 : ℕ) : N0 ≤ bandFloor B N0 := ActualPrimary.threshold B N0

theorem sourceBand_ge_floor {B N0 : ℕ} (l : Index B N0) :
    bandFloor B N0 ≤ sourceBand l := l.1.property

theorem particular_reference_band {B N0 : ℕ} (l : Index B N0) :
    (ActualParticularStageControls.reference (swap B N0 l)).band = sourceBand l := rfl

theorem particular_gap {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ActualParticularStageControls.gap (swap B N0 l) n =
      ChartScales.nativeIndex ActualPrimary.h (sourceBand l) -
        CommonWindow.index ActualPrimary.h n := rfl

theorem activeLabel_band {B N0 : ℕ} (n : ℕ) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    sourceBand l ∈ CommonWindow.levels n := by
  classical
  have hm := (ActualPrimary.mem_activeLabels ActualPrimary.standardRegion n l.1 l.2).mp hl
  obtain ⟨m, hm, hg⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hg
  have he : m = sourceBand l := congrArg Prod.fst hk
  simpa only [he] using hm

theorem activeLabel_index {B N0 : ℕ} (n : ℕ) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (sourceBand l) :=
  CommonWindow.index_le (activeLabel_band n l hl)

theorem activeLabel_particular {B N0 : ℕ} (n : ℕ) (hn : 1 ≤ n) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    1 ≤ n ∧ BaseChartJets.cellBand (swap B N0 l).2 ∈ CommonWindow.levels n :=
  ⟨hn, activeLabel_band n l hl⟩

/-! The particular source really is the current stored residual. -/

theorem particular_assembly_context {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).context =
      StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B) := rfl

theorem particular_assembly_state {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).state =
      StateReindex.state cycleAssoc.symm x.state := rfl

theorem particular_assembly_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).carrierBlock =
      StateReindex.block cycleAssoc.symm (x.coefficients.blocks l) := rfl

theorem particular_assembly_gaussian {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).gaussianInput =
      StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l) := rfl

theorem particular_assembly_alias {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).aliasInput =
      StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l) := rfl

theorem particular_source {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) :
    (((parameters x).particular l).copyData
      (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
          j).source =
    ParticularWaveAssembly.sourceFamily
      (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j := rfl

theorem signed_request {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).signedRequest x.coefficients (ActualPrimary.commonContext B) x.state =
      LocalSignedRequest.fullRequest ActualInitialization.strip ActualInitialization.patch
        (2 * ActualPrimary.h) (ActualPrimary.commonContext B)
        ((parameters x).afterParticular x.coefficients (ActualPrimary.commonContext B) x.state) :=
            rfl

/-! ## The signed update uses the initialized primary carrier -/

theorem signed_frequency (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).frequency = p.base.frequency := rfl

theorem signed_phase (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).phase = fun n z => p.base.phase n (z, 0) := rfl

theorem signed_angular (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).angularFrequency = p.angularFrequency := rfl

theorem primaryPiece_frequency (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).frequency = p.coefficients.frequency := rfl

theorem primaryPiece_phase (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).phase = phase := rfl

theorem primaryPiece_angular (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).angularFrequency = angular := rfl

theorem signed_primary_carrier {B N0 : ℕ} (l : Index B N0)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (ActualInitialization.primaryBlock l)
      ((ActualSignedStageControls.parameters l).exactBlock s request) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (signed_frequency (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_frequency (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm
  · exact (signed_phase (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_phase (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm
  · exact (signed_angular (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_angular (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm

theorem signed_tangent_carrier {B N0 : ℕ} (l : Index B N0)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (ActualInitialization.tangentBlock l)
      ((ActualSignedStageControls.parameters l).exactBlock s request) := by
  have hs := signed_primary_carrier l s request
  have hp := ActualInitialization.primary_tangent_carrier l
  exact ⟨hs.frequency.trans hp.frequency.symm, hs.phase.trans hp.phase.symm,
    hs.angular.trans hp.angular.symm⟩

theorem parameters_signed_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients c x.state l) := by
  have hs := signed_tangent_carrier l (parameters x).strip
    ((parameters x).signedRequest x.coefficients c x.state)
  exact ⟨hs.frequency.trans H.frequency, hs.phase.trans H.phase, hs.angular.trans H.angular⟩

theorem parameters_particular_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).particularBlock x.coefficients c x.state l) :=
  (parameters x).particular_carrier x.coefficients c x.state l

theorem parameters_gaussian_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).particularGaussianBlock x.coefficients c x.state l) :=
  (parameters x).particularGaussian_carrier x.coefficients c x.state l

theorem invariant_signed_carrier {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l) :=
  parameters_signed_carrier x _ l (H.carrier l)

theorem initial_signed_carrier (B N0 : ℕ) (l : Index B N0) :
    let x := ActualInitialization.initialCycleState B N0
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l) :=
  parameters_signed_carrier _ _ l (ActualInitialization.primary_tangent_carrier l)

/-! ## The same fixed primitives at every valid state -/

/-- Fixed parameters, constructed using `CycleParameters.ofGeometry`. -/
noncomputable def fixedParameters (B N0 : ℕ) : CycleParameters (Index B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (swap B N0 l))
    ActualSignedStageControls.parameters ActualPrimary.rankData

@[simp] theorem fixedParameters_particular (B N0 : ℕ) (l : Index B N0) :
    (fixedParameters B N0).particular l =
      ActualParticularStageControls.canonicalParameters (l.2, l.1) := rfl

@[simp] theorem fixedParameters_signed (B N0 : ℕ) (l : Index B N0) :
    (fixedParameters B N0).signed l = ActualSignedStageControls.parameters l := rfl

@[simp] theorem fixedParameters_strip (B N0 : ℕ) :
    (fixedParameters B N0).strip = ActualInitialization.geometry.strip := rfl

@[simp] theorem fixedParameters_gauge (B N0 : ℕ) :
    (fixedParameters B N0).gauge = ActualInitialization.geometry.gauge := rfl

@[simp] theorem fixedParameters_patch (B N0 : ℕ) :
    (fixedParameters B N0).patch = ActualInitialization.geometry.patch := rfl

@[simp] theorem fixedParameters_coordinate (B N0 : ℕ) :
    (fixedParameters B N0).coordinate = ActualInitialization.geometry.coord := rfl

@[simp] theorem fixedParameters_timeExponent (B N0 : ℕ) :
    (fixedParameters B N0).timeExponent = ActualPrimary.h := rfl

@[simp] theorem fixedParameters_commonIndex (B N0 : ℕ) :
    (fixedParameters B N0).commonIndex = CommonWindow.index ActualPrimary.h := rfl

@[simp] theorem fixedParameters_axial (B N0 : ℕ) :
    (fixedParameters B N0).axial = ActualInitialization.axial := rfl

@[simp] theorem fixedParameters_rank (B N0 : ℕ) :
    (fixedParameters B N0).rank = ActualPrimary.rankData := rfl

theorem fixedParameters_compatible (B N0 : ℕ) :
    ActualCycleExcluded.Compatible ActualCycleGeometry.similarityData (fixedParameters B N0)
      (ActualPrimary.commonContext B) :=
  ActualCycleGeometry.compatible B
    (fun l => ActualParticularStageControls.canonicalParameters (swap B N0 l))
    ActualSignedStageControls.parameters

theorem current_frequency {B N0 : ℕ} (x : CycleState (Index B N0)) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) (n : ℕ) :
    (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n := by
  calc
    _ = (ActualInitialization.tangentBlock l).frequency n := congrFun H.frequency.symm n
    _ = (ActualInitialization.primaryBlock l).frequency n :=
      congrFun (ActualInitialization.primary_tangent_carrier l).frequency n
    _ = (ActualInitialization.primaryPiece l).coefficients.frequency n :=
      congrFun (primaryPiece_frequency (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)) n
    _ = _ := rfl

theorem parameters_particular_eq_fixed {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    (parameters x).particular l = (fixedParameters B N0).particular l :=
  ActualParticularStageControls.parameters_eq_canonical (particularState x) (swap B N0 l)
    (current_frequency x l H)

theorem parameters_eq_fixed {B N0 : ℕ} (x : CycleState (Index B N0))
    (H : ∀ l, SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    parameters x = fixedParameters B N0 := by
  have hp : (parameters x).particular = (fixedParameters B N0).particular :=
    funext (fun l => parameters_particular_eq_fixed x l (H l))
  exact congrArg (fun part : Index B N0 → ParticularParameters CycleSlow =>
    CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      part ActualSignedStageControls.parameters ActualPrimary.rankData) hp

theorem invariant_parameters_eq_fixed {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) :
    parameters x = fixedParameters B N0 := parameters_eq_fixed x H.carrier

theorem initial_parameters_eq_fixed (B N0 : ℕ) :
    parameters (ActualInitialization.initialCycleState B N0) = fixedParameters B N0 :=
  parameters_eq_fixed _ ActualInitialization.primary_tangent_carrier

theorem fixedParameters_signed_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    SameCarrier (x.coefficients.blocks l)
      ((fixedParameters B N0).signedBlock x.coefficients c x.state l) := by
  have hs := signed_tangent_carrier l (fixedParameters B N0).strip
    ((fixedParameters B N0).signedRequest x.coefficients c x.state)
  exact ⟨hs.frequency.trans H.frequency, hs.phase.trans H.phase, hs.angular.trans H.angular⟩

theorem invariant_fixedParameters_signed_carrier {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((fixedParameters B N0).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l)
          :=
  fixedParameters_signed_carrier x _ l (H.carrier l)

end NavierStokes.ActualCycleParameters
