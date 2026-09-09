/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCandidateConstruction
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalStageBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualValidBandWaves
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalPrefixFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.GluedStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedWaveData
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentSignedCurl
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermEndpointInputs

@[expose] public section

/-!
# Literal physical data for the actual candidate

The initial fields use the same primary choice and the same initialized
mean state as `ActualCandidateConstruction`.  Their support, smoothness,
and axis germs are derived from those constructors.
-/

noncomputable section

namespace NavierStokes.ActualCandidateAssembly


open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-! ## The finite initialization, without the base fields -/

noncomputable def initialPotential (B N0 : ℕ) : VelocityField :=
  InitialPhysicalData.potential B N0 + ActualCandidateConstruction.streamMeanStages B N0 0

noncomputable def initialPressure (B N0 : ℕ) : PressureField :=
  InitialPhysicalData.pressure B N0 + ActualCandidateConstruction.pressureMeanStages B N0 0

noncomputable def initialDirect (B N0 : ℕ) : VelocityField :=
  ActualCandidateConstruction.angularMeanStages B N0 0

noncomputable def initialDirectData (B N0 : ℕ) :
    DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h (ActualCandidateConstruction.qbig B N0)) :=
  ActualMeanStageData.initialAngularData B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.qbig B N0) le_rfl

theorem initialDirectData_field (B N0 : ℕ) :
    DirectAngularDiagonal.angularField (initialDirectData B N0).scalar = initialDirect B N0 := by
  exact (ActualMeanStageData.initialAngularData_field B N0
    (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.qbig B N0)
      le_rfl).trans
      (ActualCandidateConstruction.angularMeanStages_zero B N0).symm

theorem initialPotential_eq_stage (B N0 : ℕ) :
    initialPotential B N0 =
      (ActualCandidateConstruction.initialPotentialStage B N0
        (InitialPhysicalData.copyPotential B N0)).field := by
  rw [ActualCandidateConstruction.initialPotentialStage_field,
    InitialPhysicalData.copyPotential_field]
  rfl

theorem initialPotential_eq_increment (B N0 : ℕ) :
    initialPotential B N0 = ActualPhysicalStageBounds.initialIncrement
      (InitialPhysicalData.potentialWaveData B N0)
      (ActualPhysicalStageBounds.actualInitialTemporalInput B N0
        (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B
          N0))
      (ActualPhysicalStageBounds.actualInitialRankInput B N0
        (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B
          N0)) := by
  rw [initialPotential, ActualCandidateConstruction.streamMeanStages_zero,
    ActualMeanPhysicalData.initialStream_angularField]
  funext w
  change InitialPhysicalData.potential B N0 w +
      ((ActualMeanPhysicalData.initialTemporalFamily B N0
        (ActualCandidateConstruction.firstBand B N0)).angularField w +
       (ActualMeanPhysicalData.initialRankFamily B N0
        (ActualCandidateConstruction.firstBand B N0)).angularField w) = _
  exact (add_assoc _ _ _).symm

theorem initialPressure_eq_increment (B N0 : ℕ) :
    initialPressure B N0 = ActualPhysicalStageBounds.initialPressureIncrement
      (InitialPhysicalData.pressureWaveData B N0)
      (ActualPhysicalStageBounds.actualInitialPressureInput B N0
        (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B
          N0)) := by
  rw [initialPressure, ActualCandidateConstruction.pressureMeanStages_zero]
  rfl

theorem initialPotential_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (initialPotential B N0) (ActualCandidateConstruction.physicalDomain B N0) := by
  rw [initialPotential_eq_increment]
  exact ActualPhysicalStageBounds.initialIncrement_smooth _ _ _
    outgoing.data.h_pos outgoing.data.h_lt_half le_rfl le_rfl

theorem initialPressure_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (initialPressure B N0) (ActualCandidateConstruction.physicalDomain B N0) := by
  rw [initialPressure_eq_increment]
  exact ActualPhysicalStageBounds.initialPressureIncrement_smooth _ _
    outgoing.data.h_pos outgoing.data.h_lt_half le_rfl

theorem initialDirect_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (initialDirect B N0) (ActualCandidateConstruction.physicalDomain B N0) := by
  rw [← initialDirectData_field]
  exact (initialDirectData B N0).field_smooth
    (LocalAngularDiagonal.localSlowDomain_open outgoing.data.h_pos outgoing.data.h_lt_half _)

theorem initialPotential_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialPotential B N0) := by
  have hw := PhysicalStageSupport.wave_vector_support
    (InitialPhysicalData.potentialWaveData B N0)
    (qbig := ActualCandidateConstruction.qbig B N0)
    (R := ActualInitialization.geometry.patch.b) (by exact le_rfl)
  have hm := (ActualMeanStageData.initial_shrinkingSupport B N0
    (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.qbig B N0)
      le_rfl).2.2.2
  erw [ActualMeanStageData.initialStreamSupport_field] at hm
  rw [initialPotential, ActualCandidateConstruction.streamMeanStages_zero]
  exact PhysicalStageSupport.support_add hw hm

theorem initialPressure_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialPressure B N0) := by
  have hw := PhysicalStageSupport.wave_pressure_support
    (InitialPhysicalData.pressureWaveData B N0)
    (qbig := ActualCandidateConstruction.qbig B N0)
    (R := ActualInitialization.geometry.patch.b) (by exact le_rfl)
  have hm := (PhysicalStageSupport.actual_coherent_support
    (ActualMeanPhysicalData.initialPressureFamily B N0 (ActualCandidateConstruction.firstBand B N0))
    (ActualMeanStageData.nativeSupport_of_moving _
      (ActualMeanPhysicalData.initial_pressure_moving B N0))
    (qbig := ActualCandidateConstruction.qbig B N0) le_rfl).1
  rw [initialPressure, ActualCandidateConstruction.pressureMeanStages_zero]
  exact PhysicalStageSupport.support_add hw hm

theorem initialDirect_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialDirect B N0) := by
  have hm := (ActualMeanStageData.initial_shrinkingSupport B N0
    (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.qbig B N0) le_rfl).1
  erw [ActualMeanStageData.initialAngularSupport_field] at hm
  simp only [initialDirect, ActualCandidateConstruction.angularMeanStages_zero]
  exact hm

theorem initialPotential_axisZeroOn (B N0 : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (initialPotential B N0) := by
  rw [initialPotential_eq_stage]
  exact GermCandidateAssembly.potentialStage_axisZeroOn outgoing.data.h_pos outgoing.data.h_lt_half
    _

/-! ## Exact exterior coordinates -/

theorem physicalRadiusX_eq (w : SpaceTime) :
    PhysicalWaveSum.physicalPosition w 0 ^ 2 / (2 * PhysicalWaveSum.physicalQ h w) =
      (SlowBorelBase.cartesianChart h w).2.1 := by
  change PolarCharts.radius (PhysicalGraphBounds.radialProjection w) ^ 2 /
      (2 * PhysicalWaveSum.physicalQ h w) =
    AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w
  rw [PolarCharts.radius_sq]
  change (w.2 0 ^ 2 + w.2 1 ^ 2) / (2 * PhysicalWaveSum.physicalQ h w) =
    ((w.2 0 ^ 2 + w.2 1 ^ 2) / 2) / PhysicalWaveSum.physicalQ h w
  rw [div_div]

theorem initialDirect_exterior (B N0 : ℕ) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) : initialDirect B N0 w = 0 := by
  rw [initialDirect, ActualCandidateConstruction.angularMeanStages_zero]
  exact (ActualMeanExterior.initialAngular_exterior B N0
    (ActualCandidateConstruction.firstBand B N0) ht hq he).2

theorem initialPotential_exterior (B N0 : ℕ) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) : initialPotential B N0 w = 0 := by
  have hx : InitialPhysicalData.physicalX w ∉
      Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal) := by
    simpa only [InitialPhysicalData.physicalX, physicalRadiusX_eq,
      ActualPolarCoverage.active, Set.mem_ofPred_eq] using he
  change InitialPhysicalData.potential B N0 w +
    ActualCandidateConstruction.streamMeanStages B N0 0 w = 0
  rw [InitialPhysicalData.potential_zero_exterior B N0 ht hx,
    ActualCandidateConstruction.streamMeanStages_zero,
    (ActualMeanExterior.initialStream_exterior B N0
      (ActualCandidateConstruction.firstBand B N0) ht hq he).2, add_zero]

theorem initialPressure_exterior (B N0 : ℕ) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) : initialPressure B N0 w = 0 := by
  have hx : InitialPhysicalData.physicalX w ∉
      Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal) := by
    simpa only [InitialPhysicalData.physicalX, physicalRadiusX_eq,
      ActualPolarCoverage.active, Set.mem_ofPred_eq] using he
  change InitialPhysicalData.pressure B N0 w +
    ActualCandidateConstruction.pressureMeanStages B N0 0 w = 0
  rw [InitialPhysicalData.pressure_zero_exterior B N0 ht hx,
    ActualCandidateConstruction.pressureMeanStages_zero,
    (ActualMeanExterior.initialPressure_exterior B N0
      (ActualCandidateConstruction.firstBand B N0) ht hq he).1, add_zero]

/-! ## The literal zeroth potential and pressure retain the base -/

noncomputable def zerothPotential (B N0 : ℕ) : VelocityField :=
  TailGaugePotential.finalPotential certificate modulation upper B + initialPotential B N0

noncomputable def zerothPressure (B N0 : ℕ) : PressureField :=
  FinalSlowBase.pressure certificate modulation upper B + initialPressure B N0

theorem zerothPotential_eq_initialPotential (B N0 : ℕ) :
    zerothPotential B N0 = ActualPhysicalStageBounds.initialPotential certificate modulation upper B
      (InitialPhysicalData.potentialWaveData B N0)
      (ActualPhysicalStageBounds.actualInitialTemporalInput B N0
        (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B
          N0))
      (ActualPhysicalStageBounds.actualInitialRankInput B N0
        (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B
          N0)) := by
  rw [zerothPotential, initialPotential_eq_increment]
  rfl

theorem zerothPotential_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (zerothPotential B N0) (ActualCandidateConstruction.physicalDomain B N0) := by
  rw [zerothPotential_eq_initialPotential]
  exact ActualPhysicalStageBounds.initialPotential_smooth certificate modulation upper B _ _ _
    le_rfl le_rfl

theorem zerothPressure_smooth (B N0 : ℕ) :
    ContDiffOn ℝ ∞ (zerothPressure B N0) (ActualCandidateConstruction.physicalDomain B N0) :=
  ((FinalSlowBase.pressure_smooth certificate modulation upper B).mono
    (fun _ hw => ⟨hw.1, mem_univ _⟩)).add (initialPressure_smooth B N0)

/-! ## The particular fields come from the same current state

The valid-band representative uses the common physical floor. Its local
formulas are the actual current solves, with the initializer's label order
converted by `ActualCycleParameters.particularState` inside the producer.
-/

noncomputable def particularPotential (B N0 j : ℕ) : VelocityField :=
  ActualValidBandWaves.potential (ActualCandidateConstruction.cycle B N0 j)
    (ActualCandidateConstruction.firstBand B N0)

noncomputable def particularPressure (B N0 j : ℕ) : PressureField :=
  ActualValidBandWaves.pressure (ActualCandidateConstruction.cycle B N0 j)
    (ActualCandidateConstruction.firstBand B N0)

/-! ## Mean fields on the exact residual-comparison charts -/

theorem meanChart_mem (B N0 n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain
      (ActualCandidateConstruction.qbig B N0) n a i) :
    (PhysicalMeanJetBounds.graph h n
      ((ActualCandidateConstruction.meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier := by
  have he := ActualMeanPotentialRealization.chartPoint_eq_graph ha i h n
    (ActualCycleResidualBounds.actualGap n) (Nat.sub_le _ _) hw.2.1
  rw [ActualCycleResidualBounds.actualGap_index] at he
  change (PhysicalMeanJetBounds.graph h n (ActualCycleResidualBounds.actualGap n) w).2.1 ∈
    standardRegion.carrier
  rw [← he]
  exact hw.2.2.2.1.1

theorem initial_oscillation (B N0 n : ℕ) (x : PhysicalResidualBridge.Cylinder) (i : Fin 3) :
    (ActualCandidateConstruction.cycle B N0 0).state.oscillation n x i =
      ∑ l ∈ activeLabels standardRegion B N0 n,
        (piece standardRegion l.2 l.1).velocity n x i := by
  change (ActualInitialization.initialState B N0).oscillation n x i = _
  rw [ActualInitialization.initialState_oscillation]
  rfl

theorem initial_oscillatoryPressure (B N0 n : ℕ) (x : PhysicalResidualBridge.Cylinder) :
    (ActualCandidateConstruction.cycle B N0 0).state.oscillatoryPressure n x =
      ∑ l ∈ activeLabels standardRegion B N0 n,
        (piece standardRegion l.2 l.1).pressure n x := by
  change (ActualInitialization.initialState B N0).oscillatoryPressure n x =
    ∑ l ∈ (ActualInitialization.coefficients B N0).labels n,
      (ActualInitialization.primaryPiece l).pressure n x
  simp [ActualInitialization.initialState, ActualInitialization.rankState,
    ActualInitialization.temporalState, ActualInitialization.primaryState,
    ActualInitialization.sourceState, CorrectionInitialization.bandSeed,
    CorrectionInitialization.GaugeInitialization.retainPressureAlias,
    VariableGaugeMean.rankStageState, VariableGaugeMean.temporalStageState,
    VariableGaugeMean.reconstructState, CorrectionState.State.addIncrement]

theorem initialVelocity_on_cylinder (B N0 n d : ℕ) {z : SpaceTime}
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hs : (PhysicalMeanJetBounds.graph h n d
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ standardRegion.carrier) :
    CyclePhysicalPrefixes.velocityMap (ActualCandidateConstruction.graph n)
      ((ActualCandidateConstruction.cycle B N0 0).state.oscillation n) z =
        CylindricalResidual.frame (-(z.2 1))
          (SpatialCurl.spatialCurl (InitialPhysicalData.potential B N0)
            (z.1, CylindricalResidual.chart z.2)) := by
  ext j
  simp only [CyclePhysicalPrefixes.velocityMap, LinearMap.coe_mk, AddHom.coe_mk,
    PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
    (ActualCandidateConstruction.cycle B N0 0).state.oscillation n
      (PhysicalResidualTZ.graphMapTZ (ActualCandidateConstruction.graph n) z) j = _
  have he : (ActualCandidateConstruction.cycle B N0 0).state.oscillation n
      (PhysicalResidualTZ.graphMapTZ (ActualCandidateConstruction.graph n) z) j =
      ChartScales.Q n ^ CoordinateAlgebra.A h *
        CylindricalResidual.frame (-(z.2 1))
          (SpatialCurl.spatialCurl (InitialPhysicalData.potential B N0)
            (z.1, CylindricalResidual.chart z.2)) j := by
    rw [initial_oscillation]
    exact InitialPhysicalData.velocity_chart_slow n d z ht hr hs j
  rw [he, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp

theorem initialPressure_on_cylinder (B N0 n d : ℕ) {z : SpaceTime}
    (ht : z.1 < 1) (hr : 0 < z.2 0)
    (hs : (PhysicalMeanJetBounds.graph h n d
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ standardRegion.carrier) :
    CyclePhysicalPrefixes.pressureMap (ActualCandidateConstruction.graph n)
      ((ActualCandidateConstruction.cycle B N0 0).state.oscillatoryPressure n) z =
        InitialPhysicalData.pressure B N0 (z.1, CylindricalResidual.chart z.2) := by
  change (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) ^ 2 *
    (ActualCandidateConstruction.cycle B N0 0).state.oscillatoryPressure n
      (PhysicalResidualTZ.graphMapTZ (ActualCandidateConstruction.graph n) z) = _
  have he : (ActualCandidateConstruction.cycle B N0 0).state.oscillatoryPressure n
      (PhysicalResidualTZ.graphMapTZ (ActualCandidateConstruction.graph n) z) =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) *
        InitialPhysicalData.pressure B N0 (z.1, CylindricalResidual.chart z.2) := by
    rw [initial_oscillatoryPressure]
    exact InitialPhysicalData.pressure_chart_slow n d z ht hr hs
  rw [he, pow_two, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n),
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have he : -CoordinateAlgebra.A h + -CoordinateAlgebra.A h + 2 * CoordinateAlgebra.A h = 0 := by
    ring
  rw [he, Real.rpow_zero, one_mul]

theorem initialWavePotential_on_chart (B N0 n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (InitialPhysicalData.potential B N0))
      (ActualCandidateConstruction.chartWaveParts B N0 a i n 0)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw.2.1).1
  have hb : (z.1, CylindricalResidual.chart z.2) = w :=
    ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
  have hs : (PhysicalMeanJetBounds.graph h n
      ((ActualCandidateConstruction.meanAtlas B N0).gap n)
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ standardRegion.carrier := by
    rw [hb]
    exact meanChart_mem B N0 n ha i hw
  have hangle : z.2 1 = (PhysicalCurlCovariance.polarInput a i w).2 := by
    simp only [z, PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_one]
  symm
  change CyclePhysicalPrefixes.polarVelocityMap a i
    (CyclePhysicalPrefixes.velocityMap (ActualCandidateConstruction.graph n)
      ((ActualCandidateConstruction.cycle B N0 0).state.oscillation n)) w = _
  simp only [CyclePhysicalPrefixes.polarVelocityMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hangle]
  change CylindricalResidual.frame (z.2 1)
    (CyclePhysicalPrefixes.velocityMap (ActualCandidateConstruction.graph n)
      ((ActualCandidateConstruction.cycle B N0 0).state.oscillation n) z) = _
  rw [initialVelocity_on_cylinder B N0 n _ (z := z) hw.1.1 hr hs,
    CylindricalResidual.frame_inverse', hb]

theorem initialWavePressure_on_chart (B N0 n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (InitialPhysicalData.pressure B N0)
      (ActualCandidateConstruction.chartWavePressureParts B N0 a i n 0)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw.2.1).1
  have hb : (z.1, CylindricalResidual.chart z.2) = w :=
    ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
  have hs : (PhysicalMeanJetBounds.graph h n
      ((ActualCandidateConstruction.meanAtlas B N0).gap n)
      (z.1, CylindricalResidual.chart z.2)).2.1 ∈ standardRegion.carrier := by
    rw [hb]
    exact meanChart_mem B N0 n ha i hw
  symm
  change CyclePhysicalPrefixes.pressureMap (ActualCandidateConstruction.graph n)
    ((ActualCandidateConstruction.cycle B N0 0).state.oscillatoryPressure n) z = _
  rw [initialPressure_on_cylinder B N0 n _ (z := z) hw.1.1 hr hs, hb]

theorem chartDomain_band (B N0 n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain
      (ActualCandidateConstruction.qbig B N0) n a i) :
    w ∈ ValidDyadicBandCover.band h n := by
  apply ValidDyadicBandCover.mem_band_iff.mpr
  refine ⟨hw.1.1, ?_⟩
  have hs := (meanChart_mem B N0 n ha i hw).2
  rwa [PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n
    ((ActualCandidateConstruction.meanAtlas B N0).gap n) hw.1.1] at hs

theorem direct_on_chart {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j n : ℕ) (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (LocalAngularDiagonal.rawSeries (ActualCandidateConstruction.directData M) j)
      (ActualCandidateConstruction.chartDirectStages B N0 a i n j)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  rw [ActualCandidateConstruction.directData_field]
  exact ActualCandidateConstruction.angularMeanStages_on_chart M j ha i n hn hw.1.1
    (meanChart_mem B N0 n ha i hw) hw.2.1

theorem stream_on_chart {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j n : ℕ) (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (ActualCandidateConstruction.streamMeanStages B N0 j))
      (ActualCandidateConstruction.chartStreamParts B N0 a i n j)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  exact ActualCandidateConstruction.streamMeanStages_curl_on_chart M j ha i n hn hw.1.1
    (meanChart_mem B N0 n ha i hw) hw.2.1

theorem meanPressure_on_chart {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j n : ℕ) (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (ActualCandidateConstruction.pressureMeanStages B N0 j)
      (ActualCandidateConstruction.chartMeanPressureParts B N0 a i n j)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  exact ActualCandidateConstruction.pressureMeanStages_on_chart M j ha i n hn hw.1.1
    (meanChart_mem B N0 n ha i hw) hw.2.1

theorem stream_exterior {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j : ℕ) {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    ActualCandidateConstruction.streamMeanStages B N0 j w = 0 := by
  cases j with
  | zero =>
      rw [ActualCandidateConstruction.streamMeanStages_zero]
      exact (ActualMeanExterior.initialStream_exterior B N0
        (ActualCandidateConstruction.firstBand B N0) ht hq he).2
  | succ j =>
      rw [ActualCandidateConstruction.streamMeanStages_succ M]
      exact (ActualMeanExterior.cycleStream_exterior M j ht hq he).2

theorem direct_exterior {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j : ℕ) {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    LocalAngularDiagonal.rawSeries (ActualCandidateConstruction.directData M) j w = 0 := by
  rw [ActualCandidateConstruction.directData_field]
  cases j with
  | zero => exact initialDirect_exterior B N0 ht hq he
  | succ j =>
      rw [ActualCandidateConstruction.angularMeanStages_succ M]
      exact (ActualMeanExterior.cycleAngularIncrement_exterior M j ht hq he).2

theorem meanPressure_exterior {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j : ℕ) {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ActualCandidateConstruction.qbig B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    ActualCandidateConstruction.pressureMeanStages B N0 j w = 0 := by
  cases j with
  | zero =>
      rw [ActualCandidateConstruction.pressureMeanStages_zero]
      exact (ActualMeanExterior.initialPressure_exterior B N0
        (ActualCandidateConstruction.firstBand B N0) ht hq he).1
  | succ j =>
      rw [ActualCandidateConstruction.pressureMeanStages_succ M]
      exact (ActualMeanExterior.cyclePressureIncrement_exterior M j ht hq he).1

theorem stream_axisZeroOn {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (ActualCandidateConstruction.streamMeanStages B N0 j) := by
  rw [← ActualCandidateConstruction.meanStreamSupport_field M j]
  exact GermCandidateAssembly.angularSupport_axisZeroOn outgoing.data.h_pos outgoing.data.h_lt_half
    _

/-! ## The actual native run supplies every mean and signed request -/

noncomputable def runData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualStageEstimates.RunData B N0 where
  invariant := ActualCyclePreservation.state_invariant B N0 hN
  step := ActualCyclePreservation.state_stepData B N0 hN
  particular := ActualCyclePreservation.state_particularInputs B N0 hN

theorem meanCycleInput (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualCandidateConstruction.MeanCycleInput B N0 :=
  ActualCycleCoherence.mean_input_of_transport B N0 (ActualCandidateConstruction.firstBand B N0)
    ActualIterationLedger.sigma ActualCoreSupport.refinedCarrier
    (ActualCyclePreservation.state_invariant B N0 hN)
    (ActualCyclePreservation.state_waveData B N0 hN)
    (ActualCyclePreservation.state_wave_transport B N0 hN)

theorem postParticularResult (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularMeanGain.Result (ActualCandidateConstruction.cycle B N0 j)
      (ActualIterationLedger.sigma j) :=
  ActualParticularMeanGain.postParticular_gain
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_particularInputs B N0 hN j)
    (ActualIterationLedger.sigma_admissible j)

noncomputable def signedPotential (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : VelocityField :=
  ActualSignedExterior.cyclePotential (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCandidateConstruction.cycle B N0 j)
      (postParticularResult B N0 hN j).primitive)

noncomputable def signedPressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : PressureField :=
  ActualSignedExterior.cyclePressure (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCandidateConstruction.cycle B N0 j)
      (postParticularResult B N0 hN j).primitive)

noncomputable def positivePotential (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : VelocityField :=
  particularPotential B N0 j + signedPotential B N0 hN j +
    ActualCandidateConstruction.streamMeanStages B N0 (j + 1)

noncomputable def positivePressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : PressureField :=
  particularPressure B N0 j + signedPressure B N0 hN j +
    ActualCandidateConstruction.pressureMeanStages B N0 (j + 1)

noncomputable def directData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h (ActualCandidateConstruction.qbig B N0)) :=
  ActualCandidateConstruction.directData (meanCycleInput B N0 hN)

noncomputable def potentialStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : ℕ → VelocityField :=
  GermCandidateAssembly.potentialStages certificate modulation upper B
    (initialPotential B N0) (positivePotential B N0 hN)

noncomputable def directStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : ℕ → VelocityField :=
  LocalAngularDiagonal.rawSeries (directData B N0 hN)

noncomputable def pressureStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : ℕ → PressureField :=
  MixedCandidateAssembly.pressureStages certificate modulation upper B
    (initialPressure B N0) (positivePressure B N0 hN)

theorem potentialStages_zero (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    potentialStages B N0 hN 0 = zerothPotential B N0 := rfl

theorem potentialStages_succ (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    potentialStages B N0 hN (j + 1) = positivePotential B N0 hN j := rfl

theorem directStages_eq (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    directStages B N0 hN j = ActualCandidateConstruction.angularMeanStages B N0 j :=
  ActualCandidateConstruction.directData_field (meanCycleInput B N0 hN) j

theorem directStages_zero (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    directStages B N0 hN 0 = initialDirect B N0 := directStages_eq B N0 hN 0

theorem pressureStages_zero (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    pressureStages B N0 hN 0 = zerothPressure B N0 := rfl

theorem pressureStages_succ (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    pressureStages B N0 hN (j + 1) = positivePressure B N0 hN j := rfl

/-! ## Geometric inputs are consequences of the same constructed fields -/

theorem particular_smooth (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (particularPotential B N0 j) (ActualCandidateConstruction.physicalDomain B N0) ∧
      ContDiffOn ℝ ∞ (particularPressure B N0 j) (ActualCandidateConstruction.physicalDomain B N0)
        :=
  ActualValidBandWaves.fields_smooth
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl) le_rfl

theorem particular_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (particularPotential B N0 j) ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (particularPressure B N0 j) :=
  ActualValidBandWaves.shrinking_support
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl) le_rfl

theorem particular_axisZeroOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (particularPotential B N0 j) :=
  ActualValidBandWaves.axis_zero
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl) le_rfl

theorem particular_zero_germs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) {w : SpaceTime}
    (hw : w ∈ ActualCandidateConstruction.physicalDomain B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    (particularPotential B N0 j =ᶠ[𝓝 w] fun _ => 0) ∧
      (particularPressure B N0 j =ᶠ[𝓝 w] fun _ => 0) :=
  ActualValidBandWaves.active_zero_germs
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl) le_rfl hw he

theorem signed_zero_germs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal) (he : w ∉ ActualPolarCoverage.active) :
    (signedPotential B N0 hN j =ᶠ[𝓝 w] fun _ => 0) ∧
      (signedPressure B N0 hN j =ᶠ[𝓝 w] fun _ => 0) :=
  ActualSignedExterior.cycle_zero_germs _ _ _ ht he

theorem support_of_exterior_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} {qbig : ℝ}
    (hz : ∀ w, w ∈ PhysicalWaveSum.preterminal → w ∉ ActualPolarCoverage.active → f w = 0) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      qbig f := by
  intro w ht _ hn
  have ha : w ∈ ActualPolarCoverage.active := by
    by_contra hna
    exact hn (hz w ht hna)
  have hr := ((ActualCurrentWaveSupport.profileRadius_mem_iff_active ht).mpr ha).2.trans
    ActualCurrentWaveSupport.rightRadius_le_actualOuterConstant
  exact (div_le_iff₀ (Real.sqrt_pos.mpr
    (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht))).mp hr

theorem signed_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (signedPotential B N0 hN j) ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (signedPressure B N0 hN j) :=
  ⟨support_of_exterior_zero (fun _ ht he => (signed_zero_germs B N0 hN j ht he).1.eq_of_nhds),
    support_of_exterior_zero (fun _ ht he => (signed_zero_germs B N0 hN j ht he).2.eq_of_nhds)⟩

theorem axis_not_active {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (ha : PhysicalGraphBounds.radialProjection w = 0) : w ∉ ActualPolarCoverage.active := by
  intro hm
  have hr := ((ActualCurrentWaveSupport.profileRadius_mem_iff_active ht).mpr hm).1
  rw [ActualCurrentWaveSupport.profileRadius_zero_of_axis h ha] at hr
  exact (not_le_of_gt (PrimaryTargetBounds.leftRadius_pos nominal)) hr

theorem signed_axisZeroOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (signedPotential B N0 hN j) := by
  intro w hw ha
  exact (signed_zero_germs B N0 hN j hw.1 (axis_not_active hw.1 ha)).1

theorem positivePotential_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (positivePotential B N0 hN j) :=
  PhysicalStageSupport.support_add
    (PhysicalStageSupport.support_add (particular_support B N0 hN j).1 (signed_support B N0 hN j).1)
    (ActualCandidateConstruction.streamMeanStages_shrinkingSupport (meanCycleInput B N0 hN) (j + 1))

theorem positivePressure_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (positivePressure B N0 hN j) :=
  PhysicalStageSupport.support_add
    (PhysicalStageSupport.support_add (particular_support B N0 hN j).2 (signed_support B N0 hN j).2)
    (ActualCandidateConstruction.pressureMeanStages_shrinkingSupport (meanCycleInput B N0 hN) (j +
      1))

theorem directStages_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (directStages B N0 hN j) := by
  rw [directStages_eq]
  exact ActualCandidateConstruction.angularMeanStages_shrinkingSupport (meanCycleInput B N0 hN) j

theorem positivePotential_axisZeroOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (positivePotential B N0 hN j) :=
  ((particular_axisZeroOn B N0 hN j).add (signed_axisZeroOn B N0 hN j)).add
    (stream_axisZeroOn (meanCycleInput B N0 hN) (j + 1))

theorem positive_exterior (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) {w : SpaceTime}
    (hw : w ∈ ActualCandidateConstruction.physicalDomain B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    positivePotential B N0 hN j w = 0 ∧ positivePressure B N0 hN j w = 0 := by
  have hp := particular_zero_germs B N0 hN j hw he
  have hs := signed_zero_germs B N0 hN j hw.1 he
  constructor
  · simp only [positivePotential, Pi.add_apply, hp.1.eq_of_nhds, hs.1.eq_of_nhds,
      stream_exterior (meanCycleInput B N0 hN) (j + 1) hw.1 hw.2.le he, add_zero]
  · simp only [positivePressure, Pi.add_apply, hp.2.eq_of_nhds, hs.2.eq_of_nhds,
      meanPressure_exterior (meanCycleInput B N0 hN) (j + 1) hw.1 hw.2.le he, add_zero]

theorem exteriorStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualExteriorPrefix.ExteriorStages B (ActualCandidateConstruction.residualBand B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) := by
  have hsub {w : SpaceTime}
      (hw : w ∈ ActualExteriorPrefix.exteriorDomain (ActualCandidateConstruction.residualBand B
        N0)) :
      w ∈ ActualCandidateConstruction.physicalDomain B N0 :=
    ⟨hw.1.1, hw.2.2.trans_le (ActualPrimaryCovariance.Q_antitone
      (ActualCandidateConstruction.firstBand_le_residualBand B N0))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [potentialStages_zero]
    change _ + initialPotential B N0 w = _
    rw [initialPotential_exterior B N0 (hsub hw).1 (hsub hw).2.le hw.1.2, add_zero]
  · intro j w hw
    exact (positive_exterior B N0 hN j (hsub hw) hw.1.2).1
  · intro j w hw
    exact direct_exterior (meanCycleInput B N0 hN) j (hsub hw).1 (hsub hw).2.le hw.1.2
  · intro w hw
    rw [pressureStages_zero]
    change _ + initialPressure B N0 w = _
    rw [initialPressure_exterior B N0 (hsub hw).1 (hsub hw).2.le hw.1.2, add_zero]
  · intro j w hw
    exact (positive_exterior B N0 hN j (hsub hw) hw.1.2).2

theorem particularPotential_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (particularPotential B N0 j))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCandidateConstruction.graph n)
          ((ActualCandidateConstruction.parameters B N0).particularVelocity
            (ActualCandidateConstruction.cycle B N0 j).coefficients (commonContext B)
            (ActualCandidateConstruction.cycle B N0 j).state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  have he := ActualValidBandWaves.potential_curl_germ
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl)
    (ActualCandidateConstruction.firstBand B N0) n hn (chartDomain_band B N0 n ha i hw)
  exact he.eq_of_nhds.trans (ActualCurrentParticularAssembly.localPotential_curl_eqOn
    (ActualCyclePreservation.state_invariant B N0 hN j) hN
    (ActualCandidateConstruction.qbig B N0) n ha i hw)

theorem particularPressure_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (particularPressure B N0 j)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCandidateConstruction.graph n)
          ((ActualCandidateConstruction.parameters B N0).particularPressure
            (ActualCandidateConstruction.cycle B N0 j).coefficients (commonContext B)
            (ActualCandidateConstruction.cycle B N0 j).state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  have he := (ActualValidBandWaves.fields_eq
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j) hN
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => Subset.rfl)
    (ActualCandidateConstruction.firstBand B N0) n hn (chartDomain_band B N0 n ha i hw)).2
  exact he.trans (ActualCurrentParticularAssembly.localPressure_eqOn
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCandidateConstruction.qbig B N0) n ha i hw)

/-! ## The quantitative component record uses these exact sequences -/

theorem representations_of_signed_eqOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
    (W : GluedStageEstimates.SignedInputs D I K)
    (hA : ∀ j, EqOn (W.potential j).vector (signedPotential B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0))
    (hP : ∀ j, EqOn (W.pressure j).pressure (signedPressure B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) :
    GluedStageEstimates.ActualRepresentations (runData B N0 hN) (meanCycleInput B N0 hN)
      (ActualCandidateConstruction.firstBand_four B N0) W (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _
    rw [potentialStages_zero, zerothPotential_eq_initialPotential]
  · intro w _
    rw [directStages_zero]
    rfl
  · intro w _
    rw [pressureStages_zero, zerothPressure, initialPressure_eq_increment]
    rfl
  · intro j w hw
    rw [potentialStages_succ]
    change particularPotential B N0 j w + (W.potential j).vector w +
        ((ActualMeanPhysicalData.initialCycleData (meanCycleInput B N0 hN)).temporalFamily
          j).angularField w +
        ((ActualMeanPhysicalData.initialCycleData (meanCycleInput B N0 hN)).rankFamily
          j).angularField w = _
    erw [hA j hw, positivePotential,
      ActualCandidateConstruction.streamMeanStages_succ (meanCycleInput B N0 hN),
      ActualMeanPhysicalData.CycleData.stream_angularField]
    simp only [Pi.add_apply, add_assoc]
  · intro j w _
    rw [directStages_eq, ActualCandidateConstruction.angularMeanStages_succ (meanCycleInput B N0
      hN)]
    rfl
  · intro j w hw
    rw [pressureStages_succ]
    change particularPressure B N0 j w + (W.pressure j).pressure w +
        ((ActualMeanPhysicalData.initialCycleData (meanCycleInput B N0 hN)).pressureIncrementFamily
          j).field w = _
    rw [hP j hw, positivePressure,
      ActualCandidateConstruction.pressureMeanStages_succ (meanCycleInput B N0 hN)]
    rfl

theorem stages_smooth_of_signed_eqOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
    (W : GluedStageEstimates.SignedInputs D I K)
    (hA : ∀ j, EqOn (W.potential j).vector (signedPotential B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0))
    (hP : ∀ j, EqOn (W.pressure j).pressure (signedPressure B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) :
    (∀ j, ContDiffOn ℝ ∞ (potentialStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) ∧
    (∀ j, ContDiffOn ℝ ∞ (directStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) ∧
    (∀ j, ContDiffOn ℝ ∞ (pressureStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) := by
  have e := representations_of_signed_eqOn B N0 hN W hA hP
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact GluedStageEstimates.Representations.potential_smooth
      (runData B N0 hN) (meanCycleInput B N0 hN)
      (ActualCandidateConstruction.firstBand_four B N0) W _ _ le_rfl _ _ e
      (fun k => (particular_smooth B N0 hN k).1) j
  · intro j
    exact GluedStageEstimates.Representations.direct_smooth
      (runData B N0 hN) (meanCycleInput B N0 hN)
      (ActualCandidateConstruction.firstBand_four B N0) W _ _ le_rfl _ _ e j
  · intro j
    exact GluedStageEstimates.Representations.pressure_smooth
      (runData B N0 hN) (meanCycleInput B N0 hN)
      (ActualCandidateConstruction.firstBand_four B N0) W _ _ le_rfl _ _ e
      (fun k => (particular_smooth B N0 hN k).2) j

theorem signedPotential_eq_native (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((ActualSignedWaveData.signedInputs B N0 hN).potential j).vector
      (signedPotential B N0 hN j) PhysicalWaveSum.preterminal :=
  ActualSignedWaveData.signedInputs_potential_eq B N0 hN j

theorem signedPressure_eq_native (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn ((ActualSignedWaveData.signedInputs B N0 hN).pressure j).pressure
      (signedPressure B N0 hN j) PhysicalWaveSum.preterminal :=
  ActualSignedWaveData.signedInputs_pressure_eq B N0 hN j

theorem signedPotential_smooth (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedPotential B N0 hN j) PhysicalWaveSum.preterminal :=
  (((ActualSignedWaveData.signedInputs B N0 hN).potential j).vector_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half).congr
      (fun _ hw => (signedPotential_eq_native B N0 hN j hw).symm)

theorem signedPressure_smooth (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedPressure B N0 hN j) PhysicalWaveSum.preterminal :=
  (((ActualSignedWaveData.signedInputs B N0 hN).pressure j).pressure_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half).congr
      (fun _ hw => (signedPressure_eq_native B N0 hN j hw).symm)

theorem representations (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    GluedStageEstimates.ActualRepresentations (runData B N0 hN) (meanCycleInput B N0 hN)
      (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
      (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) :=
  representations_of_signed_eqOn B N0 hN (ActualSignedWaveData.signedInputs B N0 hN)
    (fun j _ hw => signedPotential_eq_native B N0 hN j hw.1)
    (fun j _ hw => signedPressure_eq_native B N0 hN j hw.1)

theorem stages_smooth (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    (∀ j, ContDiffOn ℝ ∞ (potentialStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) ∧
    (∀ j, ContDiffOn ℝ ∞ (directStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) ∧
    (∀ j, ContDiffOn ℝ ∞ (pressureStages B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0)) :=
  stages_smooth_of_signed_eqOn B N0 hN (ActualSignedWaveData.signedInputs B N0 hN)
    (fun j _ hw => signedPotential_eq_native B N0 hN j hw.1)
    (fun j _ hw => signedPressure_eq_native B N0 hN j hw.1)

theorem postParticular_coherent (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualCycleCoherence.StateCoherent
      (ActualParticularMeanGain.postParticular (ActualCandidateConstruction.cycle B N0 j)) :=
  ActualCycleCoherence.afterParticular_coherent
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualCyclePreservation.state_waveData B N0 hN j)
    (ActualCyclePreservation.state_coherent B N0 hN j)
    (fun n m k hi => (ActualCyclePreservation.state_wave_transport B N0 hN j n m k hi).particular)

theorem signed_amplitude_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ)
    (l : ActualInitialization.Index B N0) :
    CurrentSignedCurl.AmplitudeBound l
      (ActualParticularMeanGain.postParticular (ActualCandidateConstruction.cycle B N0 j))
      ((1 + ActualIterationLedger.sigma j - ChartScales.kappa) - 1 / 2) :=
  CurrentSignedCurl.amplitudeBound_of_mean l _ _
    (postParticularResult B N0 hN j).primitive (postParticularResult B N0 hN j).reconstructed
    (postParticularResult B N0 hN j).theta (postParticularResult B N0 hN j).axial

theorem zerothPotential_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (zerothPotential B N0))
      (ActualCandidateConstruction.chartPotentialParts B N0 a i n 0)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos
    outgoing.data.h_lt_half (ActualCandidateConstruction.qbig B N0)
  have hb : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential certificate modulation upper B)
      (ActualCandidateConstruction.physicalDomain B N0) :=
    (TailGaugePotential.finalPotential_smooth certificate modulation upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hwave : ContDiffOn ℝ ∞ (InitialPhysicalData.potential B N0)
      (ActualCandidateConstruction.physicalDomain B N0) :=
    (InitialPhysicalData.potential_smooth B N0).mono (fun _ hw => hw.1)
  have hmean := ActualCandidateConstruction.streamMeanStages_smooth (meanCycleInput B N0 hN) 0
  intro w hw
  have hi : SpatialCurl.spatialCurl (initialPotential B N0) w =
      SpatialCurl.spatialCurl (InitialPhysicalData.potential B N0) w +
        SpatialCurl.spatialCurl (ActualCandidateConstruction.streamMeanStages B N0 0) w :=
    InitializedPhysicalBackground.spatialCurl_add_on hU hwave hmean hw.1
  calc
    _ = SpatialCurl.spatialCurl (TailGaugePotential.finalPotential certificate modulation upper B)
      w +
        SpatialCurl.spatialCurl (initialPotential B N0) w :=
      InitializedPhysicalBackground.spatialCurl_add_on hU hb (initialPotential_smooth B N0) hw.1
    _ = ActualCandidateConstruction.chartBaseVelocity B a i n w +
        (ActualCandidateConstruction.chartWaveParts B N0 a i n 0 w +
          ActualCandidateConstruction.chartStreamParts B N0 a i n 0 w) := by
      rw [ActualCandidateConstruction.basePotential_curl_on_chart B ha i n hw.1.1 hw.2.1, hi,
        initialWavePotential_on_chart B N0 n ha i hw,
        stream_on_chart (meanCycleInput B N0 hN) 0 n hn ha i hw]
    _ = _ := by
      rw [ActualCandidateConstruction.chartPotentialParts_zero]
      simp only [Pi.add_apply, add_assoc]

theorem zerothPressure_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (zerothPressure B N0)
      (ActualCandidateConstruction.chartPressureStages B N0 a i n 0)
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  change FinalSlowBase.pressure certificate modulation upper B w +
    (InitialPhysicalData.pressure B N0 w +
      ActualCandidateConstruction.pressureMeanStages B N0 0 w) = _
  rw [← ActualCandidateConstruction.chartBasePressure_eq B ha i n hw.2.1,
    initialWavePressure_on_chart B N0 n ha i hw,
    meanPressure_on_chart (meanCycleInput B N0 hN) 0 n hn ha i hw,
    ActualCandidateConstruction.chartPressureParts_zero]
  simp only [Pi.add_apply, add_assoc]

theorem signedPotential_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (signedPotential B N0 hN j))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCandidateConstruction.graph n)
          ((ActualCandidateConstruction.parameters B N0).signedVelocity
            (ActualCandidateConstruction.cycle B N0 j).coefficients (commonContext B)
            (ActualCandidateConstruction.cycle B N0 j).state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) :=
  ActualSignedPhysicalCoherence.cyclePotential_curl (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure _ (postParticularResult B N0 hN
      j).primitive)
    (congrArg (fun u : CorrectionState.State ActualSignedCoherence.Point => u.pressure)
      (postParticularResult B N0 hN j).reconstructed)
    (postParticular_coherent B N0 hN j) (ActualCyclePreservation.state_coherent B N0 hN j).labels
    n (fun l _ => signed_amplitude_bound B N0 hN j l) ha i

theorem signedPressure_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (signedPressure B N0 hN j)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCandidateConstruction.graph n)
          ((ActualCandidateConstruction.parameters B N0).signedPressure
            (ActualCandidateConstruction.cycle B N0 j).coefficients (commonContext B)
            (ActualCandidateConstruction.cycle B N0 j).state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) :=
  ActualSignedPhysicalCoherence.cyclePressure_eq (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure _ (postParticularResult B N0 hN
      j).primitive)
    (congrArg (fun u : CorrectionState.State ActualSignedCoherence.Point => u.pressure)
      (postParticularResult B N0 hN j).reconstructed)
    (postParticular_coherent B N0 hN j) (ActualCyclePreservation.state_coherent B N0 hN j).labels n
      ha i

theorem positivePotential_curl (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    EqOn (SpatialCurl.spatialCurl (positivePotential B N0 hN j))
      (fun w => SpatialCurl.spatialCurl (particularPotential B N0 j) w +
        SpatialCurl.spatialCurl (signedPotential B N0 hN j) w +
        SpatialCurl.spatialCurl (ActualCandidateConstruction.streamMeanStages B N0 (j + 1)) w)
      (ActualCandidateConstruction.physicalDomain B N0) := by
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos
    outgoing.data.h_lt_half (ActualCandidateConstruction.qbig B N0)
  have hp := (particular_smooth B N0 hN j).1
  have hs : ContDiffOn ℝ ∞ (signedPotential B N0 hN j)
      (ActualCandidateConstruction.physicalDomain B N0) :=
    (signedPotential_smooth B N0 hN j).mono (fun _ hw => hw.1)
  have hm := ActualCandidateConstruction.streamMeanStages_smooth (meanCycleInput B N0 hN) (j + 1)
  intro w hw
  change SpatialCurl.spatialCurl
    (fun z => (particularPotential B N0 j z + signedPotential B N0 hN j z) +
      ActualCandidateConstruction.streamMeanStages B N0 (j + 1) z) w = _
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU (hp.add hs) hm hw]
  dsimp only
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU hp hs hw]

theorem positivePotential_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (positivePotential B N0 hN j))
      (ActualCandidateConstruction.chartPotentialParts B N0 a i n (j + 1))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  rw [positivePotential_curl B N0 hN j hw.1]
  dsimp only
  rw [particularPotential_on_chart B N0 hN j n hn ha i hw,
    signedPotential_on_chart B N0 hN j n ha i hw,
    stream_on_chart (meanCycleInput B N0 hN) (j + 1) n hn ha i hw,
    ActualCandidateConstruction.chartPotentialParts_succ]
  simp only [ActualCandidateConstruction.chartWaveParts, map_add, Pi.add_apply]

theorem positivePressure_on_chart (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n : ℕ)
    (hn : ActualCandidateConstruction.firstBand B N0 ≤ n)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (positivePressure B N0 hN j)
      (ActualCandidateConstruction.chartPressureStages B N0 a i n (j + 1))
      (ActualPhysicalPrefixFields.cartesianChartDomain
        (ActualCandidateConstruction.qbig B N0) n a i) := by
  intro w hw
  change particularPressure B N0 j w + signedPressure B N0 hN j w +
    ActualCandidateConstruction.pressureMeanStages B N0 (j + 1) w = _
  rw [particularPressure_on_chart B N0 hN j n hn ha i hw,
    signedPressure_on_chart B N0 hN j n ha i hw,
    meanPressure_on_chart (meanCycleInput B N0 hN) (j + 1) n hn ha i hw,
    ActualCandidateConstruction.chartPressureParts_succ]
  simp only [ActualCandidateConstruction.chartWavePressureParts, map_add, Pi.add_apply]

theorem stageRealizations (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualPhysicalPrefixFields.StageRealizations B N0 (ActualCandidateConstruction.residualBand B
      N0)
      (ActualCandidateConstruction.parameterSequence B N0) (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn a ha i k
    have hn' := (ActualCandidateConstruction.firstBand_le_residualBand B N0).trans hn
    cases k with
    | zero => exact zerothPotential_on_chart B N0 hN n hn' ha i
    | succ j => exact positivePotential_on_chart B N0 hN j n hn' ha i
  · intro n hn a ha i k
    exact direct_on_chart (meanCycleInput B N0 hN) k n
      ((ActualCandidateConstruction.firstBand_le_residualBand B N0).trans hn) ha i
  · intro n hn a ha i k
    have hn' := (ActualCandidateConstruction.firstBand_le_residualBand B N0).trans hn
    cases k with
    | zero => exact zerothPressure_on_chart B N0 hN n hn' ha i
    | succ j => exact positivePressure_on_chart B N0 hN j n hn' ha i

theorem physicalData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ∀ J, ActualCycleResidualBounds.PhysicalData B (ActualCandidateConstruction.residualBand B N0)
      (ActualCandidateConstruction.cycle B N0 J).state
      (MixedDiagonalResidual.uncutVelocity (potentialStages B N0 hN) (directStages B N0 hN) J)
      (DiagonalJetBounds.uncutPrefix (pressureStages B N0 hN) (J + 1)) :=
  ActualPhysicalPrefixFields.physicalFields_all (stageRealizations B N0 hN) (exteriorStages B N0 hN)
    (ActualCandidateConstruction.twice_residual_scale B N0).le
    (stages_smooth B N0 hN).1 (stages_smooth B N0 hN).2.1 (stages_smooth B N0 hN).2.2
    (ActualCandidateConstruction.cycle_representation B N0)

noncomputable def estimates (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    MixedCandidateAssembly.StageEstimates h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) :=
  GluedStageEstimates.actualStageEstimates (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
    (ActualCyclePreservation.state_coherent B N0 hN) le_rfl
    (ActualCandidateConstruction.qbig_pos B N0) hN _ _ _
    (representations B N0 hN) (physicalData B N0 hN)

theorem endpoints (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualEndpointInputs.EndpointInputs h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) := by
  apply GermEndpointInputs.actual_germ_stage_endpoints_of_estimates B N0
    (ActualCandidateConstruction.firstBand B N0) (ActualCandidateConstruction.firstBand_four B N0)
    le_rfl (initialPotential B N0) (positivePotential B N0 hN) (directData B N0 hN)
    (initialPressure B N0) (positivePressure B N0 hN) (estimates B N0 hN)
  · intro w _
    rfl
  · intro w _
    change directStages B N0 hN 0 w = _
    rw [directStages_zero]
    rfl
  · intro w _
    rfl

/-! ## The common schedule and its actual fields -/

/-- The output retains the actual three sums, the smooth force, and the
strong consequences for this same velocity and pressure. -/
def Witness (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : Prop :=
  ∃ a : ℕ → ℕ,
    MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) a ∧
    let ASum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (potentialStages B N0 hN)
    let BSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (directStages B N0 hN)
    let PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (pressureStages B N0 hN)
    ∃ (ea : JointResidualLimits.AwayExtensions ASum)
      (eb : JointResidualLimits.AwayExtensions BSum)
      (ep : JointResidualLimits.AwayExtensions PSum),
    ∃ forcing : VelocityField,
      CandidateProperties
        (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
      ContDiff ℝ ∞ forcing ∧
      CandidateConsequences.Consequences
        (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t,
          x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
      (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
          |(iteratedFDeriv ℝ m forcing (t, x)
            (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
              C * (1 + t) ^ (-K)) ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n forcing (1, x) =
        MixedPeriodicAssembly.boundaryLimits ASum BSum PSum ea eb ep x n)

theorem witness (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    Witness B N0 hN :=
  GermCandidateAssembly.exists_candidate_witness_of_finite_stages certificate modulation upper B
    (ActualCandidateConstruction.qbig_pos B N0) (initialPotential B N0) (positivePotential B N0 hN)
    (directData B N0 hN) (initialPressure B N0) (positivePressure B N0 hN) (estimates B N0 hN)
    (initialPotential_support B N0) (positivePotential_support B N0 hN) (directStages_support B N0
      hN)
    (initialPressure_support B N0) (positivePressure_support B N0 hN)
    (endpoints B N0 hN).potential (endpoints B N0 hN).direct (endpoints B N0 hN).pressure
    (initialPotential_axisZeroOn B N0) (positivePotential_axisZeroOn B N0 hN)

/-! One closed choice fixes all three raw sequences together. -/

noncomputable def selectedPotentialStages : ℕ → VelocityField :=
  potentialStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

noncomputable def selectedDirectStages : ℕ → VelocityField :=
  directStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

noncomputable def selectedPressureStages : ℕ → PressureField :=
  pressureStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

theorem selected_witness :
    Witness ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry :=
  witness ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

theorem selected_candidate : ProblemStatement.candidateStatement := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ := selected_witness
  exact ⟨_, _, forcing, hc⟩

end NavierStokes.ActualCandidateAssembly
