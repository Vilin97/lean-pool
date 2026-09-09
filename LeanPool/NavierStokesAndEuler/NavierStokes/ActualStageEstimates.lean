/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalStageBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleResidualBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIntermediateDebtBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly

@[expose] public section

/-!
# Stage estimates for the fixed actual iteration

The native step data and the actual physical field representations are
assembled into the finite-stage obligations of the mixed diagonal theorem.
No estimate of the output physical residual is an input.
-/

noncomputable section

namespace NavierStokes.ActualStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators


/-! ## Source indices do not change physical copy fields -/

/-- Add an unused tag to native source indices. The actual copies, their
carriers, and their physical fields are unchanged. -/
noncomputable def taggedSource {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K J T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K J) :
    PhysicalStageBounds.WaveData h D (T × I) K J where
  lowerRadius := W.lowerRadius
  upperRadius := W.upperRadius
  nativeWidth := W.nativeWidth
  slowBound := W.slowBound
  frequencyBound := W.frequencyBound
  alpha := W.alpha
  shift := W.shift
  harmonics := W.harmonics
  gapBound := W.gapBound
  lower_pos := W.lower_pos
  width_nonneg := W.width_nonneg
  slow_nonneg := W.slow_nonneg
  frequency_one_le := W.frequency_one_le
  strip := W.strip
  weight i := W.weight i.2
  source i := W.source i.2
  source_bounds := {
    uniform := W.source_bounds.uniform.reindex Prod.snd
    flat_geometry := W.source_bounds.flat_geometry
    weight_le := by
      obtain ⟨c, hc, hb⟩ := W.source_bounds.weight_le
      exact ⟨c, hc, fun i => hb i.2⟩
    epsilon_eq := W.source_bounds.epsilon_eq
    slow_le := W.source_bounds.slow_le }
  copies := W.copies
  cells := W.cells
  chart i := {
    sourceIndex k L := (tag, (W.chart i).sourceIndex k L)
    map := (W.chart i).map
    domain := (W.chart i).domain
    open_domain := (W.chart i).open_domain
    smooth := (W.chart i).smooth
    positive_jets := (W.chart i).positive_jets
    amplitude_eq := (W.chart i).amplitude_eq
    contains := (W.chart i).contains }
  chart_maps := W.chart_maps
  carrier := W.carrier
  support := W.support
  smooth := W.smooth
  frequencies := W.frequencies

@[simp] theorem taggedSource_vector {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K (Fin 3)) :
    (taggedSource tag W).vector = W.vector := rfl

@[simp] theorem taggedSource_pressure {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K Unit) :
    (taggedSource tag W).pressure = W.pressure := rfl

/-! ## One fixed native iteration -/

noncomputable def StepData (B N0 j : ℕ)
    (H : ActualCyclePreservation.Invariant (ActualIterationLedger.sigma j)
      (ActualCyclePreservation.state B N0 j)) : Type :=
  CorrectionAnalyticStep.StepData ActualInitialization.geometry h (CommonWindow.index h)
    ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0 l))
    ActualSignedStageControls.parameters rankData (commonContext B)
    (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
    ActualInitialization.envelope ActualCoreSupport.refinedCarrier
    (ActualCyclePreservation.staticData B) H (ActualIterationLedger.sigma_admissible j)

/-- All data refer to the same fixed parameters and actual initial state.
The step record contains native wave constructions; it is not a physical
stage-bound or residual-bound oracle. -/
structure RunData (B N0 : ℕ) where
  invariant : ∀ j, ActualCyclePreservation.Invariant (ActualIterationLedger.sigma j)
    (ActualCyclePreservation.state B N0 j)
  step : ∀ j, StepData B N0 j (invariant j)
  particular : ∀ j, ActualParticularMeanGain.Inputs (ActualCyclePreservation.state B N0 j)
    (ActualIterationLedger.sigma j)

theorem RunData.result {B N0 : ℕ} (R : RunData B N0) (j : ℕ) :
    CorrectionAnalyticStep.StepResult ActualInitialization.geometry h (CommonWindow.index h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0
        l))
      ActualSignedStageControls.parameters rankData (commonContext B)
      (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
      ActualInitialization.envelope ActualCoreSupport.refinedCarrier
      (σ := ActualIterationLedger.sigma j) (κ := ChartScales.kappa) :=
  CorrectionAnalyticStep.step _ _ _ _ _ _ _ _ _ _ _ _
    (ActualCyclePreservation.staticData B) (R.invariant j) (ActualIterationLedger.sigma_admissible
      j)
    ActualCyclePreservation.kappa_small (R.step j)

theorem RunData.rank_class {B N0 : ℕ} (R : RunData B N0) (j : ℕ) :
    WeightedClasses.UnweightedClass ActualInitialization.slowStrip
      (1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa)
      (CorrectionState.debt (commonContext B)
        (ActualIntermediateDebtBounds.postTemporal (ActualCyclePreservation.state B N0 j))) :=
  ActualIntermediateDebtBounds.afterTemporal_debt_from_stepData
    (ActualCyclePreservation.staticData B) (R.invariant j) (ActualIterationLedger.sigma_admissible
      j)
    (R.particular j) (R.step j)

theorem nativeMean_eq_ledger (j : ℕ) :
    1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa =
      ActualIterationLedger.meanNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.meanNative, ActualIterationLedger.inputSigma_succ,
    ExponentLedger.meanUpdateExponent, ExponentLedger.meanExponent]

theorem nativePotential_eq_ledger (j : ℕ) :
    1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa =
      ActualIterationLedger.waveNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.waveNative, ActualIterationLedger.inputSigma_succ,
    ExponentLedger.waveExponent]

theorem nativePressure_eq_ledger (j : ℕ) :
    1 + ActualIterationLedger.sigma j - ChartScales.kappa =
      ActualIterationLedger.wavePressureNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.wavePressureNative, ← nativePotential_eq_ledger]
  ring

variable {B N0 N : ℕ}

noncomputable def temporalInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  actualCycleTemporalInput M j hN (R.result j).afterSignedAxial

noncomputable def rankInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  actualCycleRankInput M j hN (R.rank_class j)

noncomputable def angularInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h) :=
  actualCycleAngularInput M j hN (R.result j).temporal (R.result j).rank

noncomputable def pressureInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (2 * CoordinateAlgebra.A h) :=
  actualCyclePressureInput M j hN (R.result j).pressure

/-! ## Actual wave records and their native exponents -/

structure WaveInputs (DP : Type) [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    (IP KP : Type*) (DS : Type) [NormedAddCommGroup DS] [NormedSpace ℝ DS] (IS KS : Type*) where
  particularPotential : ℕ → PhysicalStageBounds.WaveData h DP (Fin 3 × IP) KP (Fin 3)
  signedPotential : ℕ → PhysicalStageBounds.WaveData h DS (Fin 3 × IS) KS (Fin 3)
  particularPressure : ℕ → PhysicalStageBounds.WaveData h DP IP KP Unit
  signedPressure : ℕ → PhysicalStageBounds.WaveData h DS IS KS Unit
  particularPotential_exponent : ∀ j, 1/2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (particularPotential j).alpha
  signedPotential_exponent : ∀ j, 1/2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (signedPotential j).alpha
  particularPressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (particularPressure j).alpha
  signedPressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (signedPressure j).alpha
  particularPotential_shift : ∀ j, (particularPotential j).shift = -h
  signedPotential_shift : ∀ j, (signedPotential j).shift = -h
  particularPressure_shift : ∀ j, (particularPressure j).shift = -(2 * CoordinateAlgebra.A h)
  signedPressure_shift : ∀ j, (signedPressure j).shift = -(2 * CoordinateAlgebra.A h)

section CycleInputs

variable {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : WaveInputs DP IP KP DS IS KS)

noncomputable def cycleInputs : CycleInputs h DP (Fin 3 × IP) KP DS (Fin 3 × IS) KS where
  particularPotential := W.particularPotential
  signedPotential := W.signedPotential
  particularPressure j := taggedSource (0 : Fin 3) (W.particularPressure j)
  signedPressure j := taggedSource (0 : Fin 3) (W.signedPressure j)
  temporal := temporalInput R M hN
  rank := rankInput R M hN
  angular := angularInput R M hN
  pressure := pressureInput R M hN

theorem cycleInputs_potential (j : ℕ) :
    (cycleInputs R M hN W).potential j = fun w =>
      (W.particularPotential j).vector w + (W.signedPotential j).vector w +
        ((ActualMeanPhysicalData.initialCycleData M).temporalFamily j).angularField w +
        ((ActualMeanPhysicalData.initialCycleData M).rankFamily j).angularField w := rfl

theorem cycleInputs_direct (j : ℕ) :
    (cycleInputs R M hN W).direct j =
      ((ActualMeanPhysicalData.initialCycleData M).angularIncrementFamily j).angularField := rfl

theorem cycleInputs_pressure (j : ℕ) :
    (cycleInputs R M hN W).pressureField j = fun w =>
      (W.particularPressure j).pressure w + (W.signedPressure j).pressure w +
        ((ActualMeanPhysicalData.initialCycleData M).pressureIncrementFamily j).field w := rfl

theorem cycleInputs_metadata : (cycleInputs R M hN W).Metadata ChartScales.kappa := by
  constructor
  · intro j
    exact (nativePotential_eq_ledger j).symm.le.trans (W.particularPotential_exponent j)
  · intro j
    exact (W.particularPotential_shift j).ge
  · intro j
    exact (nativePotential_eq_ledger j).symm.le.trans (W.signedPotential_exponent j)
  · intro j
    exact (W.signedPotential_shift j).ge
  · intro j
    exact (nativeMean_eq_ledger j).ge
  · intro j
    exact (nativeMean_eq_ledger j).ge
  · intro j
    exact (nativeMean_eq_ledger j).ge
  · intro j
    exact (nativePressure_eq_ledger j).symm.le.trans (W.particularPressure_exponent j)
  · intro j
    exact (W.particularPressure_shift j).ge
  · intro j
    exact (nativePressure_eq_ledger j).symm.le.trans (W.signedPressure_exponent j)
  · intro j
    exact (W.signedPressure_shift j).ge
  · intro j
    exact (nativeMean_eq_ledger j).ge

theorem cycleInputs_validScale {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    (cycleInputs R M hN W).ValidScale qbig :=
  ⟨fun _ => hq, fun _ => hq, fun _ => hq, fun _ => hq⟩

end CycleInputs

/-! ## The actual finite-stage estimate record -/

/-- The initialized background loss is fixed before the number of
correction stages is chosen. -/
noncomputable def backgroundLoss (waveAlpha waveShift : ℝ) : ℕ → ℝ :=
  MixedFiniteBackground.initialBackgroundLoss
    (InitializedPhysicalBackground.initialLoss h waveAlpha waveShift
      (1 - ChartScales.kappa) (9 / 10))
    (PhysicalStageBounds.potentialLoss h h 0) (PhysicalStageBounds.directLoss h 0)

section StageEstimates

variable {DP DS DA0 DP0 : Type}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0] [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {IP KP IS KS IA0 KA0 IP0 KP0 : Type*}
  (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : WaveInputs DP IP KP DS IS KS)
  (qbig : ℝ)
  (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
  (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
  (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)

/-- Literal component identities supplied by the physical sequence
construction. These are equalities of fields on a fixed open sublevel,
and contain no bounds for physical derivatives. -/
structure Representations : Prop where
  potential_zero : EqOn (A 0)
    (initialPotential certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_zero : EqOn (Bdirect 0) (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_zero : EqOn (P 0)
    (fun w => FinalSlowBase.pressure certificate modulation upper B w +
      initialPressureIncrement WP (actualInitialPressureInput B N0 N hN) w)
    (CutStageEstimates.physicalSublevel h qbig)
  potential_succ : ∀ j, EqOn ((cycleInputs R M hN W).potential j) (A (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_succ : ∀ j, EqOn ((cycleInputs R M hN W).direct j) (Bdirect (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_succ : ∀ j, EqOn ((cycleInputs R M hN W).pressureField j) (P (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)

variable {qbig A Bdirect P}
  (e : Representations R M hN W qbig WA WP A Bdirect P)
  (hq : qbig ≤ ChartScales.Q N)

include e hq

theorem Representations.potential_smooth (j : ℕ) :
    ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact (initialPotential_smooth certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN) hq hq).congr
        (fun _ hw => e.potential_zero hw)
  | succ j =>
    exact ((cycleInputs R M hN W).potential_smooth (cycleInputs_validScale R M hN W hq)
      outgoing.data.h_pos outgoing.data.h_lt_half j).congr (fun _ hw => (e.potential_succ j
        hw).symm)

theorem Representations.direct_smooth (j : ℕ) :
    ContDiffOn ℝ ∞ (Bdirect j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact ((actualInitialAngularInput B N0 N hN).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq).congr (fun _ hw => e.direct_zero hw)
  | succ j =>
    exact ((cycleInputs R M hN W).direct_smooth (cycleInputs_validScale R M hN W hq)
      outgoing.data.h_pos outgoing.data.h_lt_half j).congr (fun _ hw => (e.direct_succ j hw).symm)

theorem Representations.pressure_smooth (j : ℕ) :
    ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    have hb : ContDiffOn ℝ ∞ (FinalSlowBase.pressure certificate modulation upper B)
        (CutStageEstimates.physicalSublevel h qbig) :=
      (FinalSlowBase.pressure_smooth certificate modulation upper B).mono
        (fun _ hw => ⟨hw.1, mem_univ _⟩)
    exact (hb.add (initialPressureIncrement_smooth WP (actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)).congr (fun _ hw => e.pressure_zero hw)
  | succ j =>
    exact ((cycleInputs R M hN W).pressure_smooth (cycleInputs_validScale R M hN W hq)
      outgoing.data.h_pos outgoing.data.h_lt_half j).congr (fun _ hw => (e.pressure_succ j hw).symm)

/-- The complete estimate record is constructed from native data and
exact physical realizations. The residual comparison floor is separate
from the mean-family floor, so it can be chosen one band larger. -/
noncomputable def stageEstimates_of_representations
    (hqbig : 0 < qbig) {Nres : ℕ} (hNres : 4 ≤ Nres)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B Nres
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let Cyc := cycleInputs R M hN W
  have hmeta := cycleInputs_metadata R M hN W
  have hscale := cycleInputs_validScale R M hN W hq
  have hraw := Cyc.represented_raw_bounds hmeta hscale outgoing.data.h_pos
    outgoing.data.h_lt_half ActualCyclePreservation.kappa_small A Bdirect P
    e.potential_succ e.direct_succ e.pressure_succ
  let CA := hraw.choose
  let CB := hraw.choose_spec.choose
  let CP := hraw.choose_spec.choose_spec.choose
  have hc := hraw.choose_spec.choose_spec.choose_spec
  refine {
    potential_smooth := e.potential_smooth R M hN W WA WP hq
    direct_smooth := e.direct_smooth R M hN W WA WP hq
    pressure_smooth := e.pressure_smooth R M hN W WA WP hq
    gain := ActualIterationLedger.gain h
    gain_zero := ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le 0
    gain_pos := fun _ hj => ActualIterationLedger.gain_pos outgoing.data.h_pos hj
    gain_mono := ActualIterationLedger.gain_monotone outgoing.data.h_pos.le
    gain_top := ActualIterationLedger.gain_tendsto_atTop outgoing.data.h_pos
    potentialLoss := PhysicalStageBounds.potentialLoss h h 0
    directLoss := PhysicalStageBounds.directLoss h 0
    pressureLoss := PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0
    potentialConstant := CA
    directConstant := CB
    pressureConstant := CP
    potentialLog := fun _ _ => 0
    directLog := fun _ _ => 0
    pressureLog := fun _ _ => 0
    potential_bound := hc.2.1
    direct_bound := hc.2.2.1
    pressure_bound := hc.2.2.2
    backgroundLoss := backgroundLoss WA.alpha WA.shift
    residualLoss := ActualCycleResidualBounds.fixedLoss
    finite_background := ?_
    finite_residual := ?_ }
  · intro J m
    have hb := background_from_representations certificate modulation Cyc hmeta hscale
      ActualCyclePreservation.kappa_small hqbig upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
      (actualInitialAngularInput B N0 N hN) hq hq hq A Bdirect
      e.potential_zero e.direct_zero e.potential_succ e.direct_succ J m
    simp only [backgroundLoss, actualInitialTemporalInput, actualInitialRankInput,
      actualInitialAngularInput, MeanInput.ofMoving, min_self] at hb ⊢
    exact hb
  · exact ActualCycleResidualBounds.finite_residual_rates hGeom hNres
      (fun _ => ActualCycleParameters.fixedParameters B N0)
      (fun J => MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
      (fun J => ActualCyclePreservation.broad_invariant (R.invariant J)) d

theorem stageEstimates_ledger
    (hqbig : 0 < qbig) {Nres : ℕ} (hNres : 4 ≤ Nres)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B Nres
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    let E := stageEstimates_of_representations R M hN W WA WP e hq hqbig hNres hGeom d
    E.gain = ActualIterationLedger.gain h ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = backgroundLoss WA.alpha WA.shift ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end StageEstimates

end NavierStokes.ActualStageEstimates
