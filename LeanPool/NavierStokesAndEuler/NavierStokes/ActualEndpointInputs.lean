/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OffplaneJetExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanStageData
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailGaugePotential
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBaseEndpoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualStageEstimates

@[expose] public section

/-!
# Endpoint inputs for the actual raw candidate stages

Positive stages use their already proved raw estimates.  Stage zero uses
the actual initial mean families and the existing extensions of the same
base potential and pressure.  No output extension is an input below.
-/

noncomputable section

namespace NavierStokes.ActualEndpointInputs

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

universe u

/-- The three off-plane endpoint obligations of `candidate_of_finite_stages`.
This is an output package; the construction below does not assume its fields. -/
structure EndpointInputs (h qbig : ℝ) (A V : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (A j) x)
  direct : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (V j) x)
  pressure : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (P j) x)

section InitialModels

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The exact base and bounded finite initial potential correction. -/
noncomputable def initialPotentialModel (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3)) : VelocityField :=
  ActualPhysicalStageBounds.initialPotential certificate modulation upper B WA
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)

noncomputable def initialDirectModel (B N0 N : ℕ) : VelocityField :=
  (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField

/-- The pressure of the same summed base and the actual finite initial
wave and mean-pressure correction. -/
noncomputable def initialPressureModel (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit) : PressureField :=
  fun w => FinalSlowBase.pressure certificate modulation upper B w +
    ActualPhysicalStageBounds.initialPressureIncrement WP
      (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN) w

theorem initialPotentialModel_eq (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3)) (w : SpaceTime) :
    initialPotentialModel B N0 N hN WA w =
      TailGaugePotential.finalPotential certificate modulation upper B w +
        (WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  change _ + (WA.vector w + (ActualMeanPhysicalData.initialTemporalFamily B N0 N).angularField w +
    (ActualMeanPhysicalData.initialRankFamily B N0 N).angularField w) = _
  rw [ActualMeanPhysicalData.initialStream_angularField]
  simp only [Pi.add_apply]
  abel

theorem initialPressureModel_eq (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit) (w : SpaceTime) :
    initialPressureModel B N0 N hN WP w =
      FinalSlowBase.pressure certificate modulation upper B w +
        (WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) := rfl

theorem initialPotentialModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPotentialModel B N0 N hN WA) x) := by
  have hx0 : x ≠ 0 := by intro he; exact hx (by simp [he])
  have hb := TailGaugePotential.finalPotential_awayExtensions certificate modulation upper B x hx0
  have hi := OffplaneJetExtensions.initialIncrement_extension WA
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hq hx hqx
  exact OffplaneJetExtensions.extension_add hb hi

theorem initialDirectModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialDirectModel B N0 N) x) :=
  OffplaneJetExtensions.mean_angular_extension
    (ActualPhysicalStageBounds.actualInitialAngularInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hx hqx

theorem initialPressureModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPressureModel B N0 N hN WP) x) := by
  have hb : Nonempty (JointResidualLimits.OneSidedExtension
      (FinalSlowBase.pressure certificate modulation upper B) x) :=
    ⟨SlowBaseEndpoint.finalPressureNonzeroAxial certificate modulation upper B hx⟩
  have hi := OffplaneJetExtensions.initialPressureIncrement_extension WP
    (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hx hqx
  exact OffplaneJetExtensions.extension_add hb hi

end InitialModels

section RawFamilies

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The physical bounds and exact initial representations supply all
three endpoint inputs, including index zero.  No extension or endpoint
limit is assumed for any raw stage. -/
theorem endpointInputs_of_representations (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : MixedCandidateAssembly.StageEstimates h qbig A V P)
    (hA : EqOn (A 0) (initialPotentialModel B N0 N hN WA) (CutStageEstimates.physicalSublevel h
      qbig))
    (hV : EqOn (V 0) (initialDirectModel B N0 N) (CutStageEstimates.physicalSublevel h qbig))
    (hP : EqOn (P 0) (initialPressureModel B N0 N hN WP) (CutStageEstimates.physicalSublevel h
      qbig)) :
    EndpointInputs h qbig A V P := by
  have hq1 := hq.trans (ChartScales.Q_le_one N)
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          hA hx hqx (initialPotentialModel_extension B N0 N hN WA hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          E.potential_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.potential_smooth (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          hV hx hqx (initialDirectModel_extension B N0 N hN hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          E.direct_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.direct_smooth (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          hP hx hqx (initialPressureModel_extension B N0 N hN WP hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          E.pressure_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.pressure_smooth (j + 1)) hx hqx

/-- Application to the literal raw families expected by
`MixedCandidateAssembly.candidate_of_finite_stages`. The remaining
equalities identify the produced physical fields, not their endpoint jets. -/
theorem actual_stage_endpoints (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (initial : MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h
      qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h
      qbig))
    (direct : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates h qbig
      (MixedCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries direct)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages))
    (hInitial : EqOn initial.field
      (fun w => WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries direct 0) (initialDirectModel B N0 N)
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig)) :
    EndpointInputs h qbig
      (MixedCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries direct)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  refine endpointInputs_of_representations B N0 N hN hq WA WP E ?_ hDirect ?_
  · intro w hw
    change TailGaugePotential.finalPotential certificate modulation upper B w + initial.field w = _
    rw [initialPotentialModel_eq]
    exact congrArg (fun z => TailGaugePotential.finalPotential certificate modulation upper B w +
      z) (hInitial hw)
  · intro w hw
    rw [MixedCandidateAssembly.pressureStages_zero, initialPressureModel_eq]
    exact congrArg (fun z => FinalSlowBase.pressure certificate modulation upper B w + z)
      (hPressure hw)

/-- The chosen direct angular constructor supplies its stage-zero
representation by its proved global field identity. -/
theorem direct_initial_representation (B N0 N : ℕ) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (direct : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (hDirect : direct 0 = ActualMeanStageData.initialAngularData B N0 N qbig hq) :
    LocalAngularDiagonal.rawSeries direct 0 = initialDirectModel B N0 N := by
  rw [LocalAngularDiagonal.rawSeries_eq, hDirect, ActualMeanStageData.initialAngularData_field]
  rfl

end RawFamilies

section ActualRun

variable {B N0 N : ℕ}
  {DP DS DA0 DP0 : Type}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {IP KP IS KS IA0 KA0 IP0 KP0 : Type*}

/-- Direct application to the fixed actual run. Native wave and mean data
and their exact physical representations already imply the endpoint
inputs; no finite-residual estimate or completed `StageEstimates` record
is required for this conclusion. -/
theorem endpointInputs_of_run
    (R : ActualStageEstimates.RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N)
    (W : ActualStageEstimates.WaveInputs DP IP KP DS IS KS)
    (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
    (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
    {qbig : ℝ} {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    (e : ActualStageEstimates.Representations R M hN W qbig WA WP A V P)
    (hq : qbig ≤ ChartScales.Q N) : EndpointInputs h qbig A V P := by
  let Cyc := ActualStageEstimates.cycleInputs R M hN W
  obtain ⟨CA, CV, CP, _, ha, hv, hp⟩ :=
    ActualPhysicalStageBounds.CycleInputs.represented_raw_bounds Cyc
      (ActualStageEstimates.cycleInputs_metadata R M hN W)
      (ActualStageEstimates.cycleInputs_validScale R M hN W hq)
      outgoing.data.h_pos outgoing.data.h_lt_half ActualCyclePreservation.kappa_small
      A V P e.potential_succ e.direct_succ e.pressure_succ
  have hsA := e.potential_smooth R M hN W WA WP hq
  have hsV := e.direct_smooth R M hN W WA WP hq
  have hsP := e.pressure_smooth R M hN W WA WP hq
  have hq1 := hq.trans (ChartScales.Q_le_one N)
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          e.potential_zero hx hqx (initialPotentialModel_extension B N0 N hN WA hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          ha (Nat.succ_le_succ (Nat.zero_le j)) (hsA (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          e.direct_zero hx hqx (initialDirectModel_extension B N0 N hN hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          hv (Nat.succ_le_succ (Nat.zero_le j)) (hsV (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos
          outgoing.data.h_lt_half
          e.pressure_zero hx hqx (initialPressureModel_extension B N0 N hN WP hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half
          hq1
          hp (Nat.succ_le_succ (Nat.zero_le j)) (hsP (j + 1)) hx hqx

end ActualRun

end NavierStokes.ActualEndpointInputs
