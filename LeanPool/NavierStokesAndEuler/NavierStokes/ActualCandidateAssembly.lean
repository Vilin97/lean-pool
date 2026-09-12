/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedWaveData
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentSignedCurl
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentWaveSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanStageData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalPrefixFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData
import LeanPool.NavierStokesAndEuler.NavierStokes.OffplaneJetExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialMeanEquation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger

/-!
# Literal physical data for the actual candidate

The initial fields use the same primary choice and the same initialized
mean state as `ActualCandidateConstruction`.  Their support, smoothness,
and axis germs are derived from those constructors.
-/

section

/-!
# The same initialized correction sequence and its physical prefixes

Every state below comes from the actual initialized primary choice and the
fixed actual cycle parameters. The finite labels, phase carriers, base error,
and current pressure alias are retained through the literal recurrence.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCandidateConstruction

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep
open CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology BigOperators

universe u

/-- Index: an abbreviation for `ActualInitialization.Index`. -/
abbrev Index := ActualInitialization.Index
/-- Point: an abbreviation for `CorrectionStep.CyclePoint`. -/
abbrev Point := CorrectionStep.CyclePoint
/-- Full: an abbreviation for `Point × ℝ`. -/
abbrev Full := Point × ℝ

/-- Parameters, given by `ActualCycleParameters.fixedParameters B N0`. -/
noncomputable def parameters (B N0 : ℕ) : CycleParameters (Index B N0) :=
  ActualCycleParameters.fixedParameters B N0

/-- Parameter sequence, defined pointwise by `parameters B N0`. -/
noncomputable def parameterSequence (B N0 : ℕ) : ℕ → CycleParameters (Index B N0) :=
  fun _ => parameters B N0

/-- Cycle, given by `CycleState.iterate (parameterSequence B N0) (commonContext B)
(ActualInitialization.initialCycleState B N0)`. -/
noncomputable def cycle (B N0 : ℕ) : ℕ → CycleState (Index B N0) :=
  CycleState.iterate (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0)

@[simp] theorem cycle_zero (B N0 : ℕ) :
    cycle B N0 0 = ActualInitialization.initialCycleState B N0 := rfl

theorem cycle_succ (B N0 j : ℕ) :
    cycle B N0 (j + 1) = (cycle B N0 j).step (parameters B N0) (commonContext B) := rfl

theorem cycle_labels (B N0 j : ℕ) :
    (cycle B N0 j).coefficients.labels = activeLabels standardRegion B N0 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem cycle_aliasCoefficients (B N0 j : ℕ) :
    (cycle B N0 j).coefficients.aliasCoefficients = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem cycle_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l) (ActualInitialization.tangentBlock l) := by
  induction j with
  | zero => exact ActualInitialization.primary_tangent_carrier l
  | succ j ih => exact ⟨ih.frequency, ih.phase, ih.angular⟩

/-- Recomputing the actual constructor at this state selects precisely
the fixed parameters used by the recurrence. -/
theorem current_parameters (B N0 j : ℕ) :
    ActualCycleParameters.parameters (cycle B N0 j) = parameters B N0 :=
  ActualCycleParameters.parameters_eq_fixed _ (cycle_carrier B N0 j)

theorem cycle_signed_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l)
      ((parameters B N0).signedBlock (cycle B N0 j).coefficients (commonContext B)
        (cycle B N0 j).state l) :=
  ActualCycleParameters.fixedParameters_signed_carrier _ _ l (cycle_carrier B N0 j l)

theorem cycle_representation (B N0 j : ℕ) :
    CycleRepresentation (cycle B N0 j).coefficients (cycle B N0 j).state
      (cycle B N0 j).axisymmetricAlias :=
  CycleState.iterate_representation (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0)
        (ActualInitialization.initialCycleState_represents B N0)
    (cycle_signed_carrier B N0) j

theorem cycle_coefficientBands (B N0 j : ℕ) :
    CoefficientBands (cycle B N0 j).coefficients :=
  CycleState.iterate_bands (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) (ActualInitialization.coefficients_band B N0) j

theorem cycle_residualBand (B N0 j : ℕ) :
    (cycle B N0 j).coefficients.residualBand = 2 ^ (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change 2 * max (cycle B N0 j).coefficients.residualBand 1 = 2 ^ (j + 1 + 1)
      have hp : 1 ≤ (2 : ℕ) ^ (j + 1) := Nat.succ_le_iff.mpr (by positivity)
      rw [ih, max_eq_left hp]
      simp only [pow_succ]
      ring

theorem cycle_base_error (B N0 j : ℕ) :
    (cycle B N0 j).state.errors.base = ActualInitialization.baseError B := by
  induction j with
  | zero => exact (ActualInitialization.initialState_error_components B N0).1
  | succ j ih =>
      change ((parameters B N0).next (cycle B N0 j).coefficients (commonContext B)
        (cycle B N0 j).state).errors.base = _
      rw [CycleParameters.next_base_error]
      exact ih

theorem cycle_reconstructed (B N0 j : ℕ) :
    (VariableGaugeMean.reconstructState commonGauge (commonContext B) (cycle B N0
        j).state).pressure =
      (cycle B N0 j).state.pressure := by
  cases j with
  | zero => exact congrArg State.pressure (ActualInitialization.initialState_reconstructed B N0)
  | succ j =>
      exact (parameters B N0).next_reconstructed (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state

/-- Initial temporal alias, constructed using `VariableGaugeMean.temporalAliasState`. -/
noncomputable def initialTemporalAlias (B N0 : ℕ) : Oscillation Point :=
  VariableGaugeMean.temporalAliasState commonGauge h (CorrectionInitialization.CommonWindow.index h)
    (commonContext B) (ActualInitialization.primaryState B N0)

/-- Temporal alias, given by `CycleStateCoherence.temporalAliasAt (parameterSequence B N0)
(commonContext B) (ActualInitialization.initialCycleState B N0) j`. -/
noncomputable def temporalAlias (B N0 j : ℕ) : Oscillation Point :=
  CycleStateCoherence.temporalAliasAt (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) j

/-- Every earlier temporal alias and exactly the current pressure alias
remain present, with the signs inherited from the actual state updates. -/
theorem cycle_alias_error (B N0 J : ℕ) :
    (cycle B N0 J).state.errors.aliasError = initialTemporalAlias B N0 +
      (∑ j ∈ Finset.range J, temporalAlias B N0 j) +
        VariableGaugeMean.pressureAliasState commonGauge (commonContext B) (cycle B N0 J).state :=
            by
  apply CycleStateCoherence.iterate_alias_separated (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) commonGauge (fun _ => rfl)
    (initialTemporalAlias B N0)
  exact (ActualInitialization.initialState_error_components B N0).2.2

/-- One positive band floor is retained for every physical stage. -/
noncomputable def firstBand (B N0 : ℕ) : ℕ := max 4 (ActualCycleParameters.bandFloor B N0)

theorem firstBand_four (B N0 : ℕ) : 4 ≤ firstBand B N0 := le_max_left _ _

theorem firstBand_pos (B N0 : ℕ) : 1 ≤ firstBand B N0 :=
  (by norm_num : 1 ≤ (4 : ℕ)).trans (firstBand_four B N0)

theorem firstBand_ge_choice (B N0 : ℕ) :
    ActualCycleParameters.bandFloor B N0 ≤ firstBand B N0 := le_max_right _ _

theorem firstBand_ge (B N0 : ℕ) : N0 ≤ firstBand B N0 :=
  (ActualCycleParameters.bandFloor_ge B N0).trans (firstBand_ge_choice B N0)

/-- Qbig, given by `ChartScales.Q (firstBand B N0)`. -/
noncomputable def qbig (B N0 : ℕ) : ℝ := ChartScales.Q (firstBand B N0)

theorem qbig_pos (B N0 : ℕ) : 0 < qbig B N0 := ChartScales.Q_pos _

theorem qbig_le_choice (B N0 : ℕ) :
    qbig B N0 ≤ ChartScales.Q (ActualCycleParameters.bandFloor B N0) :=
  ActualPrimaryCovariance.Q_antitone (firstBand_ge_choice B N0)

/-- One extra comparison band keeps every native point with `q/Q < 2`
inside the original raw field's validity domain. -/
noncomputable def residualBand (B N0 : ℕ) : ℕ := firstBand B N0 + 1

theorem residualBand_four (B N0 : ℕ) : 4 ≤ residualBand B N0 :=
  (firstBand_four B N0).trans (Nat.le_succ _)

theorem firstBand_le_residualBand (B N0 : ℕ) : firstBand B N0 ≤ residualBand B N0 := Nat.le_succ _

theorem twice_residual_scale (B N0 : ℕ) :
    2 * ChartScales.Q (residualBand B N0) = qbig B N0 := by
  change 2 * (2 : ℝ) ^ (-((firstBand B N0 + 1 : ℕ) : ℝ)) =
    (2 : ℝ) ^ (-(firstBand B N0 : ℝ))
  rw [Nat.cast_add, Nat.cast_one, neg_add,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
  ring

theorem nativeScale_lt_qbig (B N0 n : ℕ) (hn : residualBand B N0 ≤ n)
    {r : ℝ} (hr : r < 2) : ChartScales.Q n * r < qbig B N0 := by
  calc
    ChartScales.Q n * r < ChartScales.Q n * 2 :=
      mul_lt_mul_of_pos_left hr (ChartScales.Q_pos n)
    _ ≤ ChartScales.Q (residualBand B N0) * 2 :=
      mul_le_mul_of_nonneg_right (ActualPrimaryCovariance.Q_antitone hn) (by norm_num)
    _ = qbig B N0 := by rw [mul_comm, twice_residual_scale]

/-- Physical domain, given by `CutStageEstimates.physicalSublevel h (qbig B N0)`. -/
noncomputable def physicalDomain (B N0 : ℕ) : Set SpaceTime :=
  CutStageEstimates.physicalSublevel h (qbig B N0)

theorem physicalDomain_open (B N0 : ℕ) : IsOpen (physicalDomain B N0) :=
  CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half _

theorem initial_invariant (B N0 : ℕ) :
    CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      (ActualInitialization.tangentBlock (B := B) (N0 := N0))
      ActualInitialization.envelope ActualInitialization.labelCarrier
      (ActualIterationLedger.sigma 0) (cycle B N0 0) := by
  simp only [ActualIterationLedger.sigma_zero]
  exact ActualInitialization.initial_invariant B N0

/-! ## One selected initialization -/

/-- Selected budget, given by `0`. -/
noncomputable def selectedBudget : ℕ := 0

/-- Selected threshold, given by `ActualCarrierGeometry.startingThreshold 0`. -/
noncomputable def selectedThreshold : ℕ := ActualCarrierGeometry.startingThreshold 0

theorem selectedThreshold_geometry : ActualCarrierGeometry.geometricThreshold ≤ selectedThreshold :=
  ActualCarrierGeometry.geometricThreshold_le_startingThreshold 0

/-- Selected cycle, given by `cycle selectedBudget selectedThreshold`. -/
noncomputable def selectedCycle : ℕ → CycleState (Index selectedBudget selectedThreshold) :=
  cycle selectedBudget selectedThreshold

/-- Selected qbig, given by `qbig selectedBudget selectedThreshold`. -/
noncomputable def selectedQbig : ℝ := qbig selectedBudget selectedThreshold

theorem selectedQbig_pos : 0 < selectedQbig := qbig_pos _ _

theorem selected_initial_invariant :
    CycleAnalyticInvariant ActualInitialization.geometry (commonContext selectedBudget)
      (ActualInitialization.tangentBlock (B := selectedBudget) (N0 := selectedThreshold))
      ActualInitialization.envelope ActualInitialization.labelCarrier
      (ActualIterationLedger.sigma 0) (selectedCycle 0) := initial_invariant _ _

theorem selected_initial_meanHypotheses :
    LiftedMeanResidual.MeanHypotheses ActualInitialMeanEquation.strip.domain
      (commonContext selectedBudget) (selectedCycle 0).state :=
  ActualInitialMeanEquation.initialized_meanHypotheses _ _

/-! ## Exact finite physical prefixes in any valid polar chart -/

/-- Graph, given by `PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
(CorrectionInitialization.CommonWindow.index h n)`. -/
noncomputable def graph (n : ℕ) : PhysicalResidualBridge.ScaledGraph :=
  PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
      (CorrectionInitialization.CommonWindow.index h n)

/-- Base pressure, given by `ActualBaseResidual.basePressure certificate modulation upper B n`. -/
noncomputable def basePressure (B n : ℕ) : Full → ℝ :=
  ActualBaseResidual.basePressure certificate modulation upper B n

/-- Chart velocity, given by `CyclePhysicalPrefixes.velocity a i (graph n) n (commonContext B)
(cycle B N0 j).state`. -/
noncomputable def chartVelocity (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n j : ℕ) :
    VelocityField :=
  CyclePhysicalPrefixes.velocity a i (graph n) n (commonContext B) (cycle B N0 j).state

/-- Chart pressure, given by `CyclePhysicalPrefixes.pressure a i (graph n) n (basePressure B n)
(cycle B N0 j).state`. -/
noncomputable def chartPressure (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n j : ℕ) :
    PressureField :=
  CyclePhysicalPrefixes.pressure a i (graph n) n (basePressure B n) (cycle B N0 j).state

/-- Chart velocity stages, constructed using `CyclePhysicalPrefixes.velocityStages`. -/
noncomputable def chartVelocityStages (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ →
    VelocityField :=
  CyclePhysicalPrefixes.velocityStages (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n

/-- Chart pressure stages, constructed using `CyclePhysicalPrefixes.pressureStages`. -/
noncomputable def chartPressureStages (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ →
    PressureField :=
  CyclePhysicalPrefixes.pressureStages (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n (basePressure B n)

/-- Chart potential parts, constructed using `CyclePhysicalPrefixes.potentialParts`. -/
noncomputable def chartPotentialParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ →
    VelocityField :=
  CyclePhysicalPrefixes.potentialParts (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n

/-- Chart direct stages, constructed using `CyclePhysicalPrefixes.directStages`. -/
noncomputable def chartDirectStages (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ →
    VelocityField :=
  CyclePhysicalPrefixes.directStages (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n

theorem chart_velocity_prefix (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n J : ℕ) :
    DiagonalJetBounds.uncutPrefix (chartVelocityStages B N0 a i n) (J + 1) =
      chartVelocity B N0 a i n J :=
  CyclePhysicalPrefixes.velocity_prefix (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n J

theorem chart_pressure_prefix (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n J : ℕ) :
    DiagonalJetBounds.uncutPrefix (chartPressureStages B N0 a i n) (J + 1) =
      chartPressure B N0 a i n J :=
  CyclePhysicalPrefixes.pressure_prefix (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n (basePressure B n) J

theorem chart_velocity_split (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n j : ℕ) :
    chartVelocityStages B N0 a i n j =
      chartPotentialParts B N0 a i n j + chartDirectStages B N0 a i n j :=
  CyclePhysicalPrefixes.velocityStages_split (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n j

/-! The global physical representatives need only agree with an individual
chart on its open validity set. Finite summation and the genuine residual
preserve precisely this local agreement. -/

theorem uncutPrefix_eqOn {V : Type*} [NormedAddCommGroup V]
    {U : Set SpaceTime} {f g : ℕ → SpaceTime → V}
    (hf : ∀ j, EqOn (f j) (g j) U) (N : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix f N) (DiagonalJetBounds.uncutPrefix g N) U := by
  intro z hz
  exact Finset.sum_congr rfl (fun j _ => hf j hz)

theorem chart_velocity_of_stage_realizations (B N0 : ℕ) (a : ℝ)
    (i : PolarCharts.Index) (n : ℕ) {U : Set SpaceTime} (hU : IsOpen U)
    (AP BP : ℕ → VelocityField) (hA : ∀ k, DifferentiableOn ℝ (AP k) U)
    (hcurl : ∀ k, EqOn (SpatialCurl.spatialCurl (AP k))
      (chartPotentialParts B N0 a i n k) U)
    (hB : ∀ k, EqOn (BP k) (chartDirectStages B N0 a i n k) U) (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity AP BP J) (chartVelocity B N0 a i n J) U := by
  intro z hz
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix AP (J + 1)) z +
    DiagonalJetBounds.uncutPrefix BP (J + 1) z = _
  rw [uncutPrefix_eqOn hB (J + 1) hz]
  exact CyclePhysicalPrefixes.mixedVelocity_prefix (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n hU AP hA hcurl J hz

theorem chart_pressure_of_stage_realizations (B N0 : ℕ) (a : ℝ)
    (i : PolarCharts.Index) (n : ℕ) {U : Set SpaceTime} (PP : ℕ → PressureField)
    (hP : ∀ k, EqOn (PP k) (chartPressureStages B N0 a i n k) U) (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix PP (J + 1)) (chartPressure B N0 a i n J) U := by
  rw [← chart_pressure_prefix B N0 a i n J]
  exact uncutPrefix_eqOn hP (J + 1)

theorem chart_residual_of_stage_realizations (B N0 : ℕ) (a : ℝ)
    (i : PolarCharts.Index) (n : ℕ) {U : Set SpaceTime} (hU : IsOpen U)
    (AP BP : ℕ → VelocityField) (PP : ℕ → PressureField)
    (hA : ∀ k, DifferentiableOn ℝ (AP k) U)
    (hcurl : ∀ k, EqOn (SpatialCurl.spatialCurl (AP k))
      (chartPotentialParts B N0 a i n k) U)
    (hB : ∀ k, EqOn (BP k) (chartDirectStages B N0 a i n k) U)
    (hP : ∀ k, EqOn (PP k) (chartPressureStages B N0 a i n k) U) (J : ℕ) :
    EqOn (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity AP BP J)
      (DiagonalJetBounds.uncutPrefix PP (J + 1)) z.1 z.2)
      (fun z => navierStokesResidual (chartVelocity B N0 a i n J)
        (chartPressure B N0 a i n J) z.1 z.2) U := by
  intro z hz
  apply ResidualRegularity.residual_congr
  · exact eventually_of_mem (hU.mem_nhds hz) (fun _ hy =>
      chart_velocity_of_stage_realizations B N0 a i n hU AP BP hA hcurl hB J hy)
  · exact eventually_of_mem (hU.mem_nhds hz) (fun _ hy =>
      chart_pressure_of_stage_realizations B N0 a i n PP hP J hy)

theorem chart_residual_jets_of_stage_realizations (B N0 : ℕ) (a : ℝ)
    (i : PolarCharts.Index) (n : ℕ) {U : Set SpaceTime} (hU : IsOpen U)
    (AP BP : ℕ → VelocityField) (PP : ℕ → PressureField)
    (hA : ∀ k, DifferentiableOn ℝ (AP k) U)
    (hcurl : ∀ k, EqOn (SpatialCurl.spatialCurl (AP k))
      (chartPotentialParts B N0 a i n k) U)
    (hB : ∀ k, EqOn (BP k) (chartDirectStages B N0 a i n k) U)
    (hP : ∀ k, EqOn (PP k) (chartPressureStages B N0 a i n k) U) (J m : ℕ) :
    EqOn (iteratedFDeriv ℝ m (fun z =>
      navierStokesResidual (MixedDiagonalResidual.uncutVelocity AP BP J)
        (DiagonalJetBounds.uncutPrefix PP (J + 1)) z.1 z.2))
      (iteratedFDeriv ℝ m (fun z => navierStokesResidual (chartVelocity B N0 a i n J)
        (chartPressure B N0 a i n J) z.1 z.2)) U := by
  intro z hz
  exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (eventually_of_mem (hU.mem_nhds hz) (fun _ hy =>
      chart_residual_of_stage_realizations B N0 a i n hU AP BP PP hA hcurl hB hP J hy))
    m).self_of_nhds

/-! ## The actual mean fields, with one common physical representative

The selector defining this atlas depends on the physical point and the
fixed validity strip. It is independent of the scalar being represented.
Consequently sums and differences retain the original absolute mean and
pressure; no new integration constant or choice enters a later stage. -/

/-- Mean atlas, given by `ActualMeanPhysicalData.initialAtlas (firstBand B N0)`. -/
noncomputable def meanAtlas (B N0 : ℕ) :=
  ActualMeanPhysicalData.initialAtlas (firstBand B N0)

/-- Mean field, given by `(meanAtlas B N0).physical standardRegion.carrier degree f ∘
PhysicalMeanJetBounds.physicalPoint h`. -/
noncomputable def meanField (B N0 : ℕ) (degree : ℝ)
    (f : ActualMeanPhysicalData.Scalar) : PressureField :=
  (meanAtlas B N0).physical standardRegion.carrier degree f ∘
    PhysicalMeanJetBounds.physicalPoint h

/-- Mean angular field, defined pointwise by `meanField B N0 degree f w •
PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w)`. -/
noncomputable def meanAngularField (B N0 : ℕ) (degree : ℝ)
    (f : ActualMeanPhysicalData.Scalar) : VelocityField :=
  fun w => meanField B N0 degree f w •
    PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w)

theorem meanField_add (B N0 : ℕ) (degree : ℝ) (f g : ActualMeanPhysicalData.Scalar) :
    meanField B N0 degree (f + g) = meanField B N0 degree f + meanField B N0 degree g := by
  funext w
  exact congrFun ((meanAtlas B N0).physical_add standardRegion.carrier degree f g)
    (PhysicalMeanJetBounds.physicalPoint h w)

theorem meanField_sub (B N0 : ℕ) (degree : ℝ) (f g : ActualMeanPhysicalData.Scalar) :
    meanField B N0 degree (f - g) = meanField B N0 degree f - meanField B N0 degree g := by
  funext w
  exact congrFun ((meanAtlas B N0).physical_sub standardRegion.carrier degree f g)
    (PhysicalMeanJetBounds.physicalPoint h w)

theorem meanAngularField_add (B N0 : ℕ) (degree : ℝ) (f g : ActualMeanPhysicalData.Scalar) :
    meanAngularField B N0 degree (f + g) =
      meanAngularField B N0 degree f + meanAngularField B N0 degree g := by
  funext w
  simp only [meanAngularField, meanField_add, Pi.add_apply, add_smul]

theorem meanAngularField_sub (B N0 : ℕ) (degree : ℝ) (f g : ActualMeanPhysicalData.Scalar) :
    meanAngularField B N0 degree (f - g) =
      meanAngularField B N0 degree f - meanAngularField B N0 degree g := by
  funext w
  simp only [meanAngularField, meanField_sub, Pi.sub_apply, sub_smul]

/-- Angular native stages as an element of `ℕ → ActualMeanPhysicalData.Scalar`. -/
noncomputable def angularNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k (cycle B N0 0).state.mean.angular
    (fun j => (cycle B N0 (j + 1)).state.mean.angular - (cycle B N0 j).state.mean.angular)

/-- Pressure native stages, defined pointwise by `Nat.casesOn k (cycle B N0 0).state.pressure
(fun j => (cycle B N0 (j + 1)).state.pressure - (cycle B N0 j).state.pressure)`. -/
noncomputable def pressureNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k (cycle B N0 0).state.pressure
    (fun j => (cycle B N0 (j + 1)).state.pressure - (cycle B N0 j).state.pressure)

/-- Angular mean stages, defined pointwise by `meanAngularField B N0 (CoordinateAlgebra.A h)
(angularNativeStages B N0 j)`. -/
noncomputable def angularMeanStages (B N0 : ℕ) : ℕ → VelocityField :=
  fun j => meanAngularField B N0 (CoordinateAlgebra.A h) (angularNativeStages B N0 j)

/-- Pressure mean stages, defined pointwise by `meanField B N0 (2 * CoordinateAlgebra.A h)
(pressureNativeStages B N0 j)`. -/
noncomputable def pressureMeanStages (B N0 : ℕ) : ℕ → PressureField :=
  fun j => meanField B N0 (2 * CoordinateAlgebra.A h) (pressureNativeStages B N0 j)

theorem angularNativeStages_succ (B N0 j : ℕ) :
    angularNativeStages B N0 (j + 1) =
      ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).angular +
      ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).angular := by
  change ((parameters B N0).next (cycle B N0 j).coefficients
    (commonContext B) (cycle B N0 j).state).mean.angular -
      (cycle B N0 j).state.mean.angular = _
  rw [CycleParameters.next_mean]
  change (_ + _) + _ - _ = _
  abel

theorem uncutPrefix_succ {V : Type*} [NormedAddCommGroup V]
    (f : ℕ → SpaceTime → V) (N : ℕ) :
    DiagonalJetBounds.uncutPrefix f (N + 1) = DiagonalJetBounds.uncutPrefix f N + f N := by
  funext w
  exact Finset.sum_range_succ (fun j => f j w) N

theorem angularMeanStages_prefix (B N0 J : ℕ) :
    DiagonalJetBounds.uncutPrefix (angularMeanStages B N0) (J + 1) =
      meanAngularField B N0 (CoordinateAlgebra.A h) (cycle B N0 J).state.mean.angular := by
  induction J with
  | zero =>
      funext w
      simp [DiagonalJetBounds.uncutPrefix, angularMeanStages, angularNativeStages]
  | succ J ih =>
      rw [uncutPrefix_succ, ih]
      change _ + meanAngularField B N0 (CoordinateAlgebra.A h)
        ((cycle B N0 (J + 1)).state.mean.angular - (cycle B N0 J).state.mean.angular) = _
      rw [meanAngularField_sub]
      abel

theorem pressureMeanStages_prefix (B N0 J : ℕ) :
    DiagonalJetBounds.uncutPrefix (pressureMeanStages B N0) (J + 1) =
      meanField B N0 (2 * CoordinateAlgebra.A h) (cycle B N0 J).state.pressure := by
  induction J with
  | zero =>
      funext w
      simp [DiagonalJetBounds.uncutPrefix, pressureMeanStages, pressureNativeStages]
  | succ J ih =>
      rw [uncutPrefix_succ, ih]
      change _ + meanField B N0 (2 * CoordinateAlgebra.A h)
        ((cycle B N0 (J + 1)).state.pressure - (cycle B N0 J).state.pressure) = _
      rw [meanField_sub]
      abel

/-- Temporal native, constructed using `VariableGaugeMean.temporalPotential`. -/
noncomputable def temporalNative (B N0 j : ℕ) : ActualMeanPhysicalData.Scalar :=
  VariableGaugeMean.temporalPotential (parameters B N0).gauge (parameters B N0).timeExponent
    (parameters B N0).commonIndex (commonContext B)
    ((parameters B N0).afterSigned (cycle B N0 j).coefficients
      (commonContext B) (cycle B N0 j).state)

/-- Rank native, constructed using `VariableGaugeMean.rankPotential`. -/
noncomputable def rankNative (B N0 j : ℕ) : ActualMeanPhysicalData.Scalar :=
  VariableGaugeMean.rankPotential (parameters B N0).gauge (parameters B N0).rank (commonContext B)
    ((parameters B N0).afterTemporal (cycle B N0 j).coefficients
      (commonContext B) (cycle B N0 j).state)

/-- Stream native stages as an element of `ℕ → ActualMeanPhysicalData.Scalar`. -/
noncomputable def streamNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k
    (ActualMeanPhysicalData.initialTemporalScalar B N0 + ActualMeanPhysicalData.initialRankScalar B
        N0)
    (fun j => temporalNative B N0 j + rankNative B N0 j)

/-- Stream mean stages, defined pointwise by `meanAngularField B N0 (CoordinateAlgebra.A h - 1 /
2) (streamNativeStages B N0 j)`. -/
noncomputable def streamMeanStages (B N0 : ℕ) : ℕ → VelocityField :=
  fun j => meanAngularField B N0 (CoordinateAlgebra.A h - 1 / 2) (streamNativeStages B N0 j)

theorem streamMeanStages_zero (B N0 : ℕ) :
    streamMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialStreamFamily B N0 (firstBand B N0)).angularField := rfl

theorem angularMeanStages_zero (B N0 : ℕ) :
    angularMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialAngularFamily B N0 (firstBand B N0)).angularField := rfl

theorem pressureMeanStages_zero (B N0 : ℕ) :
    pressureMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialPressureFamily B N0 (firstBand B N0)).field := rfl

/-- Mean cycle input: an abbreviation for `ActualMeanPhysicalData.InitialCycleInput B N0
(firstBand B N0) (parameterSequence B N0)`. -/
abbrev MeanCycleInput (B N0 : ℕ) :=
  ActualMeanPhysicalData.InitialCycleInput B N0 (firstBand B N0) (parameterSequence B N0)

theorem parameters_realizes (B N0 j : ℕ) :
    CycleStateCoherence.Realizes ActualMeanPhysicalData.initialGeometry
      (parameterSequence B N0 j) (commonContext B) :=
  ActualMeanPhysicalData.initial_realizes B _ _

theorem streamMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    streamMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).streamFamily j).angularField := rfl

theorem angularMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    angularMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).angularIncrementFamily j).angularField := rfl

theorem pressureMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    pressureMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).pressureIncrementFamily j).field := rfl

/-- Chart mean pressure parts, constructed using `CyclePhysicalPrefixes.polarPressureMap`. -/
noncomputable def chartMeanPressureParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n j : ℕ) : PressureField :=
  CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (fun x => pressureNativeStages B N0 j n x.1))

/-- Chart stream parts as an element of `ℕ → VelocityField`. -/
noncomputable def chartStreamParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → VelocityField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n)))
    (fun j => CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph
        n)
      (CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n +
       CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n)))

theorem angularNativeStages_overlap {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanAtlas B N0).OverlapLaw standardRegion.carrier (CoordinateAlgebra.A h)
      (angularNativeStages B N0 j) := by
  cases j with
  | zero => exact (ActualMeanPhysicalData.initialized_overlap B N0 (firstBand B N0)).angular
  | succ j =>
      exact (((ActualMeanPhysicalData.initialCycleData H).state_overlap (j + 1)).angular).sub
        (((ActualMeanPhysicalData.initialCycleData H).state_overlap j).angular)

theorem pressureNativeStages_overlap {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanAtlas B N0).OverlapLaw standardRegion.carrier (2 * CoordinateAlgebra.A h)
      (pressureNativeStages B N0 j) := by
  cases j with
  | zero => exact (ActualMeanPhysicalData.initialized_overlap B N0 (firstBand B N0)).pressure
  | succ j =>
      exact (((ActualMeanPhysicalData.initialCycleData H).state_overlap (j + 1)).pressure).sub
        (((ActualMeanPhysicalData.initialCycleData H).state_overlap j).pressure)

theorem angularNativeStages_chart (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n j : ℕ) :
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (fun x => ![0, angularNativeStages B N0 j n x.1, 0])) =
      chartDirectStages B N0 a i n j := by
  cases j with
  | zero => rfl
  | succ j =>
      change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
        (fun x => ![0, angularNativeStages B N0 (j + 1) n x.1, 0])) =
        CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
          (CyclePhysicalPrefixes.angularComponents
            ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
              (commonContext B) (cycle B N0 j).state) n +
           CyclePhysicalPrefixes.angularComponents
            ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
              (commonContext B) (cycle B N0 j).state) n))
      congr 2
      rw [angularNativeStages_succ]
      funext x q
      fin_cases q <;> simp [CyclePhysicalPrefixes.angularComponents]

theorem angularMeanStages_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    angularMeanStages B N0 j w = chartDirectStages B N0 a i n j w := by
  have he := (meanAtlas B N0).angular_field (angularNativeStages_overlap H j) ha i n hn ht hu hw
  change angularMeanStages B N0 j w =
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (fun x => ![0, angularNativeStages B N0 j n x.1, 0])) w at he
  rw [angularNativeStages_chart] at he
  exact he

theorem pressureMeanStages_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    pressureMeanStages B N0 j w = chartMeanPressureParts B N0 a i n j w :=
  (meanAtlas B N0).pressure_field (pressureNativeStages_overlap H j) ha i n hn ht hu hw

theorem streamMeanStages_curl_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    SpatialCurl.spatialCurl (streamMeanStages B N0 j) w = chartStreamParts B N0 a i n j w := by
  cases j with
  | zero => exact ActualMeanPhysicalData.initialStream_curl B N0 (firstBand B N0) n hn ha i ht hu hw
  | succ j => exact ActualMeanPhysicalData.cycleStream_curl H j n hn ha i ht hu hw

/-- Chart base velocity, constructed using `CyclePhysicalPrefixes.polarVelocityMap`. -/
noncomputable def chartBaseVelocity (B : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : VelocityField
    :=
  CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (PhysicalResidualBridge.baseComponents (commonContext B) n))

/-- Chart base pressure, given by `CyclePhysicalPrefixes.polarPressureMap a i
(CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n))`. -/
noncomputable def chartBasePressure (B : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : PressureField
    :=
  CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (basePressure B n))

/-- Chart wave parts as an element of `ℕ → VelocityField`. -/
noncomputable def chartWaveParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → VelocityField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      ((cycle B N0 0).state.oscillation n)))
    (fun j => CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph
        n)
      ((parameters B N0).particularVelocity (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n +
        (parameters B N0).signedVelocity (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n)))

/-- Chart wave pressure parts as an element of `ℕ → PressureField`. -/
noncomputable def chartWavePressureParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → PressureField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      ((cycle B N0 0).state.oscillatoryPressure n)))
    (fun j => CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph
        n)
      ((parameters B N0).particularPressure (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n +
        (parameters B N0).signedPressure (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n)))

theorem chartPotentialParts_zero (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPotentialParts B N0 a i n 0 = chartBaseVelocity B a i n +
      chartWaveParts B N0 a i n 0 + chartStreamParts B N0 a i n 0 := by
  change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (PhysicalResidualBridge.baseComponents (commonContext B) n +
      CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n +
        (cycle B N0 0).state.oscillation n)) =
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (PhysicalResidualBridge.baseComponents (commonContext B) n)) +
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      ((cycle B N0 0).state.oscillation n)) +
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n))
  simp only [map_add]
  abel

theorem chartPotentialParts_succ (B N0 j : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPotentialParts B N0 a i n (j + 1) =
      chartWaveParts B N0 a i n (j + 1) + chartStreamParts B N0 a i n (j + 1) := by
  change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (((parameters B N0).particularVelocity (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n +
      (parameters B N0).signedVelocity (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n) +
      CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n +
      CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n)) = _
  simp only [chartWaveParts, chartStreamParts, map_add]
  abel

theorem chartPressureParts_zero (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPressureStages B N0 a i n 0 = chartBasePressure B a i n +
      chartWavePressureParts B N0 a i n 0 + chartMeanPressureParts B N0 a i n 0 := by
  change CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (basePressure B n + (cycle B N0 0).state.totalPressureIncrement n)) =
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
        (basePressure B n)) +
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      ((cycle B N0 0).state.oscillatoryPressure n)) +
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      (fun x => (cycle B N0 0).state.pressure n x.1))
  have he : (cycle B N0 0).state.totalPressureIncrement n =
      (fun x => (cycle B N0 0).state.pressure n x.1) + (cycle B N0 0).state.oscillatoryPressure n
          := rfl
  rw [he]
  simp only [map_add]
  abel

theorem chartPressureParts_succ (B N0 j : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPressureStages B N0 a i n (j + 1) = chartWavePressureParts B N0 a i n (j + 1) +
      chartMeanPressureParts B N0 a i n (j + 1) := by
  have he : CyclePhysicalPrefixes.stepPressureComponents (parameters B N0)
      (cycle B N0 j).coefficients (commonContext B) (cycle B N0 j).state n =
      ((parameters B N0).particularPressure (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n +
       (parameters B N0).signedPressure (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n) +
      (fun x => pressureNativeStages B N0 (j + 1) n x.1) := by
    funext x
    unfold CyclePhysicalPrefixes.stepPressureComponents pressureNativeStages
    change _ = _ + _ +
      (((parameters B N0).afterRank (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).pressure n x.1 -
        (cycle B N0 j).state.pressure n x.1)
    ring
  change CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (CyclePhysicalPrefixes.stepPressureComponents (parameters B N0)
      (cycle B N0 j).coefficients (commonContext B) (cycle B N0 j).state n)) = _
  rw [he]
  simp only [chartWavePressureParts, chartMeanPressureParts, map_add]

/-! ## The fixed physical base in the same chart

Both normalizations below are computed from the actual graph map. In
particular the pressure factor is the square of the velocity factor. -/

theorem graph_cylinderPoint (n : ℕ) (z : SpaceTime) :
    ActualBaseResidual.cylinderPoint h (ChartScales.Q n)
      (PhysicalResidualTZ.graphMapTZ (graph n) z) = z := by
  have hQ := ChartScales.Q_pos n
  have hs : Real.sqrt (ChartScales.Q n) * ChartScales.Q n ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
    norm_num
  have hd : ChartScales.Q n ^ CoordinateAlgebra.D h * ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      1 := by
    rw [← Real.rpow_add hQ]
    simp
  have ht : ChartScales.Q n * ChartScales.Q n ^ (-1 : ℝ) = 1 := by
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hQ.ne']
  have htime : (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon =
      ChartScales.Q n ^ (-1 : ℝ) :=
    PhysicalResidualBridge.commonGraph_slowTimeScale hQ h _
  have haxial : (graph n).radialScale * (graph n).epsilon =
      ChartScales.Q n ^ (-CoordinateAlgebra.D h) :=
    PhysicalResidualBridge.commonGraph_axialScale hQ h _
  apply Prod.ext
  · change 1 - ChartScales.Q n *
      ((graph n).velocityScale * (graph n).radialScale * (graph n).epsilon * (1 - z.1)) = z.1
    rw [htime, ← mul_assoc, ht]
    ring
  · ext j
    fin_cases j
    · simp only [ActualBaseResidual.cylinderPoint]
      simp only [AxisymmetricResidual.pack, ProblemStatement.coordinateVector,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
      norm_num
      simp only [show (0 : Fin 3) ≠ 2 by decide, ite_false, add_zero]
      change Real.sqrt (ChartScales.Q n) * (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0) = z.2 0
      rw [← mul_assoc, hs, one_mul]
    · simp [ActualBaseResidual.cylinderPoint, AxisymmetricResidual.pack,
        ProblemStatement.coordinateVector, PhysicalResidualTZ.graphMapTZ,
            PhysicalResidualBridge.ScaledGraph.map,
        PhysicalResidualTZ.swapCylinder_apply]
    · simp only [ActualBaseResidual.cylinderPoint]
      simp only [AxisymmetricResidual.pack, ProblemStatement.coordinateVector,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
      norm_num
      change ChartScales.Q n ^ CoordinateAlgebra.D h *
        ((graph n).radialScale * (graph n).epsilon * z.2 2) = z.2 2
      rw [haxial, ← mul_assoc, hd, one_mul]

theorem graph_physicalPoint (n : ℕ) (z : SpaceTime) :
    ActualBaseResidual.physicalPoint h (ChartScales.Q n)
      (PhysicalResidualTZ.graphMapTZ (graph n) z) = (z.1, CylindricalResidual.chart z.2) := by
  unfold ActualBaseResidual.physicalPoint
  rw [graph_cylinderPoint]

theorem graph_mem_baseDomain (n : ℕ) {z : SpaceTime} (ht : z.1 < 1) (hr : 0 < z.2 0) :
    PhysicalResidualTZ.graphMapTZ (graph n) z ∈ ActualBaseResidual.domain := by
  constructor
  · change 0 < ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr
  · change 0 < (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon * (1 - z.1)
    have htime : (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon =
        ChartScales.Q n ^ (-1 : ℝ) :=
      PhysicalResidualBridge.commonGraph_slowTimeScale (ChartScales.Q_pos n) h _
    rw [htime]
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) (sub_pos.mpr ht)

theorem base_velocity_on_cylinder (B n : ℕ) {z : SpaceTime} (ht : z.1 < 1) (hr : 0 < z.2 0) :
    CyclePhysicalPrefixes.velocityMap (graph n) (PhysicalResidualBridge.baseComponents
        (commonContext B) n) z =
      CylindricalResidual.frame (-(z.2 1))
        (FinalSlowBase.velocity certificate modulation upper B (z.1, CylindricalResidual.chart
            z.2)) := by
  have hb := ActualBaseResidual.velocityAtScale_eq_baseComponents certificate modulation upper B
    (CorrectionInitialization.CommonWindow.index h) n (graph_mem_baseDomain n ht hr)
  change ActualBaseResidual.velocityAtScale certificate modulation upper B (ChartScales.Q n)
    (PhysicalResidualTZ.graphMapTZ (graph n) z) =
    PhysicalResidualBridge.baseComponents (commonContext B) n
      (PhysicalResidualTZ.graphMapTZ (graph n) z) at hb
  ext j
  simp only [CyclePhysicalPrefixes.velocityMap, LinearMap.coe_mk, AddHom.coe_mk,
    PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
    PhysicalResidualBridge.baseComponents (commonContext B) n
      (PhysicalResidualTZ.graphMapTZ (graph n) z) j = _
  rw [← hb]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) * (ChartScales.Q n ^ CoordinateAlgebra.A h *
    (CylindricalResidual.frame (-(z.2 1))
      (FinalSlowBase.velocity certificate modulation upper B
        (ActualBaseResidual.physicalPoint h (ChartScales.Q n)
          (PhysicalResidualTZ.graphMapTZ (graph n) z)))) j) = _
  rw [graph_physicalPoint, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp

theorem base_pressure_on_cylinder (B n : ℕ) (z : SpaceTime) :
    CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n) z =
      FinalSlowBase.pressure certificate modulation upper B (z.1, CylindricalResidual.chart z.2) :=
          by
  change (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) ^ 2 *
    (ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) *
      FinalSlowBase.pressure certificate modulation upper B
        (ActualBaseResidual.physicalPoint h (ChartScales.Q n)
          (PhysicalResidualTZ.graphMapTZ (graph n) z))) = _
  rw [graph_physicalPoint, pow_two, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n),
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have he : -CoordinateAlgebra.A h + -CoordinateAlgebra.A h + 2 * CoordinateAlgebra.A h = 0 := by
      ring
  rw [he, Real.rpow_zero, one_mul]

theorem chartBaseVelocity_eq (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (ht : w.1 < 1) (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    chartBaseVelocity B a i n w = FinalSlowBase.velocity certificate modulation upper B w := by
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw).1
  have hangle : z.2 1 = (PhysicalCurlCovariance.polarInput a i w).2 := by
    simp only [z, PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_one]
  unfold chartBaseVelocity
  simp only [CyclePhysicalPrefixes.polarVelocityMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hangle]
  change CylindricalResidual.frame (z.2 1)
    (CyclePhysicalPrefixes.velocityMap (graph n)
      (PhysicalResidualBridge.baseComponents (commonContext B) n) z) = _
  rw [base_velocity_on_cylinder B n (z := z) ht hr, CylindricalResidual.frame_inverse']
  exact congrArg (FinalSlowBase.velocity certificate modulation upper B)
    (ActualMeanPotentialRealization.polarCoordinates_back ha i hw)

theorem chartBasePressure_eq (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    chartBasePressure B a i n w = FinalSlowBase.pressure certificate modulation upper B w := by
  change CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n)
    (PhysicalCurlCovariance.polarCoordinates a i w) = _
  rw [base_pressure_on_cylinder]
  exact congrArg (FinalSlowBase.pressure certificate modulation upper B)
    (ActualMeanPotentialRealization.polarCoordinates_back ha i hw)

theorem basePotential_curl_on_chart (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (ht : w.1 < 1) (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    SpatialCurl.spatialCurl (TailGaugePotential.finalPotential certificate modulation upper B) w =
      chartBaseVelocity B a i n w :=
  (TailGaugePotential.finalPotential_sameCurl certificate modulation upper B ht).trans
    (chartBaseVelocity_eq B ha i n ht hw).symm

/-! ## Constructed direct angular and mean-stream stage data -/

/-- Direct data as an element of `ℕ → DirectAngularDiagonal.AngularData
(LocalAngularDiagonal.localSlowDomain h (qbig B N0))`. -/
noncomputable def directData {B N0 : ℕ} (H : MeanCycleInput B N0) :
    ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h (qbig B N0)) :=
  fun k => Nat.casesOn k
    (ActualMeanStageData.initialAngularData B N0 (firstBand B N0) (qbig B N0) le_rfl)
    (fun j => ActualMeanStageData.cycleAngularData H j (qbig B N0) le_rfl)

/-- Stream data as an element of `ℕ → DirectAngularDiagonal.AngularData
(LocalAngularDiagonal.localSlowDomain h (qbig B N0))`. -/
noncomputable def streamData {B N0 : ℕ} (H : MeanCycleInput B N0) :
    ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h (qbig B N0)) :=
  fun k => Nat.casesOn k
    (ActualMeanStageData.initialStreamData B N0 (firstBand B N0) (qbig B N0) le_rfl)
    (fun j => ActualMeanStageData.cycleStreamData H j (qbig B N0) le_rfl)

/-- Mean stream support, given by `MixedAxisPreservation.AngularSupport.ofAngularData
(streamData H j) (fun _ hw => hw)`. -/
noncomputable def meanStreamSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h (qbig B N0)) :=
  MixedAxisPreservation.AngularSupport.ofAngularData (streamData H j) (fun _ hw => hw)

theorem directData_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    LocalAngularDiagonal.rawSeries (directData H) j = angularMeanStages B N0 j := by
  cases j with
  | zero =>
      exact (ActualMeanStageData.initialAngularData_field B N0 (firstBand B N0) (qbig B N0)
          le_rfl).trans
        (angularMeanStages_zero B N0).symm
  | succ j =>
      exact (ActualMeanStageData.cycleAngularData_field H j (qbig B N0) le_rfl).trans
        (angularMeanStages_succ H j).symm

theorem streamData_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    DirectAngularDiagonal.angularField (streamData H j).scalar = streamMeanStages B N0 j := by
  cases j with
  | zero =>
      exact (ActualMeanStageData.initialStreamData_field B N0 (firstBand B N0) (qbig B N0)
          le_rfl).trans
        (streamMeanStages_zero B N0).symm
  | succ j =>
      exact (ActualMeanStageData.cycleStreamData_field H j (qbig B N0) le_rfl).trans
        (streamMeanStages_succ H j).symm

theorem meanStreamSupport_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanStreamSupport H j).field = streamMeanStages B N0 j := streamData_field H j

theorem angularMeanStages_smooth {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (angularMeanStages B N0 j) (physicalDomain B N0) := by
  rw [← directData_field H j]
  exact LocalAngularDiagonal.rawSeries_smooth outgoing.data.h_pos outgoing.data.h_lt_half
      (directData H) j

theorem streamMeanStages_smooth {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (streamMeanStages B N0 j) (physicalDomain B N0) := by
  rw [← streamData_field H j]
  exact (streamData H j).field_smooth
    (LocalAngularDiagonal.localSlowDomain_open outgoing.data.h_pos outgoing.data.h_lt_half _)

theorem angularMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (angularMeanStages B N0 j) := by
  cases j with
  | zero =>
      have hh := (ActualMeanStageData.initial_shrinkingSupport B N0 (firstBand B N0) (qbig B N0)
          le_rfl).1
      erw [ActualMeanStageData.initialAngularSupport_field] at hh
      simp only [angularMeanStages_zero]
      exact hh
  | succ j =>
      have hh := (ActualMeanStageData.cycle_shrinkingSupport H j (qbig B N0) le_rfl).1
      erw [ActualMeanStageData.cycleAngularSupport_field] at hh
      simp only [angularMeanStages_succ H]
      exact hh

theorem streamMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (streamMeanStages B N0 j) := by
  cases j with
  | zero =>
      have hh := (ActualMeanStageData.initial_shrinkingSupport B N0 (firstBand B N0) (qbig B N0)
          le_rfl).2.2.2
      erw [ActualMeanStageData.initialStreamSupport_field] at hh
      simp only [streamMeanStages_zero]
      exact hh
  | succ j =>
      have hh := (ActualMeanStageData.cycle_shrinkingSupport H j (qbig B N0) le_rfl).2.2.2
      erw [ActualMeanStageData.cycleStreamSupport_field] at hh
      simp only [streamMeanStages_succ H]
      exact hh

theorem pressureMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (pressureMeanStages B N0 j) := by
  cases j with
  | zero =>
      rw [pressureMeanStages_zero]
      exact (PhysicalStageSupport.actual_coherent_support
        (ActualMeanPhysicalData.initialPressureFamily B N0 (firstBand B N0))
        (ActualMeanStageData.nativeSupport_of_moving _
          (ActualMeanPhysicalData.initial_pressure_moving B N0)) le_rfl).1
  | succ j =>
      rw [pressureMeanStages_succ H]
      have hs : (VariableGaugeMean.reconstructState ActualMeanPhysicalData.initialGeometry.gauge
          (commonContext B) (ActualInitialization.initialCycleState B N0).state).pressure =
          (ActualInitialization.initialCycleState B N0).state.pressure := by
        rw [ActualMeanPhysicalData.initialGeometry_gauge]
        rfl
      exact (PhysicalStageSupport.actual_coherent_support
        ((ActualMeanPhysicalData.initialCycleData H).pressureIncrementFamily j)
        (ActualMeanStageData.nativeSupport_of_moving _
          ((ActualMeanPhysicalData.initialCycleData H).pressureIncrement_moving hs j)) le_rfl).1

/-! The stage constructors retain the actual copy data. The wave producers
supply these records; the mean field is fixed by the same cycle above. -/

/-- Initial potential stage, bundling `waveCount`, `waves`, `streamCount`, `streams`. -/
noncomputable def initialPotentialStage (B N0 : ℕ)
    (wave : MixedAxisPreservation.CopyPotential.{u} h) :
    MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h (qbig B N0))
        where
  waveCount := 1
  waves _ := wave
  streamCount := 1
  streams _ := ActualMeanStageData.initialStreamSupport B N0 (firstBand B N0) (qbig B N0) le_rfl

/-- Positive potential stage, bundling `waveCount`, `waves`, `streamCount`, `streams`. -/
noncomputable def positivePotentialStage {B N0 : ℕ} (H : MeanCycleInput B N0)
    (j : ℕ) (particular signed : MixedAxisPreservation.CopyPotential.{u} h) :
    MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h (qbig B N0))
        where
  waveCount := 2
  waves := ![particular, signed]
  streamCount := 1
  streams _ := meanStreamSupport H (j + 1)

theorem initialPotentialStage_field (B N0 : ℕ)
    (wave : MixedAxisPreservation.CopyPotential.{u} h) :
    (initialPotentialStage B N0 wave).field = wave.field + streamMeanStages B N0 0 := by
  funext w
  change (∑ _ : Fin 1, wave.field w) +
    (∑ _ : Fin 1, (ActualMeanStageData.initialStreamSupport B N0 (firstBand B N0)
      (qbig B N0) le_rfl).field w) = _
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_const,
    Finset.card_singleton, one_smul, streamMeanStages_zero, Pi.add_apply, add_right_inj]
  erw [ActualMeanStageData.initialStreamSupport_field]

theorem positivePotentialStage_field {B N0 : ℕ} (H : MeanCycleInput B N0)
    (j : ℕ) (particular signed : MixedAxisPreservation.CopyPotential.{u} h) :
    (positivePotentialStage H j particular signed).field =
      particular.field + signed.field + streamMeanStages B N0 (j + 1) := by
  funext w
  change (∑ i : Fin 2, (![particular, signed] i).field w) +
    (∑ _ : Fin 1, (meanStreamSupport H (j + 1)).field w) = _
  simp [Fin.sum_univ_two, meanStreamSupport_field]

end NavierStokes.ActualCandidateConstruction

end
end

end

section

/-!
# Endpoint inputs for the actual raw candidate stages

Positive stages use their already proved raw estimates.  Stage zero uses
the actual initial mean families and the existing extensions of the same
base potential and pressure.  No output extension is an input below.
-/

@[expose] public section

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

/-- Initial direct model, given by `(ActualMeanPhysicalData.initialAngularFamily B N0
N).angularField`. -/
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

end
end

end

section

/-!
# Endpoint inputs for physical fields assembled by germs

The potential increments may be literal glued physical fields.  Only their
interior smoothness and actual derivative estimates enter the extension
argument; a representation by a fixed-reference copy family is unnecessary.
The zeroth potential and pressure retain the separately extended slow base.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.GermEndpointInputs

open Set Function Filter ProblemStatement
open scoped Topology ContDiff

/-- Interior data for one actual physical field.  The exponent and logarithmic
loss may depend on the derivative order and on the field.  In particular this
record neither assumes an endpoint limit nor compares different stages. -/
structure PhysicalJets (h qbig : ℝ) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : SpaceTime → V) : Prop where
  smooth : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig)
  bound : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
    ‖iteratedFDeriv ℝ m f w‖ ≤
      C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
        PhysicalWaveSum.physicalQ h w ^ e

namespace PhysicalJets

variable {h qbig : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : SpaceTime → V}

/-- Adapter for the power bounds of the current-band physical construction.
The time restriction is kept, as in the physical wave estimate. -/
theorem of_power
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ e) :
    PhysicalJets h qbig f := by
  refine ⟨hf, fun m => ?_⟩
  obtain ⟨C, e, hm⟩ := hb m
  refine ⟨C, 0, e, fun w hw ht hq => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hm w hw ht hq

/-- The positive-index restriction in `RawStageBounds` is preserved. -/
theorem of_rawStage {A : ℕ → SpaceTime → V} {g L : ℕ → ℝ}
    {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig (A j) := by
  refine ⟨hf, fun m => ⟨C j m, p j m, g j - L m, ?_⟩⟩
  exact fun w hw _ hq => hb j hj m w ⟨hw.1, hw⟩ hq

/-- A smaller scale cap preserves the same constants. -/
theorem mono {qsmall : ℝ} (J : PhysicalJets h qbig f) (hq : qsmall ≤ qbig) :
    PhysicalJets h qsmall f := by
  have hsub : CutStageEstimates.physicalSublevel h qsmall ⊆
      CutStageEstimates.physicalSublevel h qbig :=
    fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩
  exact ⟨J.smooth.mono hsub, fun m => by
    obtain ⟨C, p, e, hb⟩ := J.bound m
    exact ⟨C, p, e, fun w hw => hb w (hsub hw)⟩⟩

/-- Physical identities on the open validity region identify every actual
ordinary jet.  Values at a chart face or beyond the region are irrelevant. -/
theorem congr (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : EqOn g f (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig g := by
  refine ⟨J.smooth.congr he, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  refine ⟨C, p, e, fun w hw ht hq => ?_⟩
  have hloc : g =ᶠ[𝓝 w] f := by
    filter_upwards [(CutStageEstimates.physicalSublevel_open hh hh1 qbig).mem_nhds hw]
      with z hz
    exact he hz
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hloc m]
  exact hb w hw ht hq

/-- Finite sums retain derivative bounds without identifying a summand with
any copy-family construction. -/
theorem add (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (K : PhysicalJets h qbig g) (hh : 0 < h) (hh1 : h < 1 / 2) :
    PhysicalJets h qbig (fun w => f w + g w) := by
  refine ⟨J.smooth.add K.smooth, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  obtain ⟨D, r, s, hk⟩ := K.bound m
  refine ⟨max C 0 + max D 0, max p r, min e s, fun w hw ht hq => ?_⟩
  have hq0 := PhysicalWaveSum.physicalQ_pos hh hh1 hw.1
  have hl : (1 : ℝ) ≤ 1 + |Real.log (PhysicalWaveSum.physicalQ h w)| := by
    linarith [abs_nonneg (Real.log (PhysicalWaveSum.physicalQ h w))]
  have hmono (C' p' e' : ℝ) (hp : p' ≤ max p r) (he : min e s ≤ e') :
      C' * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' ≤
        max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
    calc
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' := by
        gcongr
        exact le_max_left _ _
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hl hp) (le_max_right _ _)
        · exact Real.rpow_le_rpow_of_exponent_ge hq0 hq he
        · exact Real.rpow_nonneg hq0.le _
        · positivity
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f w‖ + ‖iteratedFDeriv ℝ m g w‖ :=
      ResidualStability.norm_jet_add_le
        (CutStageEstimates.physicalSublevel_open hh hh1 qbig) J.smooth K.smooth hw m
    _ ≤ C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e +
        D * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ r *
          PhysicalWaveSum.physicalQ h w ^ s := add_le_add (hb w hw ht hq) (hk w hw ht hq)
    _ ≤ _ := (add_le_add
      (hmono C p e (le_max_left _ _) (min_le_left _ _))
      (hmono D r s (le_max_right _ _) (min_le_right _ _))).trans_eq (by ring)

/-- This is an application of the existing local bounded-jet extension
theorem.  No new boundary regularity hypothesis is introduced. -/
theorem extension [CompleteSpace V] (J : PhysicalJets h qbig f)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) :=
  OffplaneJetExtensions.extension_of_powerLog_jets hh hh1 hqbig J.smooth J.bound hx hqx

end PhysicalJets

section MeanInputs

/-- The actual mean-pressure native bounds supply the single-field input. -/
theorem mean_field_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.field := by
  apply PhysicalJets.of_power (M.field_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.field_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

/-- This applies to both actual mean-stream potentials and the direct angular
increments, with their own physical degree and their original first band. -/
theorem mean_angular_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.angularField := by
  apply PhysicalJets.of_power (M.angular_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.angular_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

end MeanInputs

section ExistingWaveInputs

variable {h qbig : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

/-- Existing initial or signed wave data can be used for those summands.
No such data are requested for the glued particular summand. -/
theorem wave_vector_jets (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.vector := by
  apply PhysicalJets.of_power ((W.vector_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.vector_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

theorem wave_pressure_jets (W : PhysicalStageBounds.WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.pressure := by
  apply PhysicalJets.of_power ((W.pressure_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.pressure_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

end ExistingWaveInputs

section InitialCorrections

open CorrectionInitialization.ActualPrimary

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The finite potential correction at index zero uses the actual initial
wave, temporal mean, and rank mean.  The slow-base gauge is excluded here. -/
theorem initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
          := by
  have ht := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  have hr := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  apply ((wave_vector_jets WA outgoing.data.h_pos outgoing.data.h_lt_half).add
    (ht.add hr outgoing.data.h_pos outgoing.data.h_lt_half)
    outgoing.data.h_pos outgoing.data.h_lt_half).congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w _
  rw [ActualMeanPhysicalData.initialStream_angularField]
  rfl

theorem initial_direct_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField :=
  mean_angular_jets (ActualPhysicalStageBounds.actualInitialAngularInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq

/-- The finite initial pressure correction retains the actual initial
wave pressure and the pressure mean. -/
theorem initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) :=
  (wave_pressure_jets WP outgoing.data.h_pos outgoing.data.h_lt_half).add
    (mean_field_jets (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    outgoing.data.h_pos outgoing.data.h_lt_half

end InitialCorrections

/-- A finite physical sum can be extended directly from estimates of its
actual summands.  Equality is required only on the physical validity region. -/
theorem extension_of_sum3 {h qbig : ℝ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {f f₁ f₂ f₃ : SpaceTime → V}
    (J₁ : PhysicalJets h qbig f₁) (J₂ : PhysicalJets h qbig f₂)
    (J₃ : PhysicalJets h qbig f₃)
    (he : EqOn f (fun w => f₁ w + f₂ w + f₃ w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  apply OffplaneJetExtensions.extension_of_eqOn_sublevel hh hh1 he hx hqx
  exact OffplaneJetExtensions.extension_add
    (OffplaneJetExtensions.extension_add (J₁.extension hh hh1 hqbig hx hqx)
      (J₂.extension hh hh1 hqbig hx hqx)) (J₃.extension hh hh1 hqbig hx hqx)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Bounds for literal raw fields imply all three candidate endpoint inputs.
The base gauge is never subjected to a growth assumption, and the positive
stage estimate is never applied to index zero. -/
theorem endpoints_of_bounds (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    {initial : VelocityField} {pInitial : PressureField}
    (hA0 : EqOn (A 0)
      (fun w => TailGaugePotential.finalPotential H v upper bandFloor w + initial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hP0 : EqOn (P 0)
      (fun w => FinalSlowBase.pressure H v upper bandFloor w + pInitial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JA : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (A j))
    (JV : ∀ j, PhysicalJets F.data.h qbig (V j))
    (JP : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (P j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig A V P := by
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        have hx0 : x ≠ 0 := by intro he; exact hx (by simp [he])
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hA0 hx hqx
        exact OffplaneJetExtensions.extension_add
          (TailGaugePotential.finalPotential_awayExtensions H v upper bandFloor x hx0)
          (Jinitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JA (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    exact (JV j).extension F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hP0 hx hqx
        exact OffplaneJetExtensions.extension_add
          ⟨SlowBaseEndpoint.finalPressureNonzeroAxial H v upper bandFloor hx⟩
          (JpInitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JP (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx

/-- Literal fields accepted by `GermCandidateAssembly`.  In particular
`stages j` may be a glued current-particular field plus signed and mean
corrections; there is no copy-family or potential-stage argument. -/
theorem germ_stage_endpoints (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (Jstages : ∀ j, PhysicalJets F.data.h qbig (stages j))
    (JD : ∀ j, PhysicalJets F.data.h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JpStages : ∀ j, PhysicalJets F.data.h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages) := by
  apply endpoints_of_bounds H v upper bandFloor hqbig
    (fun _ _ => rfl) (fun _ _ => MixedCandidateAssembly.pressureStages_zero ..)
    Jinitial JpInitial ?_ JD ?_
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact Jstages j
  · intro j hj
    cases j with
    | zero => omega
    | succ j => simpa only [MixedCandidateAssembly.pressureStages_succ] using JpStages j

/-- Once the finite-stage estimates have been derived, only the bounded
finite initial pieces remain to be supplied.  This wrapper does not inspect
or impose a representation of any positive physical stage. -/
theorem germ_stage_endpoints_of_estimates (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages))
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (Jdirect : PhysicalJets F.data.h qbig (LocalAngularDiagonal.rawSeries D 0))
    (JpInitial : PhysicalJets F.data.h qbig pInitial) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages) := by
  apply endpoints_of_bounds H v upper bandFloor hqbig
    (fun _ _ => rfl) (fun _ _ => MixedCandidateAssembly.pressureStages_zero ..)
    Jinitial JpInitial
    (fun j hj => PhysicalJets.of_rawStage E.potential_bound hj (E.potential_smooth j)) ?_
    (fun j hj => PhysicalJets.of_rawStage E.pressure_bound hj (E.pressure_smooth j))
  intro j
  cases j with
  | zero => exact Jdirect
  | succ j =>
      exact PhysicalJets.of_rawStage E.direct_bound (Nat.succ_le_succ (Nat.zero_le j))
        (E.direct_smooth (j + 1))

end ActualBase

section ActualInitialChoice

open CorrectionInitialization.ActualPrimary

/-- The chosen initial potential supplies its own native wave data.  The
consumer does not have to provide or postulate such a witness. -/
theorem actual_initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  simpa only [InitialPhysicalData.potentialWaveData_vector] using
    initial_potential_jets B N0 N hN (InitialPhysicalData.potentialWaveData B N0) hq

theorem actual_initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) := by
  simpa only [InitialPhysicalData.pressureWaveData_pressure] using
    initial_pressure_jets B N0 N hN (InitialPhysicalData.pressureWaveData B N0) hq

/-- The same-choice mixed raw sequence has all endpoint inputs.  Positive
fields are arbitrary physical fields, including the genuine glued particular
fields.  Only their derived interior jet estimates are used.  Initialization
is bound to the actual initial wave and actual mean families by local field
identities, with no supplied wave-data or endpoint-extension witness. -/
theorem actual_germ_stage_endpoints (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig))
    (Jstages : ∀ j, PhysicalJets h qbig (stages j))
    (Jdirect : ∀ j, 1 ≤ j → PhysicalJets h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpStages : ∀ j, PhysicalJets h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply germ_stage_endpoints certificate modulation upper B (hq.trans (ChartScales.Q_le_one N))
    initial stages D pInitial pStages
    ((actual_initial_potential_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hInitial)
    Jstages ?_
    ((actual_initial_pressure_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hPressure) JpStages
  intro j
  cases j with
  | zero =>
      exact (initial_direct_jets B N0 N hN hq).congr
        outgoing.data.h_pos outgoing.data.h_lt_half hDirect
  | succ j => exact Jdirect (j + 1) (Nat.succ_le_succ (Nat.zero_le j))

/-- A derived `StageEstimates` record is an alternative source of the
positive-stage estimates.  No quantitative conclusion or representation of
the glued particular field is added as a hypothesis here. -/
theorem actual_germ_stage_endpoints_of_estimates (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages))
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply actual_germ_stage_endpoints B N0 N hN hq initial stages D pInitial pStages
    hInitial hDirect hPressure
  · intro j
    exact PhysicalJets.of_rawStage E.potential_bound (Nat.succ_le_succ (Nat.zero_le j))
      (E.potential_smooth (j + 1))
  · intro j hj
    exact PhysicalJets.of_rawStage E.direct_bound hj (E.direct_smooth j)
  · intro j
    simpa only [MixedCandidateAssembly.pressureStages_succ] using
      PhysicalJets.of_rawStage E.pressure_bound (Nat.succ_le_succ (Nat.zero_le j))
        (E.pressure_smooth (j + 1))

end ActualInitialChoice

end NavierStokes.GermEndpointInputs

end
end

end

section

/-!
# The Cartesian curl of the actual finite particular-wave sum

The potential and pressure are the literal current-band sums constructed in
`ActualCurrentParticularPhysical`.  Their modes are identified with the same
canonical solver used by the correction cycle.  On a valid current polar chart,
the curl is therefore the actual particular velocity increment, with its physical
scale and moving frame.  No output representation is an input to these identities.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCurrentParticularAssembly

open Set Function Filter ProblemStatement CorrectionState CorrectionStep CorrectionInitialization
open ActualCurrentParticularPhysical
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

theorem space_sum_apply {ι : Type*} (s : Finset ι) (v : ι → Space) (k : Fin 3) :
    (∑ b ∈ s, v b) k = ∑ b ∈ s, v b k :=
  map_sum (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : Space →L[ℝ] ℝ) v s

theorem localPotential_eq_sum (x : CycleState (ActualInitialization.Index B N0)) (n : ℕ) :
    localPotential (ActualCycleParameters.particularState x) n = fun w =>
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w := by
  classical
  funext w
  simp only [localPotential, ActualCycleParameters.particularState,
    ActualCycleParameters.reindexState, ActualCycleParameters.reindexCoefficients,
    Equiv.symm_symm, Finset.sum_map, Equiv.toEmbedding_apply,
    ActualCycleParameters.swap_apply]

theorem localPressure_eq_sum (x : CycleState (ActualInitialization.Index B N0)) (n : ℕ) :
    localPressure (ActualCycleParameters.particularState x) n = fun w =>
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        localPressureMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w := by
  classical
  funext w
  simp only [localPressure, ActualCycleParameters.particularState,
    ActualCycleParameters.reindexState, ActualCycleParameters.reindexCoefficients,
    Equiv.symm_symm, Finset.sum_map, Equiv.toEmbedding_apply,
    ActualCycleParameters.swap_apply]

theorem nativeMode_eq (x : CycleState (ActualInitialization.Index B N0))
    (l : ActualInitialization.Index B N0) (j : ℤ) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) (k : Fin 3) :
    ActualParticularCycleData.nativeMode x l j n z k =
      (nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n
        (ActualWaveRegularity.particularChart z) k).re := rfl

theorem particularVelocity_eq_sum {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) (k : Fin 3) :
    (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
        (CorrectionInitialization.ActualPrimary.commonContext B) x.state n z k =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        (nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n
          (ActualWaveRegularity.particularChart z) k).re := by
  classical
  change (∑ l ∈ x.coefficients.labels n, (ActualParticularCycleData.block x l).oscillation n z k) =
      _
  apply Finset.sum_congr rfl
  intro l _
  rw [ActualParticularCycleData.block_eq_modes H l]
  rfl

theorem particularPressure_eq_sum {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) :
    (ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
        (CorrectionInitialization.ActualPrimary.commonContext B) x.state n z =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        (nativePressure (ActualCycleParameters.particularState x) (l.2,l.1) j n
          (ActualWaveRegularity.particularChart z)).re := by
  classical
  change (∑ l ∈ x.coefficients.labels n, (ActualParticularCycleData.block x l).oscillatoryPressure
      n z) = _
  apply Finset.sum_congr rfl
  intro l _
  rw [ActualParticularCycleData.particularBlock_pressure_eq_modes _ _ _ _ _ (H.frequency l)]
  rfl

theorem nativeMap_eq_graph (n : ℕ) (z : SpaceTime) :
    PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z =
    ActualWaveRegularity.particularChart
      (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) := rfl

theorem velocityMap_apply (n : ℕ) (v : PhysicalResidualBridge.Cylinder → Fin 3 → ℝ)
    (z : SpaceTime) (k : Fin 3) :
    CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n) v z k =
      (ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
        v (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) k := by
  change (ActualCycleResidualBounds.actualBandGraph n).velocity
    (fun x => v (PhysicalResidualTZ.swapCylinder x)) z k = _
  rw [PhysicalResidualBridge.ScaledGraph.velocity_apply]
  rfl

theorem pressureMap_apply (n : ℕ) (p : PhysicalResidualBridge.Cylinder → ℝ) (z : SpaceTime) :
    CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n) p z =
      (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
        p (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) := by
  change ((ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h)) ^ 2
      * _ = _
  rw [← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  congr 2
  ring

theorem localPotential_curl_eq_sum
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n) w =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        SpatialCurl.spatialCurl
          (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w := by
  classical
  rw [localPotential_eq_sum]
  have hd (l : ActualInitialization.Index B N0) (j : ℤ)
      (hj : j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand) :
      DifferentiableAt ℝ
        (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w :=
    ((localModes_contDiffAt_of_invariant H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hw hm).1).differentiableAt (by simp)
  rw [PhysicalParticularWave.spatialCurl_finset_sum _ _ (fun l _ =>
    DifferentiableAt.fun_sum (fun j hj => hd l j hj))]
  exact Finset.sum_congr rfl (fun l _ =>
    PhysicalParticularWave.spatialCurl_finset_sum _ _ (hd l))

theorem localPotential_curl_components
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hm : PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n) z ∈ nativeDomain) (k : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2)) k =
    (ChartScales.Q n) ^ (-CoordinateAlgebra.A ActualPrimary.h) *
      (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
        (ActualPrimary.commonContext B) x.state n
        (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) k := by
  classical
  have hw : (z.1, CylindricalResidual.chart z.2) ∈
      ActualMeanPotentialRealization.cartesianDomain a i := by
    simpa [ActualMeanPotentialRealization.cartesianDomain,
        PhysicalGraphBounds.radialProjection_apply,
      CylindricalResidual.chart, PolarCharts.polar] using hz.2.2
  have hm' : nativePoint n (z.1, CylindricalResidual.chart z.2) ∈ nativeDomain := by
    apply (nativeMap_polar_mem_iff n a i _).mp
    rwa [PhysicalCurlCovariance.polarCoordinates_forward ha i hz]
  rw [localPotential_curl_eq_sum H hN n ha i hw hm', particularVelocity_eq_sum H]
  simp only [map_sum, space_sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [nativeMap_eq_graph] using localPotentialMode_curl_of_invariant H hN l j
    ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hz hm k

theorem localPotential_curl_forward
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hm : PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n) z ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2) =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n))
        (z.1, CylindricalResidual.chart z.2) := by
  have he : CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2)) =
      CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
        ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
          (ActualPrimary.commonContext B) x.state n) z := by
    ext k
    rw [velocityMap_apply]
    exact localPotential_curl_components H hN n ha i hz hm k
  rw [ActualMeanPotentialRealization.polar_forward ha i _ hz]
  simpa only [CylindricalResidual.frame_inverse'] using
    congrArg (CylindricalResidual.frame (z.2 1)) he

theorem localPotential_curl
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n) w =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n)) w := by
  have he := localPotential_curl_forward H hN n ha i
    (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw)
    ((nativeMap_polar_mem_iff n a i w).mpr hm)
  simpa only [ActualMeanPotentialRealization.polarCoordinates_back ha i hw] using he

theorem localPressure_eq
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPressure (ActualCycleParameters.particularState x) n w =
      CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
            (ActualPrimary.commonContext B) x.state n)) w := by
  classical
  rw [localPressure_eq_sum]
  change (∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes
      x.coefficients.residualBand,
    localPressureMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w) =
    CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n) _
      (PhysicalCurlCovariance.polarCoordinates a i w)
  rw [pressureMap_apply, particularPressure_eq_sum H]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  rw [localPressureMode_eq_chart _ _ _
    (ActualParticularDynamics.carrier_frequency (ActualParticularCycleData.preservesCarriers H)
        (l.2,l.1))
    n ha i hw]
  change (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
    (nativePressure (ActualCycleParameters.particularState x) (l.2,l.1) j n
      (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (PhysicalCurlCovariance.polarCoordinates a i w))).re
            = _
  rw [nativeMap_eq_graph]

theorem nativePoint_mem_of_chartDomain {qbig : ℝ} {n : ℕ} {a : ℝ} {i : PolarCharts.Index}
    {w : SpaceTime} (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    nativePoint n w ∈ nativeDomain := by
  apply (nativeMap_polar_mem_iff n a i w).mp
  change _ ∈ ActualPrimary.standardRegion.carrier ∧ True
  exact ⟨hw.2.2.2.1.1, trivial⟩

/-- The literal finite potential has exactly the physical curl required by the
particular stage of the correction cycle, throughout each valid current chart. -/
theorem localPotential_curl_eqOn
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (qbig : ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact localPotential_curl H hN n ha i hw.2.1 (nativePoint_mem_of_chartDomain hw)

/-- The pressure uses the same finite harmonic and label sums and the square of
the physical velocity scale. -/
theorem localPressure_eqOn
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (qbig : ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (localPressure (ActualCycleParameters.particularState x) n)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
            (ActualPrimary.commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact localPressure_eq H n ha i hw.2.1

end NavierStokes.ActualCurrentParticularAssembly

end
end

end

section

/-!
# Exact exterior vanishing of the actual mean fields

The native moving support is the nominal profile interval itself.  Squaring
the exact normalized-radius identity places the physical support in the closed
nominal active annulus, without enlarging either edge.  This applies to the
literal initialized fields and to every mean stage of the same coherent cycle.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualMeanExterior

open Set Function Filter ProblemStatement
open PhysicalWaveSum PhysicalMeanJetBounds
open CorrectionInitialization.ActualPrimary ActualMeanPhysicalData
open scoped Topology

section Support

variable {degree : ℝ} {N Δ : ℕ}

/-- The actual moving radial support gives the closed nominal active annulus
at every physical support point with a comparable band. -/
theorem active_of_mem_tsupport
    (D : CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ h w ≤ ChartScales.Q N) (hs : w ∈ tsupport D.field) :
    w ∈ ActualPolarCoverage.active := by
  have hqpos := physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht
  obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N hqpos hq
  have hu : (graph h n (D.gap n) w).2.1 ∈ standardRegion.carrier :=
    PhysicalStageSupport.comparable_graph_mem outgoing.data.h_pos
      outgoing.data.h_lt_half n (D.gap n) ht hqn hnq
  have hr := D.native_ratio_on_tsupport outgoing.data.h_pos outgoing.data.h_lt_half
    standardRegion.isOpen (ActualMeanStageData.nativeSupport_of_moving D Hm)
    n hn ht hu hs
  change (graph h n (D.gap n) w).1 /
      VariableGaugeMean.qLength (2 * h) (graph h n (D.gap n) w).2.1 ∈
    Icc (PrimaryTargetBounds.leftRadius nominal)
      (PrimaryTargetBounds.rightRadius nominal) at hr
  have ha := PrimaryTargetBounds.leftRadius_pos nominal
  have hb := PrimaryTargetBounds.rightRadius_pos nominal
  have hnonneg := ha.le.trans hr.1
  have hlower := (sq_le_sq₀ ha.le hnonneg).mpr hr.1
  have hupper := (sq_le_sq₀ hnonneg hb.le).mpr hr.2
  have hsq := ActualPolarCoverage.graph_profileRadius_sq outgoing.data.h_pos
    outgoing.data.h_lt_half n (D.gap n) ht
  have hasq : PrimaryTargetBounds.leftRadius nominal ^ 2 =
      2 * NominalConeAssembly.activeLeft nominal :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos nominal).le)
  have hbsq : PrimaryTargetBounds.rightRadius nominal ^ 2 =
      2 * NominalConeAssembly.activeRight nominal :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos nominal).le)
  change (SlowBorelBase.cartesianChart h w).2.1 ∈
    Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal)
  constructor <;> nlinarith

theorem not_mem_tsupport_of_exterior
    (D : CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ h w ≤ ChartScales.Q N) (he : w ∉ ActualPolarCoverage.active) :
    w ∉ tsupport D.field :=
  fun hs => he (active_of_mem_tsupport D Hm ht hq hs)

/-- Scalar coefficients and their Cartesian angular realization vanish as
germs on the exterior of the closed nominal active annulus. -/
theorem exterior_zero_germs
    (D : CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ h w ≤ ChartScales.Q N) (he : w ∉ ActualPolarCoverage.active) :
    (D.field =ᶠ[𝓝 w] fun _ => 0) ∧ (D.angularField =ᶠ[𝓝 w] fun _ => 0) := by
  have hs := not_mem_tsupport_of_exterior D Hm ht hq he
  exact ⟨notMem_tsupport_iff_eventuallyEq.mp hs, D.angularField_zero_germ hs⟩

theorem exterior_zero
    (D : CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ h w ≤ ChartScales.Q N) (he : w ∉ ActualPolarCoverage.active) :
    D.field w = 0 ∧ D.angularField w = 0 := by
  have hg := exterior_zero_germs D Hm ht hq he
  exact ⟨hg.1.eq_of_nhds, hg.2.eq_of_nhds⟩

/-- The direct angular-field constructor used for both angular velocity and
stream potentials retains the same exact exterior zero. -/
theorem actualAngularData_exterior
    (D : CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hbound : qbig ≤ ChartScales.Q N)
    {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ h w < qbig) (he : w ∉ ActualPolarCoverage.active) :
    DirectAngularDiagonal.angularField
      (ActualMeanStageData.actualAngularData D Hm qbig hbound).scalar w = 0 := by
  rw [ActualMeanStageData.actualAngularData_field]
  exact (exterior_zero D Hm ht (hq.le.trans hbound) he).2

end Support

/-! ## The same initialized fields -/

section Initial

variable (B N0 N : ℕ) {w : SpaceTime}
    (ht : w ∈ preterminal) (hq : physicalQ h w ≤ ChartScales.Q N)
    (he : w ∉ ActualPolarCoverage.active)

include ht hq he

theorem initialAngular_exterior :
    (initialAngularFamily B N0 N).field w = 0 ∧
      (initialAngularFamily B N0 N).angularField w = 0 :=
  exterior_zero (initialAngularFamily B N0 N) (initial_mean_moving B N0).angular ht hq he

theorem initialPressure_exterior :
    (initialPressureFamily B N0 N).field w = 0 ∧
      (initialPressureFamily B N0 N).angularField w = 0 :=
  exterior_zero (initialPressureFamily B N0 N) (initial_pressure_moving B N0) ht hq he

theorem initialTemporal_exterior :
    (initialTemporalFamily B N0 N).field w = 0 ∧
      (initialTemporalFamily B N0 N).angularField w = 0 :=
  exterior_zero (initialTemporalFamily B N0 N) (initialTemporal_moving B N0) ht hq he

theorem initialRank_exterior :
    (initialRankFamily B N0 N).field w = 0 ∧
      (initialRankFamily B N0 N).angularField w = 0 :=
  exterior_zero (initialRankFamily B N0 N) (initialRank_moving B N0) ht hq he

/-- The full initialized stream is the literal temporal-plus-rank stream. -/
theorem initialStream_exterior :
    (initialStreamFamily B N0 N).field w = 0 ∧
      (initialStreamFamily B N0 N).angularField w = 0 :=
  exterior_zero (initialStreamFamily B N0 N) (initialStream_moving B N0) ht hq he

end Initial

/-! ## Every stage of the same coherent cycle -/

section Cycles

open CorrectionStep CorrectionState

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    (H : InitialCycleInput B N0 N p) (j : ℕ) {w : SpaceTime}
    (ht : w ∈ preterminal) (hq : physicalQ h w ≤ ChartScales.Q N)
    (he : w ∉ ActualPolarCoverage.active)

private theorem seed_reconstructed :
    (VariableGaugeMean.reconstructState initialGeometry.gauge (commonContext B)
      (ActualInitialization.initialCycleState B N0).state).pressure =
      (ActualInitialization.initialCycleState B N0).state.pressure := by
  rw [initialGeometry_gauge]
  rfl

include ht hq he

theorem cycleAngular_exterior :
    ((initialCycleData H).angularFamily j).field w = 0 ∧
      ((initialCycleData H).angularFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).angularFamily j)
    ((initialCycleData H).primitives j).mean.angular ht hq he

theorem cyclePressure_exterior :
    ((initialCycleData H).pressureFamily j).field w = 0 ∧
      ((initialCycleData H).pressureFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).pressureFamily j)
    ((initialCycleData H).pressure_moving seed_reconstructed j) ht hq he

theorem cycleAngularIncrement_exterior :
    ((initialCycleData H).angularIncrementFamily j).field w = 0 ∧
      ((initialCycleData H).angularIncrementFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).angularIncrementFamily j)
    ((initialCycleData H).angularIncrement_moving j) ht hq he

theorem cyclePressureIncrement_exterior :
    ((initialCycleData H).pressureIncrementFamily j).field w = 0 ∧
      ((initialCycleData H).pressureIncrementFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).pressureIncrementFamily j)
    ((initialCycleData H).pressureIncrement_moving seed_reconstructed j) ht hq he

theorem cycleTemporal_exterior :
    ((initialCycleData H).temporalFamily j).field w = 0 ∧
      ((initialCycleData H).temporalFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).temporalFamily j)
    ((initialCycleData H).temporal_moving j) ht hq he

theorem cycleRank_exterior :
    ((initialCycleData H).rankFamily j).field w = 0 ∧
      ((initialCycleData H).rankFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).rankFamily j)
    ((initialCycleData H).rank_moving j) ht hq he

theorem cycleStream_exterior :
    ((initialCycleData H).streamFamily j).field w = 0 ∧
      ((initialCycleData H).streamFamily j).angularField w = 0 :=
  exterior_zero ((initialCycleData H).streamFamily j)
    ((initialCycleData H).stream_moving j) ht hq he

end Cycles

end NavierStokes.ActualMeanExterior

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCandidateAssembly

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-! ## Exterior germs for physical stages

One certificate supplies support and axis-germ bounds. The existing exterior
lemmas on closed sublevels remain available; they imply this local certificate.
-/

theorem axis_not_active {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (ha : PhysicalGraphBounds.radialProjection w = 0) : w ∉ ActualPolarCoverage.active := by
  intro hm
  have hr := ((ActualCurrentWaveSupport.profileRadius_mem_iff_active ht).mpr hm).1
  rw [ActualCurrentWaveSupport.profileRadius_zero_of_axis h ha] at hr
  exact (not_le_of_gt (PrimaryTargetBounds.leftRadius_pos nominal)) hr

/-- The exterior of the active annulus is open within the preterminal region: the profile
radius is continuous there and the annulus is its preimage of a closed interval. -/
theorem eventually_not_active {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (he : w ∉ ActualPolarCoverage.active) :
    ∀ᶠ y in 𝓝 w, y ∉ ActualPolarCoverage.active := by
  have hr : ActualCurrentWaveSupport.profileRadius h w ∉
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) :=
    fun hm => he ((ActualCurrentWaveSupport.profileRadius_mem_iff_active ht).mp hm)
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds ht,
    ActualCurrentWaveSupport.profileRadius_continuousAt outgoing.data.h_pos
      outgoing.data.h_lt_half ht (isClosed_Icc.isOpen_compl.mem_nhds hr)] with y hy hyr
  exact fun hm => hyr ((ActualCurrentWaveSupport.profileRadius_mem_iff_active hy).mpr hm)

/-- A stage field of the actual candidate: zero near every point of the physical domain
outside the active annulus. -/
structure PhysicalStage (B N0 : ℕ) {V : Type*} [Zero V]
    (f : SpaceTime → V) : Prop where
  /-- The field vanishes in a neighborhood of each exterior point. -/
  exterior : ∀ w ∈ ActualCandidateConstruction.physicalDomain B N0,
    w ∉ ActualPolarCoverage.active → f =ᶠ[𝓝 w] fun _ => 0

namespace PhysicalStage

variable {B N0 : ℕ} {V : Type*} [Zero V] {f : SpaceTime → V}

/-- A pointwise exterior identity suffices, since the exterior is open in the domain. -/
theorem of_eq_zero (hz : ∀ w ∈ ActualCandidateConstruction.physicalDomain B N0,
    w ∉ ActualPolarCoverage.active → f w = 0) : PhysicalStage B N0 f := by
  refine ⟨fun w hw he => ?_⟩
  filter_upwards [(CutStageEstimates.physicalSublevel_open outgoing.data.h_pos
    outgoing.data.h_lt_half (ActualCandidateConstruction.qbig B N0)).mem_nhds hw,
    eventually_not_active hw.1 he] with y hy hye
  exact hz y hy hye

/-- The zero field is a physical stage. -/
theorem zero : PhysicalStage B N0 (fun _ : SpaceTime => (0 : V)) :=
  ⟨fun _ _ _ => Filter.EventuallyEq.rfl⟩

theorem eq_zero (hf : PhysicalStage B N0 f) {w : SpaceTime}
    (hw : w ∈ ActualCandidateConstruction.physicalDomain B N0)
    (he : w ∉ ActualPolarCoverage.active) : f w = 0 :=
  (hf.exterior w hw he).eq_of_nhds

/-- Shrinking support: a support point lies in the active annulus, whose outer edge is
below the outer constant. -/
theorem support {V : Type*} [NormedAddCommGroup V] {f : SpaceTime → V}
    (hf : PhysicalStage B N0 f) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) f := by
  intro w ht hq hn
  have ha : w ∈ ActualPolarCoverage.active := by
    by_contra hna
    exact hn (hf.eq_zero ⟨ht, hq⟩ hna)
  have hr := ((ActualCurrentWaveSupport.profileRadius_mem_iff_active ht).mpr ha).2.trans
    ActualCurrentWaveSupport.rightRadius_le_actualOuterConstant
  exact (div_le_iff₀ (Real.sqrt_pos.mpr
    (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht))).mp hr

/-- The axis of the local domain lies outside the active annulus, so the hub's axis zero
germ is a projection. -/
theorem axisZeroOn {f : VelocityField} (hf : PhysicalStage B N0 f) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0)) f :=
  fun w hw ha => hf.exterior w hw (axis_not_active hw.1 ha)

/-- Exterior zero germs are preserved by addition. -/
theorem add {V : Type*} [AddZeroClass V] {f g : SpaceTime → V}
    (hf : PhysicalStage B N0 f) (hg : PhysicalStage B N0 g) :
    PhysicalStage B N0 (f + g) := by
  refine ⟨fun w hw he => ?_⟩
  filter_upwards [hf.exterior w hw he, hg.exterior w hw he] with y hy hz
  simp only [Pi.add_apply, hy, hz, add_zero]

end PhysicalStage

/-! ## The finite initialization, without the base fields -/

/-- Initial potential, given by `InitialPhysicalData.potential B N0 +
ActualCandidateConstruction.streamMeanStages B N0 0`. -/
noncomputable def initialPotential (B N0 : ℕ) : VelocityField :=
  InitialPhysicalData.potential B N0 + ActualCandidateConstruction.streamMeanStages B N0 0

/-- Initial pressure, given by `InitialPhysicalData.pressure B N0 +
ActualCandidateConstruction.pressureMeanStages B N0 0`. -/
noncomputable def initialPressure (B N0 : ℕ) : PressureField :=
  InitialPhysicalData.pressure B N0 + ActualCandidateConstruction.pressureMeanStages B N0 0

/-- Initial direct, given by `ActualCandidateConstruction.angularMeanStages B N0 0`. -/
noncomputable def initialDirect (B N0 : ℕ) : VelocityField :=
  ActualCandidateConstruction.angularMeanStages B N0 0

/-- Initial direct data, constructed using `ActualMeanStageData.initialAngularData`. -/
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

/-- The initial potential has an exterior zero germ on its physical domain. -/
theorem initialPotential_stage (B N0 : ℕ) : PhysicalStage B N0 (initialPotential B N0) :=
  PhysicalStage.of_eq_zero fun _ hw he => initialPotential_exterior B N0 hw.1 hw.2.le he

/-- The initial pressure has an exterior zero germ on its physical domain. -/
theorem initialPressure_stage (B N0 : ℕ) : PhysicalStage B N0 (initialPressure B N0) :=
  PhysicalStage.of_eq_zero fun _ hw he => initialPressure_exterior B N0 hw.1 hw.2.le he

/-- The initial direct field has an exterior zero germ on its physical domain. -/
theorem initialDirect_stage (B N0 : ℕ) : PhysicalStage B N0 (initialDirect B N0) :=
  PhysicalStage.of_eq_zero fun _ hw he => initialDirect_exterior B N0 hw.1 hw.2.le he

theorem initialPotential_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialPotential B N0) :=
  (initialPotential_stage B N0).support

theorem initialPressure_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialPressure B N0) :=
  (initialPressure_stage B N0).support

theorem initialDirect_support (B N0 : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (initialDirect B N0) :=
  (initialDirect_stage B N0).support

theorem initialPotential_axisZeroOn (B N0 : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (initialPotential B N0) :=
  (initialPotential_stage B N0).axisZeroOn

/-! ## The literal zeroth potential and pressure retain the base -/

/-- Zeroth potential, given by `TailGaugePotential.finalPotential certificate modulation upper B
+ initialPotential B N0`. -/
noncomputable def zerothPotential (B N0 : ℕ) : VelocityField :=
  TailGaugePotential.finalPotential certificate modulation upper B + initialPotential B N0

/-- Zeroth pressure, given by `FinalSlowBase.pressure certificate modulation upper B +
initialPressure B N0`. -/
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

/-- Particular potential, given by `ActualValidBandWaves.potential
(ActualCandidateConstruction.cycle B N0 j) (ActualCandidateConstruction.firstBand B N0)`. -/
noncomputable def particularPotential (B N0 j : ℕ) : VelocityField :=
  ActualValidBandWaves.potential (ActualCandidateConstruction.cycle B N0 j)
    (ActualCandidateConstruction.firstBand B N0)

/-- Particular pressure, constructed using `ActualValidBandWaves.pressure`. -/
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

/-- Run data, bundling `invariant`, `step`, `particular`. -/
noncomputable def runData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ActualStageEstimates.RunData B N0 where
  invariant := ActualCyclePreservation.state_invariant B N0 hN
  step := ActualCyclePreservation.stateStepData B N0 hN
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

/-- Signed potential, constructed using `ActualSignedExterior.cyclePotential`. -/
noncomputable def signedPotential (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : VelocityField :=
  ActualSignedExterior.cyclePotential (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCandidateConstruction.cycle B N0 j)
      (postParticularResult B N0 hN j).primitive)

/-- Signed pressure, constructed using `ActualSignedExterior.cyclePressure`. -/
noncomputable def signedPressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : PressureField :=
  ActualSignedExterior.cyclePressure (ActualCandidateConstruction.cycle B N0 j)
    (postParticularResult B N0 hN j).primitive
    (ActualSignedPhysicalBinding.afterParticular_pressure (ActualCandidateConstruction.cycle B N0 j)
      (postParticularResult B N0 hN j).primitive)

/-- Positive potential, given by `particularPotential B N0 j + signedPotential B N0 hN j +
ActualCandidateConstruction.streamMeanStages B N0 (j + 1)`. -/
noncomputable def positivePotential (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : VelocityField :=
  particularPotential B N0 j + signedPotential B N0 hN j +
    ActualCandidateConstruction.streamMeanStages B N0 (j + 1)

/-- Positive pressure, given by `particularPressure B N0 j + signedPressure B N0 hN j +
ActualCandidateConstruction.pressureMeanStages B N0 (j + 1)`. -/
noncomputable def positivePressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) : PressureField :=
  particularPressure B N0 j + signedPressure B N0 hN j +
    ActualCandidateConstruction.pressureMeanStages B N0 (j + 1)

/-- Direct data, given by `ActualCandidateConstruction.directData (meanCycleInput B N0 hN)`. -/
noncomputable def directData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain h (ActualCandidateConstruction.qbig B N0)) :=
  ActualCandidateConstruction.directData (meanCycleInput B N0 hN)

/-- Potential stages, given by `GermCandidateAssembly.potentialStages certificate modulation
upper B (initialPotential B N0) (positivePotential B N0 hN)`. -/
noncomputable def potentialStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : ℕ → VelocityField :=
  GermCandidateAssembly.potentialStages certificate modulation upper B
    (initialPotential B N0) (positivePotential B N0 hN)

/-- Direct stages, given by `LocalAngularDiagonal.rawSeries (directData B N0 hN)`. -/
noncomputable def directStages (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) : ℕ → VelocityField :=
  LocalAngularDiagonal.rawSeries (directData B N0 hN)

/-- Pressure stages, given by `MixedCandidateAssembly.pressureStages certificate modulation
upper B (initialPressure B N0) (positivePressure B N0 hN)`. -/
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

/-- The stream correction inherits its zero germs from its exterior identity. -/
theorem stream_stage {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0) (j : ℕ) :
    PhysicalStage B N0 (ActualCandidateConstruction.streamMeanStages B N0 j) :=
  PhysicalStage.of_eq_zero fun _ hw he => stream_exterior M j hw.1 hw.2.le he

/-- The mean pressure inherits its zero germs from its exterior identity. -/
theorem meanPressure_stage {B N0 : ℕ} (M : ActualCandidateConstruction.MeanCycleInput B N0)
    (j : ℕ) : PhysicalStage B N0 (ActualCandidateConstruction.pressureMeanStages B N0 j) :=
  PhysicalStage.of_eq_zero fun _ hw he => meanPressure_exterior M j hw.1 hw.2.le he

theorem particular_stage (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    PhysicalStage B N0 (particularPotential B N0 j) ∧
      PhysicalStage B N0 (particularPressure B N0 j) :=
  ⟨⟨fun _ hw he => (particular_zero_germs B N0 hN j hw he).1⟩,
    ⟨fun _ hw he => (particular_zero_germs B N0 hN j hw he).2⟩⟩

theorem signed_stage (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    PhysicalStage B N0 (signedPotential B N0 hN j) ∧
      PhysicalStage B N0 (signedPressure B N0 hN j) :=
  ⟨⟨fun _ hw he => (signed_zero_germs B N0 hN j hw.1 he).1⟩,
    ⟨fun _ hw he => (signed_zero_germs B N0 hN j hw.1 he).2⟩⟩

/-- The positive stages are sums of three physical stages. -/
theorem positive_stage (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    PhysicalStage B N0 (positivePotential B N0 hN j) ∧
      PhysicalStage B N0 (positivePressure B N0 hN j) :=
  ⟨((particular_stage B N0 hN j).1.add (signed_stage B N0 hN j).1).add
      (stream_stage (meanCycleInput B N0 hN) (j + 1)),
    ((particular_stage B N0 hN j).2.add (signed_stage B N0 hN j).2).add
      (meanPressure_stage (meanCycleInput B N0 hN) (j + 1))⟩

theorem particular_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (particularPotential B N0 j) ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (particularPressure B N0 j) :=
  ⟨(particular_stage B N0 hN j).1.support, (particular_stage B N0 hN j).2.support⟩

theorem particular_axisZeroOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (particularPotential B N0 j) :=
  (particular_stage B N0 hN j).1.axisZeroOn

theorem support_of_exterior_zero {V : Type*} [NormedAddCommGroup V]
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
  ⟨(signed_stage B N0 hN j).1.support, (signed_stage B N0 hN j).2.support⟩

theorem signed_axisZeroOn (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
      (signedPotential B N0 hN j) :=
  (signed_stage B N0 hN j).1.axisZeroOn

theorem positivePotential_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (positivePotential B N0 hN j) :=
  (positive_stage B N0 hN j).1.support

theorem positivePressure_support (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (ActualCandidateConstruction.qbig B N0) (positivePressure B N0 hN j) :=
  (positive_stage B N0 hN j).2.support

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
  (positive_stage B N0 hN j).1.axisZeroOn

theorem positive_exterior (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) {w : SpaceTime}
    (hw : w ∈ ActualCandidateConstruction.physicalDomain B N0)
    (he : w ∉ ActualPolarCoverage.active) :
    positivePotential B N0 hN j w = 0 ∧ positivePressure B N0 hN j w = 0 :=
  ⟨(positive_stage B N0 hN j).1.eq_zero hw he, (positive_stage B N0 hN j).2.eq_zero hw he⟩

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

/-- Estimates, constructed using `GluedStageEstimates.actualStageEstimates`. -/
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

/-- Selected potential stages, constructed using `potentialStages`. -/
noncomputable def selectedPotentialStages : ℕ → VelocityField :=
  potentialStages ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

/-- Selected direct stages, constructed using `directStages`. -/
noncomputable def selectedDirectStages : ℕ → VelocityField :=
  directStages ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

/-- Selected pressure stages, constructed using `pressureStages`. -/
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
