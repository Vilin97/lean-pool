/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanStageData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage

@[expose] public section

/-!
# Exact exterior vanishing of the actual mean fields

The native moving support is the nominal profile interval itself.  Squaring
the exact normalized-radius identity places the physical support in the closed
nominal active annulus, without enlarging either edge.  This applies to the
literal initialized fields and to every mean stage of the same coherent cycle.
-/

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
