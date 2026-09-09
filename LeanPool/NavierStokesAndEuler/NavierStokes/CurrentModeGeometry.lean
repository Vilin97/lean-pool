/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentPhysicalModeGerms
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentWaveSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentPhysicalChartJets

/-!
# Geometry of the actual current-mode evaluation point

The physical validity band and the closed nominal radial interval place
the normalized Cartesian coordinates in a fixed compact annulus.  The
same current common-cover chart has the actual native slow domain and
exactly the physical profile radius.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CurrentModeGeometry

open Set Function Filter ProblemStatement CorrectionInitialization
open scoped Topology ContDiff


/-- Chart inner, given by `PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4`. -/
noncomputable def chartInner : ℝ := PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4

/-- Chart outer, given by `2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal`. -/
noncomputable def chartOuter : ℝ := 2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal

theorem chartInner_pos : 0 < chartInner :=
  div_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) (by norm_num)

theorem chartOuter_pos : 0 < chartOuter :=
  mul_pos (by norm_num) (PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal)

theorem chartInner_lt_chartOuter : chartInner < chartOuter := by
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hab := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  dsimp [chartInner, chartOuter]
  linarith

theorem band_q_comparison (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n) :
    PhysicalWaveSum.physicalQ ActualPrimary.h w / 2 ≤ ChartScales.Q n ∧
      ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ ActualPrimary.h w := by
  constructor <;> linarith [hw.2.1, hw.2.2]

/-- The annulus is derived from the actual physical ratio, independently
of any field support or coherent-family assumption. -/
theorem scaledRadial_mem_annulus (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hr : ActualCurrentWaveSupport.profileRadius ActualPrimary.h w ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus chartInner chartOuter := by
  have hc := band_q_comparison n hw
  have hlen := PhysicalMeanJetBounds.graph_length_bounds ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw.1 hc.1 hc.2
  have hell := PhysicalMeanJetBounds.graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw.1
  have hratio : (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 /
      VariableGaugeMean.qLength (2 * ActualPrimary.h)
        (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).2.1 ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
    rw [ActualCurrentWaveSupport.graph_profileRadius_eq ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half n 0 hw.1]
    exact hr
  have hloR := (le_div_iff₀ hell).mp hratio.1
  have hhiR := (div_le_iff₀ hell).mp hratio.2
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hlow : PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 2 ≤
      (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 := by nlinarith [hlen.1]
  have hupp : (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 ≤
      2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by nlinarith [hlen.2]
  rw [PhysicalMeanJetBounds.graph_radius] at hlow hupp
  refine ⟨?_, ?_⟩
  · simpa only [chartOuter, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius _).trans hupp
  · change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 ≤
      ‖PhysicalGraphBounds.scaledRadial n w‖
    linarith only [hlow, PolarCharts.radius_le_two_norm (PhysicalGraphBounds.scaledRadial n w)]

/-- The literal current common-cover evaluation point used in the
physical mode estimates. -/
noncomputable def point (a : ℝ) (i : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    PhysicalParticularWave.WaveSpace :=
  CurrentPhysicalChartJets.chartMap a i
    (PhysicalWaveSum.commonLift ActualPrimary.h n (CurrentPhysicalModeGerms.commonGap n) w)

theorem point_eq_nativeMap (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    point a i n w = PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w) :=
  (CurrentPhysicalModeGerms.nativeMap_commonChart n ha i hc).symm

theorem point_mem_nativeDomain (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    point a i n w ∈ ActualCurrentParticularPhysical.nativeDomain := by
  rw [point_eq_nativeMap n ha i hc,
    ActualCurrentParticularPhysical.nativeMap_polar_mem_iff]
  exact ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, mem_univ _⟩

theorem point_profileRadius (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (ht : w.1 < 1)
    (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm (point a i n w)) =
      ActualCurrentWaveSupport.profileRadius ActualPrimary.h w := by
  rw [point_eq_nativeMap n ha i hc, CurrentPhysicalModeGerms.physical_polarCoordinates n ha i hc]
  have he : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm
      (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n w))) =
      ActualCoreSupport.radialRatio
        (ActualCarrierTransport.associatedPoint
          (ActualCurrentParticularPhysical.nativePoint n w).1.1
          (ActualCurrentParticularPhysical.nativePoint n w).2) := by
    change (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n w)).1.1.1
            /
        VariableGaugeMean.qLength (2 * ActualPrimary.h)
          (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
            (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n
                w)).1.1.2 =
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 /
        VariableGaugeMean.qLength (2 * ActualPrimary.h)
          (ActualCurrentParticularPhysical.nativePoint n w).1.1.2
    simp only [PhysicalParticularWave.nativeMap, PhysicalParticularWave.waveEquiv_apply,
      PhysicalResidualBridge.ScaledGraph.map, ResidualPolarGraph.cylindricalPoint,
      ActualCurrentParticularPhysical.nativePoint, ActualCurrentParticularPhysical.cylinderPoint,
      AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_two]
  rw [he, ActualCurrentWaveSupport.nativePoint_profileRadius n ht]

theorem point_mem_closed_window (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i)
    (hr : ActualCurrentWaveSupport.profileRadius ActualPrimary.h w ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    point a i n w ∈ ActualCurrentParticularPhysical.nativeDomain ∧
      ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm (point a i n w)) ∈
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  refine ⟨point_mem_nativeDomain n ha i hw hc, ?_⟩
  rwa [point_profileRadius n ha i hw.1 hc]

end NavierStokes.CurrentModeGeometry
