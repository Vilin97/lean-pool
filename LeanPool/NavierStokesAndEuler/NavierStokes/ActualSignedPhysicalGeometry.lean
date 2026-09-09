/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPotentialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData

@[expose] public section

/-!
# Geometry for current signed waves in physical polar charts

The actual active annulus is covered for every band whose physical scale
ratio lies in `(1/2,2)`.  An explicit change of the chart radius identifies
the scaled Cartesian lift with the full native cylindrical graph.
-/

noncomputable section

namespace NavierStokes.ActualSignedPhysicalGeometry

open Set Function Filter ProblemStatement PhysicalWaveSum
open PhysicalGraphBounds PhysicalMeanJetBounds
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff


/-- The annulus estimate uses only comparability of the two positive scales,
so it holds throughout the full open native scale window. -/
theorem annulus_of_ratio (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ ActualPolarCoverage.active)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    scaledRadial n w ∈ annulus ActualPolarCoverage.inner ActualPolarCoverage.outer := by
  have hQ := ChartScales.Q_pos n
  have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by
    have he := (div_lt_iff₀ hQ).mp hq.2
    linarith
  have hhi : ChartScales.Q n ≤ 2 * physicalQ h w := by
    have he := (lt_div_iff₀ hQ).mp hq.1
    linarith
  have hell := graph_length_pos outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw
  have hlen := graph_length_bounds outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw hlo hhi
  have hr := ActualPolarCoverage.graph_profileRadius_mem nominal n 0 hw hactive
  have hloR := (le_div_iff₀ hell).mp hr.1
  have hhiR := (div_le_iff₀ hell).mp hr.2
  have ha := PrimaryTargetBounds.leftRadius_pos nominal
  have hb := PrimaryTargetBounds.rightRadius_pos nominal
  have hRlo : PrimaryTargetBounds.leftRadius nominal / 2 ≤ (graph h n 0 w).1 := by
    nlinarith [hlen.1]
  have hRhi : (graph h n 0 w).1 ≤ 2 * PrimaryTargetBounds.rightRadius nominal := by
    nlinarith [hlen.2]
  rw [graph_radius] at hRlo hRhi
  refine ⟨?_, ?_⟩
  · simpa only [ActualPolarCoverage.outer, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius (scaledRadial n w)).trans hRhi
  · change PrimaryTargetBounds.leftRadius nominal / 4 ≤ ‖scaledRadial n w‖
    linarith only [hRlo, PolarCharts.radius_le_two_norm (scaledRadial n w)]

theorem chart_exists_of_ratio (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ ActualPolarCoverage.active)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    ∃ j : PolarCharts.Index,
      scaledRadial n w ∈ PolarCharts.chartDomain ActualPolarCoverage.inner j := by
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered ActualPolarCoverage.inner_pos
    (annulus_of_ratio n hw hactive hq)
  exact ⟨j, PolarCharts.sector_subset_chartDomain ActualPolarCoverage.inner_pos j hj⟩

/-- The exact unscaled chart radius corresponding to a native chart radius. -/
noncomputable def chartRadius (a : ℝ) (n : ℕ) : ℝ :=
  a / ChartScales.Q n ^ (-(1 / 2 : ℝ))

theorem chartRadius_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < chartRadius a n :=
  div_pos ha (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)

theorem chartDomain_unscale {a c : ℝ} (hc : 0 < c) (j : PolarCharts.Index)
    {p : PolarCharts.Plane} (hp : c • p ∈ PolarCharts.chartDomain a j) :
    p ∈ PolarCharts.chartDomain (a / c) j := by
  change a / 4 < (PolarCharts.rotate j (c • p)).1 at hp
  rw [PolarCharts.rotate_smul] at hp
  change a / 4 < c * (PolarCharts.rotate j p).1 at hp
  change (a / c) / 4 < (PolarCharts.rotate j p).1
  calc
    (a / c) / 4 = (a / 4) / c := by ring
    _ < _ := (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hp)

theorem physical_chart_mem (n : ℕ) {a : ℝ} (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    radialProjection w ∈ PolarCharts.chartDomain (chartRadius a n) j :=
  chartDomain_unscale (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) j hchart

/-- The scaled and unscaled charts have exactly the same angle. -/
theorem physical_chart_scale (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    PolarCharts.chart a j (scaledRadial n w) =
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) *
        (PolarCharts.chart (chartRadius a n) j (radialProjection w)).1,
       (PolarCharts.chart (chartRadius a n) j (radialProjection w)).2) := by
  rw [PolarCharts.chart_eq_localChart ha j hchart,
    PolarCharts.chart_eq_localChart (chartRadius_pos ha n) j (physical_chart_mem n j hchart)]
  exact PolarCharts.localChart_smul j (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) _

/-- No angle choice or auxiliary coordinate is discarded by this identity. -/
theorem cylinderAt_physical_chart (h : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ActualSignedPhysicalData.cylinderAt a j (physicalLift h n w) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n)).map
          (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w) := by
  have hb := chartRadius_pos ha n
  have hphysical := physical_chart_mem n j hchart
  have hv := ActualSignedPhysicalData.polarCoordinates_valid hb j hphysical
  have he := ActualSignedPhysicalData.polarCoordinates_backward hb j hphysical
  have hc : scaledRadial n
      ((PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w).1,
        CylindricalResidual.chart
          (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w).2) ∈
        PolarCharts.chartDomain a j := by
    rwa [he]
  simpa only [he] using ActualSignedPhysicalData.cylinderAt_physical_forward h n ha j
    (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w) hv.1 hv.2.1 hc

theorem exists_physical_chart (h : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ∃ b : ℝ, 0 < b ∧ radialProjection w ∈ PolarCharts.chartDomain b j ∧
      ActualSignedPhysicalData.cylinderAt a j (physicalLift h n w) =
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n)).map (PhysicalCurlCovariance.polarCoordinates b j w) :=
  ⟨chartRadius a n, chartRadius_pos ha n, physical_chart_mem n j hchart,
    cylinderAt_physical_chart h n ha j hchart⟩

/-- The mean graph's slow coordinate does not depend on its auxiliary cover. -/
theorem graph_slow_mem_standard_of_ratio {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    (graph h n d w).2.1 ∈ (ActualSignedGeometry.standardSlowRegion hh hh1).carrier := by
  change 0 < (graph h n d w).2.1.1 ∧
    SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 ∈ Ioo (1 / 2 : ℝ) 2
  refine ⟨graph_time_pos h n d hw, ?_⟩
  rwa [graph_q_eq hh hh1 n d hw]

/-- This identity is global and needs no radius or time positivity premise. -/
theorem commonGraph_slow (h : ℝ) (n i d : ℕ) (z : SpaceTime) :
    (PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).map z)).1.2.1 =
      (graph h n d (z.1, CylindricalResidual.chart z.2)).2.1 := by
  rw [graph_slow]
  change
    (((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).velocityScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).epsilon) * (1 - z.1),
     ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).epsilon) * z.2 2) = _
  rw [PhysicalResidualBridge.commonGraph_slowTimeScale (ChartScales.Q_pos n),
    PhysicalResidualBridge.commonGraph_axialScale (ChartScales.Q_pos n), Real.rpow_neg_one]
  simp only [CylindricalResidual.chart, AxisymmetricResidual.pack_two]
  congr 1
  ring

theorem nativePoint_slow (n d : ℕ) (z : SpaceTime) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.2.1 =
      (graph h n d (z.1, CylindricalResidual.chart z.2)).2.1 :=
  commonGraph_slow h n (CommonWindow.index h n) d z

theorem nativePoint_mem_physicalDomain (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) / ChartScales.Q n ∈
      Ioo (1 / 2 : ℝ) 2) :
    z ∈ ActualSignedPotentialCoherence.physicalDomain n := by
  refine ⟨hr, ?_⟩
  rw [nativePoint_slow n 0]
  exact graph_slow_mem_standard_of_ratio outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw hq

theorem polarCoordinates_mem_physicalDomain (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : radialProjection w ∈ PolarCharts.chartDomain a j)
    (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    PhysicalCurlCovariance.polarCoordinates a j w ∈
      ActualSignedPotentialCoherence.physicalDomain n := by
  have hv := ActualSignedPhysicalData.polarCoordinates_valid ha j hchart
  have he := ActualSignedPhysicalData.polarCoordinates_backward ha j hchart
  apply nativePoint_mem_physicalDomain n _ hv.1
  · rwa [he]
  · rwa [he]

theorem scaledChart_mem_physicalDomain (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j)
    (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w ∈
      ActualSignedPotentialCoherence.physicalDomain n :=
  polarCoordinates_mem_physicalDomain n (chartRadius_pos ha n) j
    (physical_chart_mem n j hchart) hw hq

end NavierStokes.ActualSignedPhysicalGeometry
