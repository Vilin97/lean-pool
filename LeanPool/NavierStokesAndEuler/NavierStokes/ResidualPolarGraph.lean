/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualTZ

@[expose] public section

/-!
# Local polar inverse of the physical residual graph

The physical radius is unscaled, while the angle is read from a valid
polar chart of the scaled radial projection. The resulting cylindrical
point maps back to the original Cartesian point and to the exact common
graph used by the physical mean estimates.
-/

noncomputable section

namespace NavierStokes.ResidualPolarGraph

open Set Filter ProblemStatement
open AxisymmetricResidual (pack pack_zero pack_one pack_two)
open scoped Topology

/-- The local angle of the scaled physical radial projection. -/
noncomputable def angle (a : ℝ) (j : PolarCharts.Index) (n : ℕ) (w : SpaceTime) : ℝ :=
  (PolarCharts.chart a j (PhysicalGraphBounds.scaledRadial n w)).2

/-- The actual unscaled cylindrical point associated with a local polar
chart. Its spatial coordinates are physical radius, angle, and axial position. -/
noncomputable def cylindricalPoint (a : ℝ) (j : PolarCharts.Index) (n : ℕ)
    (w : SpaceTime) : SpaceTime :=
  (w.1, pack (PolarCharts.radius (PhysicalGraphBounds.radialProjection w))
    (angle a j n w) (w.2 2))

@[simp] theorem cylindricalPoint_time (a : ℝ) (j : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    (cylindricalPoint a j n w).1 = w.1 := rfl

@[simp] theorem cylindricalPoint_radius (a : ℝ) (j : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    (cylindricalPoint a j n w).2 0 =
      PolarCharts.radius (PhysicalGraphBounds.radialProjection w) := by
  simp [cylindricalPoint]

@[simp] theorem cylindricalPoint_angle (a : ℝ) (j : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    (cylindricalPoint a j n w).2 1 = angle a j n w := by
  simp [cylindricalPoint]

@[simp] theorem cylindricalPoint_axial (a : ℝ) (j : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    (cylindricalPoint a j n w).2 2 = w.2 2 := by
  simp [cylindricalPoint]

theorem rotated_projection_pos {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    0 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection w)).1 := by
  have hs : 0 < (PolarCharts.rotate j (PhysicalGraphBounds.scaledRadial n w)).1 :=
    lt_trans (by positivity : 0 < a / 4) hw
  change 0 < (PolarCharts.rotate j
    ((ChartScales.Q n ^ (-(1 / 2 : ℝ))) • PhysicalGraphBounds.radialProjection w)).1 at hs
  rw [PolarCharts.rotate_smul, Prod.smul_fst, smul_eq_mul] at hs
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)).mp hs

theorem radial_projection_radius_pos {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w) := by
  rw [← PolarCharts.radius_rotate j]
  exact PolarCharts.radius_pos_of_fst_pos (rotated_projection_pos ha j n hw)

theorem cylindricalPoint_radius_pos {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    0 < (cylindricalPoint a j n w).2 0 := by
  rw [cylindricalPoint_radius]
  exact radial_projection_radius_pos ha j n hw

theorem angle_eq_localChart {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    angle a j n w = (PolarCharts.localChart j (PhysicalGraphBounds.radialProjection w)).2 := by
  unfold angle
  rw [PolarCharts.chart_eq_localChart ha j hw]
  change (PolarCharts.localChart j
    ((ChartScales.Q n ^ (-(1 / 2 : ℝ))) • PhysicalGraphBounds.radialProjection w)).2 = _
  rw [PolarCharts.localChart_smul j (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)]

theorem polar_radius_angle {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    PolarCharts.polar (PolarCharts.radius (PhysicalGraphBounds.radialProjection w), angle a j n w) =
      PhysicalGraphBounds.radialProjection w := by
  rw [angle_eq_localChart ha j n hw]
  convert! PolarCharts.polar_localChart j (rotated_projection_pos ha j n hw) using 1
  rw [PolarCharts.localChart_apply]

/-- The spatial cylindrical chart returns the original Cartesian point. -/
theorem chart_cylindricalPoint {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    CylindricalResidual.chart (cylindricalPoint a j n w).2 = w.2 := by
  have hp := polar_radius_angle ha j n hw
  ext i
  fin_cases i
  · simpa [CylindricalResidual.chart, cylindricalPoint, PolarCharts.polar] using congrArg Prod.fst
    hp
  · simpa [CylindricalResidual.chart, cylindricalPoint, PolarCharts.polar] using congrArg Prod.snd
    hp
  · simp [CylindricalResidual.chart, cylindricalPoint]

/-- The time coordinate is unchanged by the actual spatial chart. -/
theorem spacetimeChart_cylindricalPoint {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ((cylindricalPoint a j n w).1, CylindricalResidual.chart (cylindricalPoint a j n w).2) = w := by
  rw [cylindricalPoint_time, chart_cylindricalPoint ha j n hw]

/-- The two frozen graph interfaces use the same linear map in `(T,Z)` order. -/
theorem physicalToChartTZ_eq (h : ℝ) (n k : ℕ) :
    PhysicalResidualTZ.physicalToChartTZ h n k = VariableGaugeMean.physicalToChartTZ h n k := by
  rw [PhysicalResidualTZ.physicalToChartTZ_eq_formula]
  rfl

/-- The absolute cylindrical lift is the actual physical mean input,
including its radial and time auxiliary profile. -/
theorem absoluteLiftTZ_cylindricalPoint (h a : ℝ) (j : PolarCharts.Index) (n : ℕ)
    (w : SpaceTime) :
    PhysicalResidualTZ.absoluteLiftTZ h (cylindricalPoint a j n w) =
      PhysicalMeanJetBounds.physicalPoint h w := by
  simp only [PhysicalResidualTZ.absoluteLiftTZ, PhysicalResidualBridge.absoluteLift,
    cylindricalPoint_time, cylindricalPoint_radius, cylindricalPoint_axial,
    PhysicalResidualTZ.swapSlow_apply, PhysicalMeanJetBounds.physicalPoint,
    PhysicalGraphBounds.radialProfile, PhysicalGraphBounds.radiusPower_eq]
  rfl

/-- Exact compatibility of the residual graph and the mean-field common
cover, with the same native-index gap and the actual local chart angle. -/
theorem graphMapTZ_cylindricalPoint {a : ℝ} (ha : 0 < a) (h : ℝ) (j : PolarCharts.Index)
    (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    PhysicalResidualTZ.graphMapTZ
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d))
      (cylindricalPoint a j n w) =
        (PhysicalMeanJetBounds.graph h n d w, angle a j n w) := by
  rw [PhysicalResidualTZ.commonGraph_eq_physicalToChartTZ h n
    (ChartScales.nativeIndex h n - d) (cylindricalPoint_radius_pos ha j n hw),
    absoluteLiftTZ_cylindricalPoint, physicalToChartTZ_eq,
    ← PhysicalMeanJetBounds.graph_eq_physicalToChartTZ h n d hd w,
    cylindricalPoint_angle]

/-- The radial coordinate of the scaled polar chart is exactly the first
coordinate used by the physical common graph. -/
theorem chart_radius_eq_graph {a : ℝ} (ha : 0 < a) (h : ℝ) (j : PolarCharts.Index)
    (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    (PolarCharts.chart a j (PhysicalGraphBounds.scaledRadial n w)).1 =
      (PhysicalMeanJetBounds.graph h n d w).1 := by
  rw [PhysicalMeanJetBounds.graph_radius, PolarCharts.chart_eq_localChart ha j hw,
    PolarCharts.localChart_apply]

theorem eventually_chartDomain {a : ℝ} (j : PolarCharts.Index) (n : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ∀ᶠ z in 𝓝 w, PhysicalGraphBounds.scaledRadial n z ∈ PolarCharts.chartDomain a j :=
  ((PolarCharts.chartDomain_open a j).preimage (PhysicalGraphBounds.scaledRadial
    n).continuous).mem_nhds hw

theorem spacetimeChart_cylindricalPoint_eventually {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) (n : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    (fun z => ((cylindricalPoint a j n z).1,
      CylindricalResidual.chart (cylindricalPoint a j n z).2)) =ᶠ[𝓝 w] id := by
  filter_upwards [eventually_chartDomain j n hw] with z hz
  exact spacetimeChart_cylindricalPoint ha j n hz

theorem graphMapTZ_cylindricalPoint_eventually {a : ℝ} (ha : 0 < a) (h : ℝ)
    (j : PolarCharts.Index) (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    (fun z => PhysicalResidualTZ.graphMapTZ
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - d))
        (cylindricalPoint a j n z)) =ᶠ[𝓝 w]
      (fun z => (PhysicalMeanJetBounds.graph h n d z, angle a j n z)) := by
  filter_upwards [eventually_chartDomain j n hw] with z hz
  exact graphMapTZ_cylindricalPoint ha h j n d hd hz

end NavierStokes.ResidualPolarGraph
