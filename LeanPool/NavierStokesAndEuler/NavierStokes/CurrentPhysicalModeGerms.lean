/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualPolarGraph
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentPhysicalChartJets

@[expose] public section

/-!
# Normalized polar germs of the actual current particular modes

The native point below uses the actual common-cover index.  The ambient
germs retain the current solve, its chosen phase, and its Cartesian rotation.
-/

noncomputable section

namespace NavierStokes.CurrentPhysicalModeGerms

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep CorrectionInitialization
open scoped Topology ContDiff


abbrev Label (B N0 : ℕ) := ActualCurrentParticularPhysical.Label B N0

/-- The cover gap of the actual current-band graph. -/
noncomputable def commonGap (n : ℕ) : ℕ :=
  ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n -
    CommonWindow.index CorrectionInitialization.ActualPrimary.h n

theorem commonGap_le (n : ℕ) :
    commonGap n ≤ ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n :=
  Nat.sub_le _ _

theorem commonGap_index (n : ℕ) :
    ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n - commonGap n =
      CommonWindow.index CorrectionInitialization.ActualPrimary.h n :=
  Nat.sub_sub_self (CommonWindow.index_le_native CorrectionInitialization.ActualPrimary.h n)

theorem liftXY_common (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w) =
      PhysicalGraphBounds.scaledRadial n w :=
  PhysicalGraphBounds.liftXY_physicalLift h n w

/-- The exact common-lift chart is the same cylindrical graph as the
one used by the current physical solve. -/
theorem cylinderAt_commonLift (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n - d)).map
        (ResidualPolarGraph.cylindricalPoint a i n w) := by
  have hl : PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w) ∈
      PolarCharts.chartDomain a i := by
    rwa [liftXY_common]
  apply PhysicalResidualTZ.swapCylinder.injective
  change PhysicalResidualTZ.swapCylinder
    (ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w)) =
      PhysicalResidualTZ.graphMapTZ
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n - d)) (ResidualPolarGraph.cylindricalPoint a i n w)
  rw [ResidualPolarGraph.graphMapTZ_cylindricalPoint ha h i n d hd hw]
  apply Prod.ext
  · change PhysicalResidualTZ.swapSlow
      (ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w)).1 =
        PhysicalMeanJetBounds.graph h n d w
    rw [ActualSignedPhysicalData.cylinderAt_fst ha i hl]
    rfl
  · change (PolarCharts.chart a i
      (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w))).2 =
        (PolarCharts.chart a i (PhysicalGraphBounds.scaledRadial n w)).2
    rw [liftXY_common]

theorem realVector_smul (c : ℝ) (v : HarmonicCalculus.ComplexVector) :
    PhysicalCurlCovariance.realVector (c • v) =
      c • PhysicalCurlCovariance.realVector v := by
  ext i
  fin_cases i <;> simp [PhysicalCurlCovariance.realVector, Complex.real_smul]

theorem radialProjection_eq_sqrt_smul (n : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.radialProjection w =
      Real.sqrt (ChartScales.Q n) • PhysicalGraphBounds.scaledRadial n w := by
  have hscale : Real.sqrt (ChartScales.Q n) * ChartScales.Q n ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (ChartScales.Q_pos n)]
    norm_num
  change PhysicalGraphBounds.radialProjection w =
    Real.sqrt (ChartScales.Q n) •
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) • PhysicalGraphBounds.radialProjection w)
  rw [smul_smul, hscale, one_smul]

theorem physical_chart_mem (n : ℕ) {a : ℝ} (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    w ∈ ActualMeanPotentialRealization.cartesianDomain (Real.sqrt (ChartScales.Q n) * a) i := by
  change PhysicalGraphBounds.radialProjection w ∈
    PolarCharts.chartDomain (Real.sqrt (ChartScales.Q n) * a) i
  rw [radialProjection_eq_sqrt_smul n w]
  exact CurrentPhysicalChartJets.chartDomain_smul (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) i hw

theorem physical_chart_angle (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    (PolarCharts.chart (Real.sqrt (ChartScales.Q n) * a) i
      (PhysicalGraphBounds.radialProjection w)).2 = ResidualPolarGraph.angle a i n w := by
  rw [radialProjection_eq_sqrt_smul n w]
  have hh := CurrentPhysicalChartJets.chart_smul ha
    (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) i hw
  have he := congrArg Prod.snd hh
  simpa only [ResidualPolarGraph.angle] using he

/-- The physical chart uses the same angular branch as the normalized
chart, with the physical radius restored. -/
theorem physical_polarCoordinates (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w =
      ResidualPolarGraph.cylindricalPoint a i n w := by
  have hp : PolarCharts.chart (Real.sqrt (ChartScales.Q n) * a) i
      (PhysicalGraphBounds.radialProjection w) =
        (PolarCharts.radius (PhysicalGraphBounds.radialProjection w), ResidualPolarGraph.angle a i
          n w) :=
    Prod.ext (ActualSignedPhysicalData.chart_radius
      (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw))
      (physical_chart_angle n ha i hw)
  simp only [PhysicalCurlCovariance.polarCoordinates, PhysicalCurlCovariance.polarInput,
    hp, ResidualPolarGraph.cylindricalPoint]

/-- The current native map uses the common index, as opposed to the
larger native index of the unmodified lift. -/
theorem nativeMap_commonChart (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w) =
        PhysicalParticularWave.waveEquiv
          (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w)) := by
  rw [physical_polarCoordinates n ha i hw, PhysicalParticularWave.nativeMap,
    ← commonGap_index n]
  exact congrArg PhysicalParticularWave.waveEquiv
    (cylinderAt_commonLift ActualPrimary.h n (commonGap n) (commonGap_le n) ha i hw).symm

theorem rotation_commonLift (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w) =
      CartesianCopySource.rotationMap
        (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w)) := by
  rw [liftXY_common]
  exact (CurrentPhysicalChartJets.rotationMap_smul
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (-(1 / 2 : ℝ)))
    (PhysicalGraphBounds.radialProjection w)).symm

variable {B N0 : ℕ}

/-- Pointwise equality to the literal current potential on a valid
normalized polar chart. -/
theorem localPotentialMode_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
      n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n w =
      ChartScales.Q n ^ (-ActualPrimary.h) • PhysicalCurlCovariance.realVector
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n)
            w))
          (ActualCurrentParticularPhysical.nativePotential x l j n
            (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
              (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w))))) := by
  unfold ActualCurrentParticularPhysical.localPotentialMode
  rw [ActualCurrentParticularPhysical.periodic_cylinderPoint_eq_chart
    (ActualCurrentParticularPhysical.cylindricalPotential_periodic x l j hf n)
    (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw)]
  unfold ActualCurrentParticularPhysical.cylindricalPotential
  rw [nativeMap_commonChart n ha i hw, rotation_commonLift ActualPrimary.h n (commonGap n) w,
    map_smul, realVector_smul]

theorem localPressureMode_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
      n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPressureMode x l j n w =
      ChartScales.Q n ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
        (ActualCurrentParticularPhysical.nativePressure x l j n
          (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w)))).re := by
  rw [ActualCurrentParticularPhysical.localPressureMode_eq_chart x l j hf n
    (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw)]
  unfold ActualCurrentParticularPhysical.cylindricalPressure
  rw [nativeMap_commonChart n ha i hw]

/-- Ambient germ equality, suitable for ordinary Cartesian derivatives
of every order, with the actual common-cover lift. -/
theorem localPotentialMode_germ (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
      n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n =ᶠ[𝓝 w] fun y =>
      ChartScales.Q n ^ (-ActualPrimary.h) • PhysicalCurlCovariance.realVector
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n)
            y))
          (ActualCurrentParticularPhysical.nativePotential x l j n
            (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
              (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) y))))) := by
  filter_upwards [ResidualPolarGraph.eventually_chartDomain i n hw] with y hy
  exact localPotentialMode_eq x l j hf n ha i hy

theorem localPressureMode_germ (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
      n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPressureMode x l j n =ᶠ[𝓝 w] fun y =>
      ChartScales.Q n ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
        (ActualCurrentParticularPhysical.nativePressure x l j n
          (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) y)))).re := by
  filter_upwards [ResidualPolarGraph.eventually_chartDomain i n hw] with y hy
  exact localPressureMode_eq x l j hf n ha i hy

end NavierStokes.CurrentPhysicalModeGerms
