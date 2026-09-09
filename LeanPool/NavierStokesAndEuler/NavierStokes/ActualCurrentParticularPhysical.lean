/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularDynamics
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPotentialRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCycleData

@[expose] public section

/-!
# Physical fields of the actual current-band particular solve

The copy solve in this file is evaluated at the current band.  The choice
of a polar angle depends only on the Cartesian point and is independent
of the band.  No regularity of a fixed-reference continuation is used.
-/

noncomputable section

namespace NavierStokes.ActualCurrentParticularPhysical

open Set Function Filter ProblemStatement HarmonicCalculus
open CorrectionState CorrectionStep CorrectionInitialization
open scoped Topology ContDiff BigOperators


abbrev Label (B N0 : ℕ) := ActualParticularStageControls.Label B N0
abbrev Native := PhysicalParticularWave.WaveSpace

variable {B N0 : ℕ}

/-- The literal current solve, with the canonical geometry already fixed. -/
noncomputable def copyData (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters l).copyData
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j

theorem copyData_eq_actual (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) :
    copyData x l j = ActualParticularCoherence.copyData x l j := by
  unfold copyData ActualParticularCoherence.copyData
  rw [ActualParticularStageControls.parameters_eq_canonical x l hf]

/-- The current common coefficient includes every localized copy cutoff. -/
noncomputable def nativePotential (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) : Native → ComplexVector :=
  (copyData x l j).common.curlPotential
    (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
    (ActualParticularStageControls.directions (B := B)) n

noncomputable def nativePressure (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) : Native → ℂ :=
  mode ((copyData x l j).background.frequency n)
    ((copyData x l j).background.phase n) ((copyData x l j).common.pressure n)

/-- A pointwise polar angle choice.  Its apparent cuts disappear from
periodic physical fields by the chart-agreement theorem below. -/
noncomputable def angle (w : SpaceTime) : ℝ :=
  (PolarCharts.localChart
    (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
      (PhysicalGraphBounds.radialProjection w))
    (PhysicalGraphBounds.radialProjection w)).2

noncomputable def cylinderPoint (w : SpaceTime) : SpaceTime :=
  (w.1, AxisymmetricResidual.pack
    (PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) (angle w) (w.2 2))

/-- This is a current-band map; it does not use the reference band of a label. -/
noncomputable def nativePoint (n : ℕ) (w : SpaceTime) : Native :=
  PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
    (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
    (cylinderPoint w)

noncomputable def cylindricalPotential (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (z : SpaceTime) : ComplexVector :=
  (ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) •
    nativePotential x l j n
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)

noncomputable def cylindricalPressure (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (z : SpaceTime) : ℝ :=
  (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
    (nativePressure x l j n
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)).re

/-- A single actual harmonic, in Cartesian coordinates. -/
noncomputable def localPotentialMode (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (w : SpaceTime) : Space :=
  PhysicalCurlCovariance.realVector
    (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
      (cylindricalPotential x l j n (cylinderPoint w)))

noncomputable def localPressureMode (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (w : SpaceTime) : ℝ :=
  cylindricalPressure x l j n (cylinderPoint w)

/-- The actual finite active-label and nonzero-harmonic sum at band `n`. -/
noncomputable def localPotential (x : CycleState (Label B N0)) (n : ℕ) : VelocityField :=
  fun w => ∑ l ∈ x.coefficients.labels n,
    ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      localPotentialMode x l j n w

noncomputable def localPressure (x : CycleState (Label B N0)) (n : ℕ) : PressureField :=
  fun w => ∑ l ∈ x.coefficients.labels n,
    ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      localPressureMode x l j n w

theorem nativePotential_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) :
    nativePotential x l j n = CurlClassBounds.vectorPotential
      ((copyData x l j).background.frequency n) ((copyData x l j).background.radius n)
      ((ActualParticularStageControls.directions (B := B)).radialField n)
      (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
      ((ActualParticularStageControls.directions (B := B)).axialField
        (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
      ((copyData x l j).background.phase n) ((copyData x l j).common.amplitude n) := rfl

theorem localPotentialMode_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (w : SpaceTime) :
    localPotentialMode x l j n w =
      (ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) •
        PhysicalCurlCovariance.realVector
          (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
            (nativePotential x l j n (nativePoint n w))) := by
  ext i
  fin_cases i <;> simp [localPotentialMode, cylindricalPotential, nativePoint,
    PhysicalCurlCovariance.realVector, Complex.real_smul]

/-! ## The polar angle is only a coordinate choice -/

theorem chosenChart_valid {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    PhysicalGraphBounds.radialProjection w ∈ PolarCharts.chartDomain
      ‖PhysicalGraphBounds.radialProjection w‖
      (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
        (PhysicalGraphBounds.radialProjection w)) := by
  apply PhysicalWaveSum.chooseChart_valid (b := ‖PhysicalGraphBounds.radialProjection w‖)
    (norm_pos_iff.mpr hw)
  refine ⟨by simp, ?_⟩
  change ‖PhysicalGraphBounds.radialProjection w‖ ≤ ‖PhysicalGraphBounds.radialProjection w‖
  exact le_rfl

theorem polar_angle {w : SpaceTime} (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    PolarCharts.polar (PolarCharts.radius (PhysicalGraphBounds.radialProjection w), angle w) =
      PhysicalGraphBounds.radialProjection w := by
  have hc := chosenChart_valid hw
  have hp : 0 < (PolarCharts.rotate
      (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
        (PhysicalGraphBounds.radialProjection w)) (PhysicalGraphBounds.radialProjection w)).1 :=
    lt_trans (by positivity : 0 < ‖PhysicalGraphBounds.radialProjection w‖ / 4) hc
  simpa only [PolarCharts.localChart_apply, angle] using PolarCharts.polar_localChart _ hp

theorem angle_chart_cos_sin {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    Real.cos (angle w) = Real.cos (PhysicalCurlCovariance.polarInput a i w).2 ∧
      Real.sin (angle w) = Real.sin (PhysicalCurlCovariance.polarInput a i w).2 := by
  have hr := ActualSignedPhysicalData.chart_radius_pos ha i hw
  have hn : PhysicalGraphBounds.radialProjection w ≠ 0 := by
    intro hz
    simp only [hz, PolarCharts.radius, Prod.fst_zero, Prod.snd_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_zero] at hr
    exact (lt_irrefl 0) hr
  have he := (polar_angle hn).trans (PolarCharts.polar_chart ha i hw).symm
  rw [show PolarCharts.chart a i (PhysicalGraphBounds.radialProjection w) =
      (PolarCharts.radius (PhysicalGraphBounds.radialProjection w),
        (PhysicalCurlCovariance.polarInput a i w).2) by
      apply Prod.ext
      · exact ActualSignedPhysicalData.chart_radius ha i hw
      · rfl] at he
  have h0 := congrArg Prod.fst he
  have h1 := congrArg Prod.snd he
  exact ⟨mul_left_cancel₀ hr.ne' h0, mul_left_cancel₀ hr.ne' h1⟩

theorem periodic_eq_of_cos_sin {E : Type*} {f : ℝ → E}
    (hf : Function.Periodic f (2 * Real.pi)) {a b : ℝ}
    (hc : Real.cos a = Real.cos b) (hs : Real.sin a = Real.sin b) : f a = f b := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
  have he : a = b + (k : ℝ) * (2 * Real.pi) := by nlinarith [hk]
  rw [he]
  exact hf.int_mul k b

theorem periodic_cylinderPoint_eq_chart {E : Type*} {f : SpaceTime → E}
    (hf : ∀ t r z : ℝ, Function.Periodic
      (fun θ => f (t, AxisymmetricResidual.pack r θ z)) (2 * Real.pi))
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    f (cylinderPoint w) = f (PhysicalCurlCovariance.polarCoordinates a i w) := by
  obtain ⟨hc,hs⟩ := angle_chart_cos_sin ha i hw
  have he := periodic_eq_of_cos_sin
    (hf w.1 (PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) (w.2 2)) hc hs
  change f (cylinderPoint w) =
    f (w.1, AxisymmetricResidual.pack
      (PolarCharts.chart a i (PhysicalGraphBounds.radialProjection w)).1
      (PhysicalCurlCovariance.polarInput a i w).2 (w.2 2))
  rw [ActualSignedPhysicalData.chart_radius ha i hw]
  exact he

theorem rotation_realVector_eq_frame {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (v : ComplexVector) :
    PhysicalCurlCovariance.realVector
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w) v) =
    CylindricalResidual.frame (PhysicalCurlCovariance.polarInput a i w).2
      (PhysicalCurlCovariance.realVector v) := by
  ext k
  rw [PhysicalCurlCovariance.realVector_apply, ActualSignedPhysicalData.cartesian_rotation]
  exact ActualSignedPhysicalData.rotateCoefficient_chart_re ha i hw v k

/-! ## The actual current coefficients have integer angular frequency -/

theorem nativePotential_fullTurn (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ) (z : Native) :
    nativePotential x l j n (z + (2 * Real.pi) •
      (ActualParticularStageControls.directions (B := B)).angular) = nativePotential x l j n z := by
  rw [nativePotential_eq, copyData_eq_actual x l j hf]
  have hA := ActualParticularDynamics.native_angular x l j n (0,0)
  have ha := (ActualParticularDynamics.data x l j).common_amplitude_invariant
    (ActualParticularStageControls.directions (B := B)).angular
    (fun m k => (ActualParticularDynamics.native_angular x l j m k).cutoff)
    (fun m k => (ActualParticularDynamics.native_angular x l j m k).amplitude) n
  have hK : (x.coefficients.blocks l).frequency n ≠ 0 := by
    rw [hf n]
    exact (Scaling.carrier_frequency_pos
      (ChartScales.epsilon_pos CorrectionInitialization.ActualPrimary.h n)).ne'
  apply PhysicalCurlCovariance.vectorPotential_fullTurn
    (j * (x.coefficients.blocks l).angularFrequency n) hA.radius hA.radial_field
    (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _)
    (ParticularWaveAssembly.actualCarrier_affine
      (ActualParticularStageControls.parameters x l).background
      (ActualParticularStageControls.assembly x l).carrierBlock j n) ha
  change ((j : ℝ) * (x.coefficients.blocks l).frequency n) *
    ((x.coefficients.blocks l).angularFrequency n / (x.coefficients.blocks l).frequency n) = _
  push_cast
  field_simp

theorem nativePressure_fullTurn (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ) (z : Native) :
    nativePressure x l j n (z + (2 * Real.pi) •
      (ActualParticularStageControls.directions (B := B)).angular) = nativePressure x l j n z := by
  unfold nativePressure
  rw [copyData_eq_actual x l j hf]
  have hp := ActualParticularDynamics.common_pressure_invariant x l j n
  have hΦ := ParticularWaveAssembly.actualCarrier_affine
    (ActualParticularStageControls.parameters x l).background
    (ActualParticularStageControls.assembly x l).carrierBlock j n
  have hK : (x.coefficients.blocks l).frequency n ≠ 0 := by
    rw [hf n]
    exact (Scaling.carrier_frequency_pos
      (ChartScales.epsilon_pos CorrectionInitialization.ActualPrimary.h n)).ne'
  change mode ((j : ℝ) * (x.coefficients.blocks l).frequency n) _ _ _ = _
  have hp' : CopyAngularInvariance.Invariant
      (ActualParticularStageControls.directions (B := B)).angular
      ((ActualParticularCoherence.copyData x l j).common.pressure n) := hp
  have hΦ' : CopyAngularInvariance.AffinePhase
      (ActualParticularStageControls.directions (B := B)).angular
      (((x.coefficients.blocks l).angularFrequency n : ℝ) / (x.coefficients.blocks l).frequency n)
      ((ActualParticularCoherence.copyData x l j).background.phase n) := hΦ
  rw [CopyAngularInvariance.mode_translate hp' hΦ']
  have he : HarmonicCalculus.phaseFactor ((j : ℝ) * (x.coefficients.blocks l).frequency n) *
      ((((x.coefficients.blocks l).angularFrequency n : ℝ) /
        (x.coefficients.blocks l).frequency n * (2 * Real.pi) : ℝ) : ℂ) =
      ((j * (x.coefficients.blocks l).angularFrequency n : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I) := by
    unfold HarmonicCalculus.phaseFactor
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hK]
  rw [he, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rfl

theorem cylindricalPotential_periodic (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n)
    (n : ℕ) (t r z : ℝ) : Function.Periodic
      (fun θ => cylindricalPotential x l j n (t, AxisymmetricResidual.pack r θ z))
      (2 * Real.pi) := by
  intro θ
  dsimp only
  unfold cylindricalPotential
  rw [← PhysicalParticularWave.angle_translate_pack, PhysicalParticularWave.nativeMap_add_angle]
  exact congrArg (fun v : ComplexVector =>
    (ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) • v)
    (nativePotential_fullTurn x l j hf n _)

theorem cylindricalPressure_periodic (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n)
    (n : ℕ) (t r z : ℝ) : Function.Periodic
      (fun θ => cylindricalPressure x l j n (t, AxisymmetricResidual.pack r θ z))
      (2 * Real.pi) := by
  intro θ
  dsimp only
  unfold cylindricalPressure
  rw [← PhysicalParticularWave.angle_translate_pack, PhysicalParticularWave.nativeMap_add_angle]
  exact congrArg (fun v : ℂ =>
    (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) * v.re)
    (nativePressure_fullTurn x l j hf n _)

theorem localPotentialMode_eq_chart (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPotentialMode x l j n w =
      PhysicalCurlCovariance.cartesianPotential a i (cylindricalPotential x l j n) w := by
  unfold localPotentialMode
  rw [periodic_cylinderPoint_eq_chart (cylindricalPotential_periodic x l j hf n) ha i hw,
    rotation_realVector_eq_frame ha i hw]
  rfl

theorem localPressureMode_eq_chart (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPressureMode x l j n w = cylindricalPressure x l j n
      (PhysicalCurlCovariance.polarCoordinates a i w) :=
  periodic_cylinderPoint_eq_chart (cylindricalPressure_periodic x l j hf n) ha i hw

theorem localPotentialMode_germ_chart (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPotentialMode x l j n =ᶠ[𝓝 w]
      PhysicalCurlCovariance.cartesianPotential a i (cylindricalPotential x l j n) := by
  filter_upwards [(ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hw] with y hy
  exact localPotentialMode_eq_chart x l j hf n ha i hy

theorem localPressureMode_germ_chart (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPressureMode x l j n =ᶠ[𝓝 w] fun v =>
      cylindricalPressure x l j n (PhysicalCurlCovariance.polarCoordinates a i v) := by
  filter_upwards [(ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hw] with y hy
  exact localPressureMode_eq_chart x l j hf n ha i hy

/-! ## Native smoothness and its exact physical transport -/

noncomputable def nativeDomain : Set Native :=
  ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
    CorrectionInitialization.ActualPrimary.standardRegion

theorem nativeDomain_open : IsOpen nativeDomain :=
  ActualWaveRegularity.nativeDomain_open ActualWaveRegularity.particularChart
    CorrectionInitialization.ActualPrimary.standardRegion

/-- The endpoint condition concerns actual Volterra output values.  The
source-continuity and path lemmas provide it for the constructed cycle. -/
def RawBoundaryZero (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) : Prop :=
  ∀ n z, z ∈ nativeDomain →
    ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal) →
    (copyData x l j).common.amplitude n z = 0 ∧ (copyData x l j).common.pressure n z = 0

theorem nativePotential_contDiffOn (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hphase : (copyData x l j).background.phase =
      (ActualParticularStageControls.background l).phase) {α : ℝ}
    (ha : WeightedClasses.MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) α
      (copyData x l j).common.amplitude)
    (hz : RawBoundaryZero x l j) (n : ℕ) :
    ContDiffOn ℝ ∞ (nativePotential x l j n) nativeDomain := by
  have hzero := fun m z hm hr => (hz m z hm hr).1
  have hnormal := ActualWaveRegularityData.particular_normal_smooth l
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j hphase ha hzero n
  have hphi := ActualWaveRegularityData.particular_phase_smooth l
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j hphase n
  apply ActualWaveRegularityData.particular_smooth_of_positive_or_zero
  · apply contDiffOn_pi.mpr
    intro i
    exact HarmonicCalculus.contDiffOn_mode _ hphi
      (contDiffOn_pi.mp ((hnormal.mono (fun _ hx => hx.1)).const_smul
        (CurlClassBounds.inverseCarrier ((copyData x l j).background.frequency n))) i)
  · intro z hm hr
    have ho : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∉
        Icc (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal) := by
      intro hi
      exact (not_lt_of_ge (ActualWaveRegularityData.radius_nonpos hm hr))
        ((PrimaryTargetBounds.leftRadius_pos
          CorrectionInitialization.ActualPrimary.nominal).trans_le hi.1)
    filter_upwards [ActualWaveRegularityData.particular_zero_germ _ hzero n hm ho] with y hy
    rw [nativePotential_eq]
    ext i
    simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
      hy, PeriodizedWaveBounds.normalCoefficient_zero, smul_zero, Pi.zero_apply, zero_mul]

theorem nativePressure_re_contDiffOn (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hphase : (copyData x l j).background.phase =
      (ActualParticularStageControls.background l).phase) {β : ℝ}
    (hp : WeightedClasses.MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) β
      (copyData x l j).common.pressure)
    (hz : RawBoundaryZero x l j) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z => (nativePressure x l j n z).re) nativeDomain := by
  have hs := ActualWaveRegularityData.particular_mode_pressure_smooth l
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j hphase hp
    (fun m z hm hr => (hz m z hm hr).2) n
  have he := hs.comp ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn
    (fun _ hx => hx)
  simp only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] at he
  exact he

theorem nativeMap_contDiffAt (n : ℕ) {z : SpaceTime} (hr : 0 < z.2 0) :
    ContDiffAt ℝ ∞ (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)) z := by
  apply PhysicalParticularWave.waveEquiv.contDiff.contDiffAt.comp
  exact (PhysicalResidualBridge.commonGraph (ChartScales.Q n)
    CorrectionInitialization.ActualPrimary.h
    (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)).map_smoothAt
      (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr).ne'

theorem cylindricalPotential_contDiffAt_of_native (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : SpaceTime} (hr : 0 < z.2 0)
    (hP : ContDiffAt ℝ ∞ (nativePotential x l j n)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)) :
    ContDiffAt ℝ ∞ (cylindricalPotential x l j n) z :=
  (hP.comp z (nativeMap_contDiffAt n hr)).const_smul _

theorem cylindricalPressure_contDiffAt_of_native (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : SpaceTime} (hr : 0 < z.2 0)
    (hP : ContDiffAt ℝ ∞ (fun v => (nativePressure x l j n v).re)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)) :
    ContDiffAt ℝ ∞ (cylindricalPressure x l j n) z :=
  contDiffAt_const.mul (hP.comp z (nativeMap_contDiffAt n hr))

theorem localPotentialMode_contDiffAt_of_native (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hP : ContDiffAt ℝ ∞ (nativePotential x l j n)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
        (PhysicalCurlCovariance.polarCoordinates a i w))) :
    ContDiffAt ℝ ∞ (localPotentialMode x l j n) w := by
  have hz := ActualMeanPotentialRealization.polarCoordinates_valid ha i hw
  exact (PhysicalCurlCovariance.cartesianPotential_smoothAt ha i
    (cylindricalPotential_contDiffAt_of_native x l j n hz.1 hP)).congr_of_eventuallyEq
      (localPotentialMode_germ_chart x l j hf n ha i hw)

theorem localPressureMode_contDiffAt_of_native (x : CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hP : ContDiffAt ℝ ∞ (fun v => (nativePressure x l j n v).re)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
        (PhysicalCurlCovariance.polarCoordinates a i w))) :
    ContDiffAt ℝ ∞ (localPressureMode x l j n) w := by
  have hz := ActualMeanPotentialRealization.polarCoordinates_valid ha i hw
  exact ((cylindricalPressure_contDiffAt_of_native x l j n hz.1 hP).comp w
    (PhysicalCurlCovariance.polarCoordinates_smooth ha i).contDiffAt).congr_of_eventuallyEq
      (localPressureMode_germ_chart x l j hf n ha i hw)

theorem copyData_phase {x : CycleState (Label B N0)}
    (hx : ActualParticularStageControls.PreservesCarriers x) (l : Label B N0) (j : ℤ) :
    (copyData x l j).background.phase = (ActualParticularStageControls.background l).phase := by
  rw [copyData_eq_actual x l j (ActualParticularStageControls.preserves_frequency hx l)]
  exact ActualParticularDynamics.data_phase hx l j

/-- The native smoothness hypotheses are consequences of the actual
source class and support theorem; no physical jet estimate is assumed. -/
theorem native_smooth_of_current_source (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope α (ActualParticularStageControls.currentSource x
        j))
    (l : Label B N0) (hz : RawBoundaryZero x l j) (n : ℕ) :
    ContDiffOn ℝ ∞ (nativePotential x l j n) nativeDomain ∧
      ContDiffOn ℝ ∞ (fun z => (nativePressure x l j n z).re) nativeDomain := by
  have hc := ActualParticularStageControls.common_bounds x hx hs hN j hj H
  have ha := (ActualParticularStageControls.native_wave_to_weighted hc.1).each l
  have hp := (ActualParticularStageControls.native_wave_to_weighted hc.2.2.1).each l
  have he := copyData_eq_actual x l j (ActualParticularStageControls.preserves_frequency hx l)
  have ha' : WeightedClasses.MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) α
      (copyData x l j).common.amplitude := by
    rw [he]
    exact ha
  have hp' : WeightedClasses.MemClass ActualWaveRegularityData.particularFullStrip
      (fun _ z => Real.sqrt (ActualWaveRegularityData.particularFullStrip.zeta z)) (α + 1/2)
      (copyData x l j).common.pressure := by
    rw [he]
    exact hp
  exact ⟨nativePotential_contDiffOn x l j (copyData_phase hx l j) ha' hz n,
    nativePressure_re_contDiffOn x l j (copyData_phase hx l j) hp' hz n⟩

theorem nativeMap_polar_mem_iff (n : ℕ) (a : ℝ) (i : PolarCharts.Index) (w : SpaceTime) :
    PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates a i w) ∈ nativeDomain ↔
    nativePoint n w ∈ nativeDomain := by
  change ((PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h (ChartScales.Q
    n)
      (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates a i w)).1.1.2 ∈
      CorrectionInitialization.ActualPrimary.standardRegion.carrier ∧ True) ↔
    ((nativePoint n w).1.1.2 ∈ CorrectionInitialization.ActualPrimary.standardRegion.carrier ∧ True)
  simp only [PhysicalParticularWave.nativeMap, PhysicalParticularWave.waveEquiv_apply,
    PhysicalResidualBridge.ScaledGraph.map, PhysicalCurlCovariance.polarCoordinates,
    AxisymmetricResidual.pack_two, nativePoint, cylinderPoint]

theorem localModes_contDiffAt_of_current_source (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope α (ActualParticularStageControls.currentSource x
        j))
    (l : Label B N0) (hz : RawBoundaryZero x l j) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    ContDiffAt ℝ ∞ (localPotentialMode x l j n) w ∧
      ContDiffAt ℝ ∞ (localPressureMode x l j n) w := by
  have hh := native_smooth_of_current_source x hx hs hN j hj H l hz n
  have hm' := (nativeMap_polar_mem_iff n a i w).mpr hm
  exact ⟨localPotentialMode_contDiffAt_of_native x l j
      (ActualParticularStageControls.preserves_frequency hx l) n ha i hw
      (hh.1.contDiffAt (nativeDomain_open.mem_nhds hm')),
    localPressureMode_contDiffAt_of_native x l j
      (ActualParticularStageControls.preserves_frequency hx l) n ha i hw
      (hh.2.contDiffAt (nativeDomain_open.mem_nhds hm'))⟩

/-! The literal cycle input discharges the raw endpoint condition. -/

theorem copyData_particularState (x : CycleState (ActualInitialization.Index B N0))
    (l : ActualInitialization.Index B N0) (j : ℤ) :
    copyData (ActualCycleParameters.particularState x) (l.2,l.1) j =
      ActualParticularCycleData.nativeData x l j := rfl

theorem rawBoundaryZero_of_invariant {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (l : ActualInitialization.Index B N0) (j : ℤ) :
    RawBoundaryZero (ActualCycleParameters.particularState x) (l.2,l.1) j := by
  intro n z hz hr
  rw [copyData_particularState]
  exact ActualParticularCycleData.native_common_boundary H l j n hz hr

theorem native_smooth_of_invariant {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : ActualInitialization.Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (nativePotential (ActualCycleParameters.particularState x) (l.2,l.1) j n)
      nativeDomain ∧
    ContDiffOn ℝ ∞ (fun z => (nativePressure (ActualCycleParameters.particularState x)
      (l.2,l.1) j n z).re) nativeDomain := by
  have hp : (copyData (ActualCycleParameters.particularState x) (l.2,l.1) j).background.phase =
      (ActualParticularStageControls.background (l.2,l.1)).phase :=
    ActualParticularCycleData.native_phase H l j
  exact ⟨nativePotential_contDiffOn _ _ j hp
      (ActualParticularCycleData.native_raw_class H hN l j hj)
      (rawBoundaryZero_of_invariant H l j) n,
    nativePressure_re_contDiffOn _ _ j hp
      (ActualParticularCycleData.native_pressure_class H hN l j hj)
      (rawBoundaryZero_of_invariant H l j) n⟩

theorem localModes_contDiffAt_of_invariant
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : ActualInitialization.Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    ContDiffAt ℝ ∞ (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w ∧
    ContDiffAt ℝ ∞ (localPressureMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w :=
      by
  have hh := native_smooth_of_invariant H hN l j hj n
  have hm' := (nativeMap_polar_mem_iff n a i w).mpr hm
  have hf := ActualParticularDynamics.carrier_frequency
    (ActualParticularCycleData.preservesCarriers H)
    (l.2,l.1)
  exact ⟨localPotentialMode_contDiffAt_of_native _ _ j hf n ha i hw
      (hh.1.contDiffAt (nativeDomain_open.mem_nhds hm')),
    localPressureMode_contDiffAt_of_native _ _ j hf n ha i hw
      (hh.2.contDiffAt (nativeDomain_open.mem_nhds hm'))⟩

theorem localFields_contDiffAt_of_invariant
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    ContDiffAt ℝ ∞ (localPotential (ActualCycleParameters.particularState x) n) w ∧
    ContDiffAt ℝ ∞ (localPressure (ActualCycleParameters.particularState x) n) w := by
  constructor <;> apply ContDiffAt.sum <;> intro l hl <;>
    apply ContDiffAt.sum <;> intro j hj
  · exact (localModes_contDiffAt_of_invariant H hN (l.2,l.1) j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hw hm).1
  · exact (localModes_contDiffAt_of_invariant H hN (l.2,l.1) j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hw hm).2

/-! ## The complete corrected coefficient is the actual native curl -/

noncomputable def nativeVelocity (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) : Native → ComplexVector :=
  vectorMode ((copyData x l j).background.frequency n) ((copyData x l j).background.phase n)
    (((copyData x l j).commonCorrected
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
      (ActualParticularStageControls.directions (B := B))).amplitude n)

theorem nativeStrip_mem {z : Native} (hz : z ∈ nativeDomain)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∈
      Ioo (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)) :
    z ∈ (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip).domain :=
      by
  change ActualWaveRegularity.particularChart.symm z ∈ ActualSignedStageControls.fullStrip.domain
  rw [ActualWaveRegularityData.strip_domain_eq]
  exact ⟨hz,hr⟩

theorem common_tangent_on_strip (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope α (ActualParticularStageControls.currentSource x
        j))
    (l : Label B N0) (n : ℕ) {z : Native}
    (hz : z ∈ (ParticularParameters.nativeStrip
      ActualParticularStageControls.associatedStrip).domain) :
    normalDot ((copyData x l j).background.normal
        (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
        (ActualParticularStageControls.directions (B := B)) n z)
      ((copyData x l j).common.amplitude n z) = 0 := by
  rw [copyData_eq_actual x l j (ActualParticularStageControls.preserves_frequency hx l)]
  let S := ActualParticularDynamics.supportData x hs hN l j
  change normalDot ((ActualParticularDynamics.data x l j).background.normal
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
      (ActualParticularStageControls.directions (B := B)) n z)
    ((ActualParticularDynamics.data x l j).common.amplitude n z) = 0
  by_cases he : ∃ k, z ∈ S.cells.carrier n k
  · obtain ⟨k,hk⟩ := he
    rw [((ActualParticularDynamics.data x l j).common_amplitude_germ
      S.cells S.cutoff_support n hk).eq_of_nhds]
    rcases S.localized_alternative hz hk with hc | ⟨ha,_⟩
    · have ht := (ActualParticularDynamics.native_tangency_germ hx j hj H l n k hc).eq_of_nhds
      change normalDot _ ((ActualParticularDynamics.data x l j).cutoff n k z •
        (ActualParticularDynamics.data x l j).amplitude n k z) = 0
      have hlin (N : Space) (a : ComplexVector) (c : ℝ) :
          normalDot N (c • a) = (c : ℂ) * normalDot N a := by
        simp only [normalDot, Pi.smul_apply, Complex.real_smul]
        ring
      rw [hlin, ht, mul_zero]
    · rw [ha.eq_of_nhds]
      simp [normalDot]
  · rw [((ActualParticularDynamics.data x l j).common_zero_germs
      S.cells S.cutoff_support (not_exists.mp he)).1.eq_of_nhds]
    simp [normalDot]

theorem native_normal_ne {x : CycleState (Label B N0)}
    (hx : ActualParticularStageControls.PreservesCarriers x) (l : Label B N0) (j : ℤ) (n : ℕ)
    {z : Native} (hz : z ∈ ActualWaveRegularityData.particularPositive) :
    (copyData x l j).background.normal
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
      (ActualParticularStageControls.directions (B := B)) n z ≠ 0 := by
  unfold LinearWaveBounds.WaveCoefficients.normal
  rw [copyData_phase hx l j]
  change (ActualParticularStageControls.background l).normal
    ActualWaveRegularityData.particularFullStrip
    (ActualParticularStageControls.directions (B := B)) n z ≠ 0
  rw [ActualWaveRegularityData.particular_native_normal l n hz]
  exact ActualPrimaryCoherence.piece_normal_ne CorrectionInitialization.ActualPrimary.standardRegion
    l.1 l.2 n hz.2

/-- The actual native curl identity includes the radial faces: zero raw
values there give tangency, while the weighted extension supplies the
actual derivatives of the normal coefficient. -/
theorem nativePotential_curl_of_invariant
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : ActualInitialization.Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    {z : Native} (hz : z ∈ ActualWaveRegularityData.particularPositive) :
    CurlClassBounds.cylindricalCurl
      ((copyData (ActualCycleParameters.particularState x) (l.2,l.1) j).background.radius n)
      ((ActualParticularStageControls.directions (B := B)).radialField n)
      (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
      ((ActualParticularStageControls.directions (B := B)).axialField
        (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
      (nativePotential (ActualCycleParameters.particularState x) (l.2,l.1) j n) z =
    nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n z := by
  let y := ActualCycleParameters.particularState x
  have hx : ActualParticularStageControls.PreservesCarriers y :=
    ActualParticularCycleData.preservesCarriers H
  have hphase := copyData_phase hx (l.2,l.1) j
  have hzero := fun m w hm hr =>
    (rawBoundaryZero_of_invariant H l j m w hm hr).1
  have hnormal := ActualWaveRegularityData.particular_normal_smooth (l.2,l.1)
    (ActualParticularStageControls.assembly y (l.2,l.1)).context
    (ActualParticularStageControls.assembly y (l.2,l.1)).state
    (ActualParticularStageControls.assembly y (l.2,l.1)).carrierBlock
    (ActualParticularStageControls.assembly y (l.2,l.1)).gaussianInput
    (ActualParticularStageControls.assembly y (l.2,l.1)).aliasInput j hphase
    (ActualParticularCycleData.native_raw_class H hN l j hj) hzero n
  have hphi := ActualWaveRegularityData.particular_phase_smooth (l.2,l.1)
    (ActualParticularStageControls.assembly y (l.2,l.1)).context
    (ActualParticularStageControls.assembly y (l.2,l.1)).state
    (ActualParticularStageControls.assembly y (l.2,l.1)).carrierBlock
    (ActualParticularStageControls.assembly y (l.2,l.1)).gaussianInput
    (ActualParticularStageControls.assembly y (l.2,l.1)).aliasInput j hphase n
  have ht : normalDot ((copyData y (l.2,l.1) j).background.normal
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
      (ActualParticularStageControls.directions (B := B)) n z)
      ((copyData y (l.2,l.1) j).common.amplitude n z) = 0 := by
    by_cases hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∈
        Ioo (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)
    · exact common_tangent_on_strip y hx (ActualParticularCycleData.native_inputSupport H) hN
        j hj (ActualParticularCycleData.native_source_class H j hj) (l.2,l.1) n
        (nativeStrip_mem hz.1 hr)
    · rw [hzero n z hz.1 hr]
      simp [normalDot]
  have hfreq : (copyData y (l.2,l.1) j).background.frequency n ≠ 0 := by
    rw [copyData_eq_actual y (l.2,l.1) j (ActualParticularStageControls.preserves_frequency hx _)]
    exact ActualParticularDynamics.frequency_ne hx (l.2,l.1) j hj n
  exact ClosedNativeWaveIdentities.cylindricalCurl_vectorPotential_of_differentiable _ _ _ _ hfreq
    ((hphi.contDiffAt (ActualWaveRegularityData.particularPositive_open.mem_nhds
      hz)).differentiableAt
      (by simp))
    (fun i => (contDiffAt_pi.mp (hnormal.contDiffAt (nativeDomain_open.mem_nhds hz.1))
      i).differentiableAt
      (by simp))
    (native_normal_ne hx (l.2,l.1) j n hz) ht

/-! ## Curl in genuine Cartesian coordinates -/

theorem nativeCurl_reindex (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (z : PhysicalResidualBridge.Cylinder) :
    CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) CorrectionInitialization.ActualPrimary.h
        (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) CorrectionInitialization.ActualPrimary.h
        (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)).axial
      (fun y => nativePotential x l j n (PhysicalParticularWave.waveEquiv y)) z =
    CurlClassBounds.cylindricalCurl ((copyData x l j).background.radius n)
      ((ActualParticularStageControls.directions (B := B)).radialField n)
      (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
      ((ActualParticularStageControls.directions (B := B)).axialField
        (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
      (nativePotential x l j n) (PhysicalParticularWave.waveEquiv z) := by
  have he := ActualParticularRealization.curl_pull PhysicalParticularWave.waveEquiv
    ((ActualParticularStageControls.assembly x l).background.radius n)
    ((ActualParticularStageControls.assembly x l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.assembly x l).directions.angular)
    ((ActualParticularStageControls.assembly x l).directions.axialField
      (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
    (nativePotential x l j n)
  rw [(ActualParticularCoherence.targetChart x l n).radius,
    (ActualParticularCoherence.targetChart x l n).radial,
    (ActualParticularCoherence.targetChart x l n).angular,
    (ActualParticularCoherence.targetChart x l n).axial] at he
  exact congrFun he z

theorem localPotentialMode_forward_germ (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i) :
    (fun w : SpaceTime => localPotentialMode x l j n (w.1, CylindricalResidual.chart w.2)) =ᶠ[𝓝 z]
      (fun w => CylindricalResidual.frame (w.2 1)
        (PhysicalCurlCovariance.realVector (cylindricalPotential x l j n w))) := by
  have hw : (z.1, CylindricalResidual.chart z.2) ∈
      ActualMeanPotentialRealization.cartesianDomain a i := by
    simpa [ActualMeanPotentialRealization.cartesianDomain,
      PhysicalGraphBounds.radialProjection_apply,
      CylindricalResidual.chart, PolarCharts.polar] using hz.2.2
  have hfwd : ContDiff ℝ ∞ (fun w : SpaceTime => (w.1, CylindricalResidual.chart w.2)) :=
    contDiff_fst.prodMk (CylindricalResidual.contDiff_chart.comp contDiff_snd)
  have hg := (localPotentialMode_germ_chart x l j hf n ha i hw).comp_tendsto
    hfwd.continuous.continuousAt
  exact hg.trans (PhysicalCurlCovariance.cartesianPotential_forward_germ ha i
    (cylindricalPotential x l j n) hz)

theorem localPotentialMode_curl_transport (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n =
      ChartScales.carrier CorrectionInitialization.ActualPrimary.h n) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hP : ContDiffAt ℝ ∞ (nativePotential x l j n)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z))
    (k : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (localPotentialMode x l j n) (z.1, CylindricalResidual.chart z.2)) k
        =
    (ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (CurlClassBounds.cylindricalCurl ((copyData x l j).background.radius n)
        ((ActualParticularStageControls.directions (B := B)).radialField n)
        (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
        ((ActualParticularStageControls.directions (B := B)).axialField
          (ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n)
        (nativePotential x l j n)
        (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
          (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)
            k).re := by
  let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n)
    CorrectionInitialization.ActualPrimary.h
    (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
  have hl : 0 < G.radialScale := Real.rpow_pos_of_pos (ChartScales.Q_pos n) _
  have hw : (z.1, CylindricalResidual.chart z.2) ∈
      ActualMeanPotentialRealization.cartesianDomain a i := by
    simpa [ActualMeanPotentialRealization.cartesianDomain,
      PhysicalGraphBounds.radialProjection_apply,
      CylindricalResidual.chart, PolarCharts.polar] using hz.2.2
  have hP' : ContDiffAt ℝ ∞ (nativePotential x l j n)
      (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n)
        (PhysicalCurlCovariance.polarCoordinates a i (z.1, CylindricalResidual.chart z.2))) := by
    rw [PhysicalCurlCovariance.polarCoordinates_forward ha i hz]
    exact hP
  have hA := localPotentialMode_contDiffAt_of_native x l j hf n ha i hw hP'
  have hB : ∀ k, DifferentiableAt ℝ
      (fun y => nativePotential x l j n (PhysicalParticularWave.waveEquiv y) k) (G.map z) := by
    intro k
    exact (contDiffAt_pi.mp (hP.comp (G.map z)
      PhysicalParticularWave.waveEquiv.contDiff.contDiffAt) k).differentiableAt (by simp)
  have hr := localPotentialMode_forward_germ x l j hf n ha i hz
  have hc := PhysicalCurlCovariance.ScaledGraph.physical_curl G hl hz.1 hB
    ((ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h))
    (hA.differentiableAt (by simp)) hr k
  rw [nativeCurl_reindex x l j n] at hc
  have hscale : (ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) * G.radialScale =
      (ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) := by
    change (ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) *
      (ChartScales.Q n) ^ (-(1/2 : ℝ)) = _
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  simp only [hscale] at hc
  exact hc

theorem nativeMap_mem_positive (n : ℕ) {z : SpaceTime} (hr : 0 < z.2 0)
    (hz : PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z ∈
        nativeDomain) :
    PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z ∈
        ActualWaveRegularityData.particularPositive := by
  refine ⟨hz, ?_, ?_⟩
  · change 0 < (ChartScales.Q n) ^ (-(1/2 : ℝ)) * z.2 0
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr
  · exact CorrectionInitialization.ActualPrimary.standardRegion.time_pos _ hz.1

theorem localPotentialMode_curl_of_invariant
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : ActualInitialization.Index B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hm : PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z ∈
        nativeDomain)
    (k : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl
        (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n)
        (z.1, CylindricalResidual.chart z.2)) k =
    (ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n
        (PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
          (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z)
            k).re := by
  have hh := localPotentialMode_curl_transport (ActualCycleParameters.particularState x) (l.2,l.1) j
    (ActualParticularDynamics.carrier_frequency (ActualParticularCycleData.preservesCarriers H)
      (l.2,l.1))
    n ha i hz ((native_smooth_of_invariant H hN l j hj n).1.contDiffAt
      (nativeDomain_open.mem_nhds hm)) k
  rw [nativePotential_curl_of_invariant H hN l j hj n (nativeMap_mem_positive n hz.1 hm)] at hh
  exact hh

end NavierStokes.ActualCurrentParticularPhysical
