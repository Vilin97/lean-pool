/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalSignedWave
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds

@[expose] public section

/-!
# Actual native-copy realization of the signed reference wave

The primary pulse and signed quotient are fixed.  A periodic reference
coordinate and mask are constructed from the native layout.  The native
copies are summed before curl, and equality with the same reference output
is proved from the periodic-clock identity on their compact supports.
-/

noncomputable section

namespace NavierStokes.ActualPeriodizedSignedRealization

open Set Function Filter
open HarmonicCalculus LinearWaveBounds WeightedClasses
open ProblemStatement
open scoped Topology ContDiff BigOperators InnerProductSpace

abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev Plane := TorusInverse.Plane
abbrev Frequency := TorusInverse.Frequency
abbrev Space := ProblemStatement.Space
abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2

/-- Primitive native geometry and its actual compact mask.  No summed
coefficient or solved-wave identity is a field of this record. -/
structure Layout where
  geometry : ℕ → CommonCoverSolve.Geometry
  window : ℕ → PeriodicPhaseAssembly.ClockWindow
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  cutoff : ℕ → Plane → ℝ
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (cutoff n)
  cutoff_support : ∀ n, support (cutoff n) ⊆ (window n).core
  injective : ∀ n, InjOn TorusAverages.quotientPoint
    ((fun z => (geometry n).center + (geometry n).basis z) '' (window n).outer)

namespace Layout

variable (l : Layout)

noncomputable def nativeMask (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  l.cutoff n ((l.geometry n).coordinates k Y)

noncomputable def mask (n : ℕ) (Y : Plane) : ℝ := ∑' k, l.nativeMask n k Y

noncomputable def clock (n : ℕ) (Y : Plane) : ℝ :=
  PeriodicPhaseAssembly.periodicClock (l.geometry n) (l.window n).cutoff Y / l.length n

noncomputable def nativeClock (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  ((l.geometry n).coordinates k Y).2 / l.length n

noncomputable def gaussian (n : ℕ) (Y : Plane) : ℝ := GaussianTailFlat.profile (l.clock n Y)

noncomputable def nativeGaussian (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  GaussianTailFlat.profile (l.nativeClock n k Y)

theorem cutoff_compact (n : ℕ) : HasCompactSupport (l.cutoff n) :=
  HasCompactSupport.of_support_subset_isCompact (l.window n).core_compact (l.cutoff_support n)

theorem mask_summable (n : ℕ) (Y : Plane) : Summable (fun k => l.nativeMask n k Y) := by
  obtain ⟨J, hJ⟩ := (l.geometry n).finite_copy_cutoffs (l.cutoff_compact n) ‖Y‖
  exact summable_of_ne_finset_zero (s := J) (hJ Y le_rfl)

theorem clock_eq_native (n : ℕ) (k : Frequency) (Y : Plane) (hk : l.nativeMask n k Y ≠ 0) :
    l.clock n Y = l.nativeClock n k Y := by
  have h := PeriodicPhaseAssembly.periodicClock_germ (P := Unit)
    (l.geometry n) (l.window n) (l.injective n) k (z := ((), Y)) (l.cutoff_support n hk)
  exact congrArg (fun t => t / l.length n) h.self_of_nhds

theorem gaussian_eq_native (n : ℕ) (k : Frequency) (Y : Plane) (hk : l.nativeMask n k Y ≠ 0) :
    l.gaussian n Y = l.nativeGaussian n k Y :=
  congrArg GaussianTailFlat.profile (l.clock_eq_native n k Y hk)

theorem mask_smooth (n : ℕ) : ContDiff ℝ ∞ (l.mask n) :=
  PeriodicPhaseAssembly.periodizeScalar_contDiff (l.geometry n) (l.cutoff_smooth n)
    (l.cutoff_compact n)

theorem clock_smooth (n : ℕ) : ContDiff ℝ ∞ (l.clock n) :=
  (PeriodicPhaseAssembly.periodicClock_contDiff (l.geometry n) (l.window n)).div_const _

theorem mask_periodic (n : ℕ) (Y : Plane) (k : Frequency) :
    l.mask n (Y + TorusAverages.latticePoint k) = l.mask n Y :=
  PeriodicPhaseAssembly.periodizeScalar_periodic (l.geometry n) (l.cutoff n) Y k

theorem gaussian_periodic (n : ℕ) (Y : Plane) (k : Frequency) :
    l.gaussian n (Y + TorusAverages.latticePoint k) = l.gaussian n Y := by
  unfold gaussian clock
  rw [PeriodicPhaseAssembly.periodicClock_periodic]

/-- Actual finite native support justifies the scalar/vector infinite sum.
The Gaussian is inserted once, on each native copy. -/
theorem gaussian_mask_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (Y : Plane) (a : E) :
    (∑' k, l.nativeGaussian n k Y • (l.nativeMask n k Y • a)) =
      l.gaussian n Y • (l.mask n Y • a) := by
  calc
    _ = ∑' k, l.nativeMask n k Y • (l.gaussian n Y • a) := by
      apply tsum_congr
      intro k
      by_cases hk : l.nativeMask n k Y = 0
      · simp only [hk, zero_smul, smul_zero]
      · rw [l.gaussian_eq_native n k Y hk]
        exact smul_comm _ _ _
    _ = l.mask n Y • (l.gaussian n Y • a) := (l.mask_summable n Y).tsum_smul_const _
    _ = _ := smul_comm _ _ _

/-- Local finiteness of the actual native cutoffs permits arbitrary
smooth slow factors; only their germs on the native support are needed. -/
theorem maskedSum_contDiffOn {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (projection : D → Plane) (hprojection : ContDiff ℝ ∞ projection)
    {O : Set D} (hO : IsOpen O) (f : Frequency → D → E)
    (hf : ∀ k x, x ∈ O → (l.geometry n).coordinates k (projection x) ∈ tsupport (l.cutoff n) →
      ContDiffAt ℝ ∞ (f k) x) :
    ContDiffOn ℝ ∞ (fun x => ∑' k, l.nativeMask n k (projection x) • f k x) O := by
  classical
  have hc (k : Frequency) : ContDiff ℝ ∞ (fun x => (l.geometry n).coordinates k (projection x)) :=
    ((l.geometry n).coordinates_contDiff k).comp hprojection
  have ht (k : Frequency) (x : D) (hx : x ∈ O) :
      ContDiffAt ℝ ∞ (fun y => l.nativeMask n k (projection y) • f k y) x := by
    by_cases hs : (l.geometry n).coordinates k (projection x) ∈ tsupport (l.cutoff n)
    · exact (((l.cutoff_smooth n).comp (hc k)).contDiffAt).smul (hf k x hx hs)
    · have hz := (notMem_tsupport_iff_eventuallyEq.mp hs).comp_tendsto (hc
      k).continuous.continuousAt
      apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      change l.cutoff n ((l.geometry n).coordinates k (projection y)) = 0 at hy
      simp only [nativeMask, hy, zero_smul]
  apply hO.contDiffOn_iff.mpr
  intro x hx
  obtain ⟨J, hJ⟩ := (l.geometry n).finite_copy_cutoffs (l.cutoff_compact n) (‖projection x‖ + 1)
  have he : (fun y => ∑' k, l.nativeMask n k (projection y) • f k y) =ᶠ[𝓝 x]
      fun y => ∑ k ∈ J, l.nativeMask n k (projection y) • f k y := by
    filter_upwards [(isOpen_lt hprojection.continuous.norm continuous_const).mem_nhds
      (show ‖projection x‖ < ‖projection x‖ + 1 by linarith)] with y hy
    apply tsum_eq_sum
    intro k hk
    change l.cutoff n ((l.geometry n).coordinates k (projection y)) • f k y = 0
    rw [hJ (projection y) hy.le k hk, zero_smul]
  exact (ContDiffAt.sum (fun k _ => ht k x hx)).congr_of_eventuallyEq he

end Layout

/-! ## The primitive homogeneous pressure is linear in its velocity -/

noncomputable def homogeneousPressure (K : ℝ) (N Ndot : Space) (A : Space →L[ℝ] Space)
    (u : Space) : ℂ :=
  Complex.I * (TangentProjection.pressureCoefficient N Ndot u (A u) 0 : ℂ) / (K : ℂ)

theorem homogeneousPressure_smul (K c : ℝ) (N Ndot : Space) (A : Space →L[ℝ] Space) (u : Space) :
    homogeneousPressure K N Ndot A (c • u) = c • homogeneousPressure K N Ndot A u := by
  simp only [homogeneousPressure, TangentProjection.pressureCoefficient, map_smul,
    inner_smul_right, inner_zero_right, add_zero, Complex.real_smul]
  push_cast
  ring

theorem homogeneousPressure_zero (K : ℝ) (N Ndot : Space) (A : Space →L[ℝ] Space) :
    homogeneousPressure K N Ndot A 0 = 0 := by
  simpa only [zero_smul] using homogeneousPressure_smul K 0 N Ndot A (0 : Space)

theorem coefficients_amplitude_at {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (unit Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (j : Fin 2) (n : ℕ) (x : D) :
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).amplitude n x =
      SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x • CurlClassBounds.complexify (unit
        n x) := by
  simp only [SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    SignedWaveUpdate.signedVector, map_smul]

theorem coefficients_pressure_at {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (unit Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (j : Fin 2) (n : ℕ) (x : D) :
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).pressure n x =
      SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x •
        homogeneousPressure (a.frequency n) (a.normal s d n x) (Ndot n x) (A n x) (unit n x) :=
  homogeneousPressure_smul _ _ _ _ _ _

theorem signedScalar_mul_mask {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (s : StripData D) (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2)
    (mask factor : ℕ → D → ℝ) (j : Fin 2) (n : ℕ) (x : D) :
    SignedWaveUpdate.signedScalar (D := D) s H T R (fun n x => mask n x * factor n x) j n x =
      factor n x * SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x := by
  unfold SignedWaveUpdate.signedScalar
  ring

/-! ## Periodic reference constructed from the same primary data -/

section Reference

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  (B : PhysicalSignedWave.PrimaryData U) (l : Layout)

noncomputable def periodizedPrimary : PhysicalSignedWave.PrimaryData U :=
  {B with
    coordinate := fun n x => ((B.coordinate n x).1, l.clock n x.1.2.2)
    mask := fun n x => B.mask n x * l.mask n x.1.2.2}

@[simp] theorem periodizedPrimary_pulse : (periodizedPrimary B l).pulse = B.pulse := rfl
@[simp] theorem periodizedPrimary_target : (periodizedPrimary B l).target = B.target := rfl
@[simp] theorem periodizedPrimary_matrix : (periodizedPrimary B l).matrix = B.matrix := rfl

/-- All view scales, integer covers, backgrounds, and operators are retained. -/
noncomputable def views {reference : ℕ} (V : B.Views reference) :
    (periodizedPrimary B l).Views reference where
  exponent := V.exponent
  referenceScale := V.referenceScale
  referenceScale_pos := V.referenceScale_pos
  referenceCover := V.referenceCover
  scale := V.scale
  scale_pos := V.scale_pos
  cover := V.cover
  cover_le := V.cover_le
  frequency := V.frequency
  frequency_ne := V.frequency_ne
  strip := V.strip
  directions := V.directions
  background := V.background

@[simp] theorem views_map {reference : ℕ} (V : B.Views reference) :
    (views B l V).map = V.map := rfl

/-- Reuse the actual current state, reference state, and their full-fiber
coherence. There is no second signed choice or request. -/
noncomputable def stateData {reference : ℕ} {V : B.Views reference} (D : V.StateData) :
    (views B l V).StateData where
  patch := D.patch
  context := D.context
  referenceContext := D.referenceContext
  current := D.current
  referenceState := D.referenceState
  exponent_pos := D.exponent_pos
  exponent_lt_half := D.exponent_lt_half
  domain := D.domain
  domain_open := D.domain_open
  state_coherent := D.state_coherent
  context_coherent := D.context_coherent
  time_pos := D.time_pos
  fibers := D.fibers
  referenceSlow := D.referenceSlow
  referenceSlow_open := D.referenceSlow_open
  referenceSlow_mem := D.referenceSlow_mem
  reference_theta_smooth := D.reference_theta_smooth
  reference_axial_smooth := D.reference_axial_smooth
  reference_theta_periodic := D.reference_theta_periodic
  reference_axial_periodic := D.reference_axial_periodic

@[simp] theorem stateData_request {reference : ℕ} {V : B.Views reference} (D : V.StateData) :
    (stateData B l D).request = D.request := rfl

@[simp] theorem stateData_referenceRequest {reference : ℕ} {V : B.Views reference} (D :
  V.StateData) :
    (stateData B l D).referenceRequest = D.referenceRequest := rfl

variable {reference : ℕ} (V : B.Views reference)

noncomputable def sharedMask (n : ℕ) (x : Cylinder) : ℝ := B.mask reference (V.map n x)

noncomputable def totalMask (n : ℕ) (x : Cylinder) : ℝ :=
  sharedMask B V n x * l.mask reference (V.map n x).1.2.2

noncomputable def copyMask (k : Frequency) (n : ℕ) (x : Cylinder) : ℝ :=
  sharedMask B V n x * l.nativeMask reference k (V.map n x).1.2.2

noncomputable def commonUnit (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  (periodizedPrimary B l).fundamental j reference (V.map n x)

noncomputable def nativeUnit (j : Fin 2) (k : Frequency) (n : ℕ) (x : Cylinder) : Space :=
  PrimaryPulseBounds.normalizedPulse ((B.pulse j).frame reference)
    ((B.pulse j).lam reference) ((B.pulse j).u reference) ((B.pulse j).L reference)
    ((B.coordinate reference (V.map n x)).1, l.nativeClock reference k (V.map n x).1.2.2)

theorem commonUnit_eq_native (j : Fin 2) (k : Frequency) (n : ℕ) (x : Cylinder)
    (hk : l.nativeMask reference k (V.map n x).1.2.2 ≠ 0) :
    commonUnit B l V j n x = nativeUnit B l V j k n x := by
  change PrimaryPulseBounds.normalizedPulse _ _ _ _ (_, l.clock reference (V.map n x).1.2.2) = _
  rw [l.clock_eq_native reference k (V.map n x).1.2.2 hk]
  rfl

/-- One call to the original homogeneous signed quotient constructor. -/
noncomputable def coefficientsWith (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (mask : ℕ → Cylinder → ℝ) (unit : ℕ → Cylinder → Space) : WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients ((periodizedPrimary B l).viewBase V.background V.frequency (fun n
    => V.map n) reference)
    V.strip V.directions (fun n x => (periodizedPrimary B l).matrix reference (V.map n x))
    ((periodizedPrimary B l).viewTarget V.strip V.velocity (fun n => V.map n) reference) request
      mask unit
    (fun n x => (V.normal n * V.clock n) • B.normalMotion reference (V.map n x))
    (fun n x => V.clock n • B.action reference (V.map n x)) j

noncomputable def commonCoefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) : WaveCoefficients
  Cylinder :=
  coefficientsWith B l V request j (sharedMask B V) (commonUnit B l V j)

noncomputable def nativeCoefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency) :
    WaveCoefficients Cylinder :=
  coefficientsWith B l V request j (copyMask B l V k) (nativeUnit B l V j k)

theorem views_coefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    (views B l V).coefficients request j =
      coefficientsWith B l V request j (totalMask B l V) (commonUnit B l V j) := rfl

noncomputable def commonScalar (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
  ℝ :=
  SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
    (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request (sharedMask B V) j n x

theorem coefficientsWith_amplitude (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (mask : ℕ → Cylinder → ℝ) (unit : ℕ → Cylinder → Space) (n : ℕ) (x : Cylinder) :
    (coefficientsWith B l V request j mask unit).amplitude n x =
      SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
        (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request mask j n x •
          CurlClassBounds.complexify (unit n x) :=
  coefficients_amplitude_at _ _ _ _ _ _ _ _ _ _ _ _ _

theorem coefficientsWith_pressure (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (mask : ℕ → Cylinder → ℝ) (unit : ℕ → Cylinder → Space) (n : ℕ) (x : Cylinder) :
    (coefficientsWith B l V request j mask unit).pressure n x =
      SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
        (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request mask j n x •
          homogeneousPressure (V.frequency n)
            (((periodizedPrimary B l).viewBase V.background V.frequency (fun n => V.map n)
              reference).normal
              V.strip V.directions n x)
            ((V.normal n * V.clock n) • B.normalMotion reference (V.map n x))
            (V.clock n • B.action reference (V.map n x)) (unit n x) :=
  coefficients_pressure_at _ _ _ _ _ _ _ _ _ _ _ _ _

theorem copy_scalar (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency)
    (n : ℕ) (x : Cylinder) :
    SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
      (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request (copyMask B l V k) j n
        x =
      l.nativeMask reference k (V.map n x).1.2.2 *
        SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
          (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request (sharedMask B V) j
            n x := by
  unfold SignedWaveUpdate.signedScalar copyMask
  ring

theorem total_scalar (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
      (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request (totalMask B l V) j n
        x =
      l.mask reference (V.map n x).1.2.2 *
        SignedWaveUpdate.signedScalar V.strip (fun n x => B.matrix reference (V.map n x))
          (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) request (sharedMask B V) j
            n x := by
  unfold SignedWaveUpdate.signedScalar totalMask
  ring

theorem native_amplitude (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency)
    (n : ℕ) (x : Cylinder) :
    (nativeCoefficients B l V request j k).amplitude n x =
      l.nativeMask reference k (V.map n x).1.2.2 • (commonCoefficients B l V request j).amplitude n
        x := by
  simp only [nativeCoefficients, commonCoefficients, coefficientsWith_amplitude]
  rw [copy_scalar, mul_smul]
  by_cases hk : l.nativeMask reference k (V.map n x).1.2.2 = 0
  · simp only [hk, zero_smul]
  · rw [commonUnit_eq_native B l V j k n x hk]

theorem native_pressure (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency)
    (n : ℕ) (x : Cylinder) :
    (nativeCoefficients B l V request j k).pressure n x =
      l.nativeMask reference k (V.map n x).1.2.2 • (commonCoefficients B l V request j).pressure n
        x := by
  simp only [nativeCoefficients, commonCoefficients, coefficientsWith_pressure]
  rw [copy_scalar, mul_smul]
  by_cases hk : l.nativeMask reference k (V.map n x).1.2.2 = 0
  · simp only [hk, zero_smul]
  · rw [commonUnit_eq_native B l V j k n x hk]

theorem view_amplitude (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    ((views B l V).coefficients request j).amplitude n x =
      l.mask reference (V.map n x).1.2.2 • (commonCoefficients B l V request j).amplitude n x := by
  rw [views_coefficients]
  simp only [commonCoefficients, coefficientsWith_amplitude]
  rw [total_scalar, mul_smul]

theorem view_pressure (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    ((views B l V).coefficients request j).pressure n x =
      l.mask reference (V.map n x).1.2.2 • (commonCoefficients B l V request j).pressure n x := by
  rw [views_coefficients]
  simp only [commonCoefficients, coefficientsWith_pressure]
  rw [total_scalar, mul_smul]

/-- Every lattice copy is built by the actual native signed quotient and
projected homogeneous pressure; the cutoff is applied before summation. -/
noncomputable def copyData (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    PeriodizedWaveBounds.CopyData Cylinder Frequency where
  background := (periodizedPrimary B l).viewBase V.background V.frequency (fun n => V.map n)
    reference
  amplitude n k := (nativeCoefficients B l V request j k).amplitude n
  pressure n k := (nativeCoefficients B l V request j k).pressure n
  cutoff n k x := l.nativeGaussian reference k (V.map n x).1.2.2
  source := fun _ _ => 0

theorem copyData_raw (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency) :
    (copyData B l V request j).raw k = nativeCoefficients B l V request j k := rfl

theorem common_amplitude (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    (copyData B l V request j).common.amplitude n x =
      (((views B l V).coefficients request j).withCutoff (views B l V).cutoff).amplitude n x := by
  change (∑' k, l.nativeGaussian reference k (V.map n x).1.2.2 •
    (nativeCoefficients B l V request j k).amplitude n x) =
      l.gaussian reference (V.map n x).1.2.2 • ((views B l V).coefficients request j).amplitude n x
  simp_rw [native_amplitude]
  rw [l.gaussian_mask_sum, view_amplitude]

theorem common_pressure (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    (copyData B l V request j).common.pressure n x =
      (((views B l V).coefficients request j).withCutoff (views B l V).cutoff).pressure n x := by
  change (∑' k, (l.nativeGaussian reference k (V.map n x).1.2.2 : ℂ) *
    (nativeCoefficients B l V request j k).pressure n x) =
      (l.gaussian reference (V.map n x).1.2.2 : ℂ) * ((views B l V).coefficients request
        j).pressure n x
  simp_rw [native_pressure, ← Complex.real_smul]
  rw [l.gaussian_mask_sum, view_pressure]

theorem common_eq (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    (copyData B l V request j).common =
      ((views B l V).coefficients request j).withCutoff (views B l V).cutoff := by
  let a := copyData B l V request j
  let b := ((views B l V).coefficients request j).withCutoff (views B l V).cutoff
  have ha : a.common.amplitude = b.amplitude := funext fun n => funext fun x => common_amplitude B
    l V request j n x
  have hp : a.common.pressure = b.pressure := funext fun n => funext fun x => common_pressure B l V
    request j n x
  calc
    a.common = {a.background with amplitude := a.common.amplitude, pressure := a.common.pressure}
      := rfl
    _ = {a.background with amplitude := b.amplitude, pressure := b.pressure} := by rw [ha, hp]
    _ = b := rfl

/-- Exact coefficient equality precedes all differentiation.  In
particular every derivative of the native cutoffs remains in the curl. -/
theorem commonCorrected_eq (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    (copyData B l V request j).commonCorrected V.strip V.directions =
      (views B l V).exactCoefficients request j := by
  unfold PeriodizedWaveBounds.CopyData.commonCorrected
  rw [common_eq]
  rfl

/-! ## The literal current-state request and one physical reference -/

/-- The native copies use the current state's actual signed request. -/
noncomputable def actualCopyData (D : V.StateData) (j : Fin 2) :
    PeriodizedWaveBounds.CopyData Cylinder Frequency :=
  copyData B l V D.request j

theorem actual_commonCorrected_eq (D : V.StateData) (j : Fin 2) :
    (actualCopyData B l V D j).commonCorrected V.strip V.directions =
      (views B l V).exactCoefficients (stateData B l D).request j :=
  commonCorrected_eq B l V D.request j

/-- This equality holds before restriction to a physical graph, at every
point of the full slow/angle/fast strip. -/
theorem actual_amplitude_transport (D : V.StateData) (j : Fin 2)
    (n : ℕ) (x : Cylinder) (hx : x ∈ V.strip.domain) :
    (actualCopyData B l V D j).common.amplitude n x =
      V.velocity n • (periodizedPrimary B l).raw D.referenceRequest j reference (V.map n x) := by
  rw [actualCopyData, common_amplitude]
  exact (views B l V).amplitude_transport D.request D.referenceRequest j n x
    (D.request_transport n x hx)

theorem actual_amplitude_transport_germ (D : V.StateData) (j : Fin 2)
    (n : ℕ) {x : Cylinder} (hx : x ∈ V.strip.domain) :
    (actualCopyData B l V D j).common.amplitude n =ᶠ[𝓝 x]
      fun y => V.velocity n • (periodizedPrimary B l).raw D.referenceRequest j reference (V.map n
        y) := by
  filter_upwards [V.strip.isOpen_domain.mem_nhds hx] with y hy
  exact actual_amplitude_transport B l V D j n y hy

theorem actual_pressure_transport (D : V.StateData) (j : Fin 2) (n : ℕ)
    (hK : B.base.frequency reference ≠ 0)
    (G : PhysicalSignedWave.ChartGeometry B.base B.strip B.directions reference
      V.exponent V.referenceScale V.referenceCover)
    (H : PhysicalSignedWave.ChartGeometry
      (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {x : Cylinder} (hx : x ∈ V.strip.domain) (hr : 0 < x.1.1)
    (hPhi : DifferentiableAt ℝ (B.base.phase reference) (V.map n x)) :
    (actualCopyData B l V D j).common.pressure n x =
      PhysicalParticularWave.pressureWeight V.exponent (V.scale n) V.referenceScale •
        (periodizedPrimary B l).rawPressure D.referenceRequest j reference (V.map n x) := by
  rw [actualCopyData, common_pressure]
  exact (views B l V).pressure_transport D.request D.referenceRequest j n hr hK G H hPhi
    (D.request_transport n x hx)

/-- One genuine periodized Cartesian potential, retaining the same pulse,
reference state, scales, and integer covers as the native copies. -/
noncomputable def physicalPotential (D : V.StateData) (j : Fin 2) (delta : ℝ) : VelocityField :=
  (views B l V).physicalPotential D.referenceRequest j delta

noncomputable def physicalVelocity (D : V.StateData) (j : Fin 2) (delta : ℝ) : VelocityField :=
  SpatialCurl.spatialCurl (physicalPotential B l V D j delta)

noncomputable def physicalPressure (D : V.StateData) (j : Fin 2) (delta : ℝ) : PressureField :=
  (views B l V).physicalPressure D.referenceRequest j delta

theorem physicalVelocity_eq_curl (D : V.StateData) (j : Fin 2) (delta : ℝ) :
    physicalVelocity B l V D j delta = SpatialCurl.spatialCurl (physicalPotential B l V D j delta)
      := rfl

/-- The actual native-copy sum, corrected after cutoff and summation, is
the band view of the single constructed Cartesian curl.  Analytic inputs
concern the primitive reference data and coordinate charts. -/
theorem actual_wave_physical (D : V.StateData) (j : Fin 2) (n : ℕ)
    (R : (periodizedPrimary B l).Regular D.referenceRequest reference j)
    (A : (periodizedPrimary B l).Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : PhysicalSignedWave.ChartGeometry B.base B.strip B.directions reference
      V.exponent V.referenceScale V.referenceCover)
    (H : PhysicalSignedWave.ChartGeometry
      (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    (hradius : ∀ x ∈ V.strip.domain, 0 < x.1.1)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (vectorMode (((actualCopyData B l V D j).commonCorrected V.strip V.directions).frequency n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).phase n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).amplitude n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) component).re
        =
        V.scale n ^ CoordinateAlgebra.A V.exponent * CylindricalResidual.frame (-(z.2 1))
          (physicalVelocity B l V D j delta (z.1, CylindricalResidual.chart z.2)) component := by
  rw [actual_commonCorrected_eq]
  exact (stateData B l D).actual_wave_physical j n R A hK G H hmap hradius hz hdelta chart hchart
    component

theorem actual_pressure_physical (D : V.StateData) (j : Fin 2) (n : ℕ)
    (R : (periodizedPrimary B l).Regular D.referenceRequest reference j)
    (A : (periodizedPrimary B l).Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : PhysicalSignedWave.ChartGeometry B.base B.strip B.directions reference
      V.exponent V.referenceScale V.referenceCover)
    (H : PhysicalSignedWave.ChartGeometry
      (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (HarmonicCalculus.mode (((actualCopyData B l V D j).commonCorrected V.strip
      V.directions).frequency n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).phase n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).pressure n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)).re =
        V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
          physicalPressure B l V D j delta (z.1, CylindricalResidual.chart z.2) := by
  rw [actual_commonCorrected_eq]
  exact (stateData B l D).actual_pressure_physical j n R A hK G H hmap hz hdelta chart hchart

end Reference

/-! ## Support-local primitive regularity on the complete reference strip -/

section SupportLocal

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  (B : PhysicalSignedWave.PrimaryData U) (l : Layout)

noncomputable def referenceNativeUnit (j : Fin 2) (n : ℕ) (k : Frequency) (x : Cylinder) : Space :=
  PrimaryPulseBounds.normalizedPulse ((B.pulse j).frame n)
    ((B.pulse j).lam n) ((B.pulse j).u n) ((B.pulse j).L n)
    ((B.coordinate n x).1, l.nativeClock n k x.1.2.2)

theorem referenceUnit_eq_native (j : Fin 2) (n : ℕ) (k : Frequency) (x : Cylinder)
    (hk : l.nativeMask n k x.1.2.2 ≠ 0) :
    (periodizedPrimary B l).fundamental j n x = referenceNativeUnit B l j n k x := by
  change PrimaryPulseBounds.normalizedPulse _ _ _ _ (_, l.clock n x.1.2.2) = _
  rw [l.clock_eq_native n k x.1.2.2 hk]
  rfl

noncomputable def referenceScalar (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (n : ℕ) (x : Cylinder) : ℝ :=
  SignedWaveUpdate.signedScalar B.strip B.matrix B.target request B.mask j n x

theorem reference_raw_formula (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    (periodizedPrimary B l).raw request j n x =
      l.gaussian n x.1.2.2 • (l.mask n x.1.2.2 •
        (referenceScalar B request j n x •
          CurlClassBounds.complexify ((periodizedPrimary B l).fundamental j n x))) := by
  change l.gaussian n x.1.2.2 • ((periodizedPrimary B l).coefficients request j).amplitude n x = _
  rw [PhysicalSignedWave.PrimaryData.coefficients, coefficients_amplitude_at]
  have hs : SignedWaveUpdate.signedScalar (periodizedPrimary B l).strip
      (periodizedPrimary B l).matrix (periodizedPrimary B l).target request
      (periodizedPrimary B l).mask j n x = l.mask n x.1.2.2 * referenceScalar B request j n x := by
    change SignedWaveUpdate.signedScalar B.strip B.matrix B.target request
      (fun n x => B.mask n x * l.mask n x.1.2.2) j n x = _
    exact signedScalar_mul_mask _ _ _ _ _ _ _ _ _
  rw [hs, mul_smul]

theorem reference_raw_eq_sum (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    (periodizedPrimary B l).raw request j n = fun x =>
      ∑' k, l.nativeMask n k x.1.2.2 • (l.nativeGaussian n k x.1.2.2 •
        (referenceScalar B request j n x • CurlClassBounds.complexify (referenceNativeUnit B l j n
          k x))) := by
  funext x
  rw [reference_raw_formula, ← l.gaussian_mask_sum]
  apply tsum_congr
  intro k
  by_cases hk : l.nativeMask n k x.1.2.2 = 0
  · simp only [hk, zero_smul, smul_zero]
  · rw [referenceUnit_eq_native B l j n k x hk]
    exact smul_comm _ _ _

/-- Every condition is on the original slow data, native pulse, or
native support.  Inactive gaps need no uncut pulse-time hypothesis. -/
structure SupportedRegular (request : ℕ → Cylinder → Vec2) (reference : ℕ) (column : Fin 2) : Prop
  where
  coordinate : ContDiffOn ℝ ∞ (fun x => (B.coordinate reference x).1) B.strip.domain
  coordinate_mem : ∀ x ∈ B.strip.domain, (B.coordinate reference x).1 ∈ U.carrier reference
  native_time : ∀ k x, x ∈ B.strip.domain →
    (l.geometry reference).coordinates k x.1.2.2 ∈ tsupport (l.cutoff reference) →
      l.nativeClock reference k x.1.2.2 ∈ Ioo (0 : ℝ) 1
  prefactor : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => B.prefactor j n)
  target : ∀ j, ContDiffOn ℝ ∞ (fun x => B.target reference x j) B.strip.domain
  request : ∀ j, ContDiffOn ℝ ∞ (fun x => request reference x j) B.strip.domain
  mask : ContDiffOn ℝ ∞ (B.mask reference) B.strip.domain
  cone : ∀ x ∈ B.strip.domain, SmoothCovariance.StrictCone (B.matrix reference x) (B.target
    reference x)
  phase : ContDiffOn ℝ ∞ (B.base.phase reference) B.strip.domain
  normal_ne : ∀ x ∈ B.strip.domain, B.base.normal B.strip B.directions reference x ≠ 0
  normal_frame : ∀ k x, x ∈ B.strip.domain → l.nativeMask reference k x.1.2.2 ≠ 0 →
    B.base.normal B.strip B.directions reference x =
      ((B.pulse column).frame reference).normal ((B.coordinate reference x).1,
        (B.pulse column).L reference * l.nativeClock reference k x.1.2.2)

namespace SupportedRegular

variable {B l} {request : ℕ → Cylinder → Vec2} {reference : ℕ} {column : Fin 2}
  (R : SupportedRegular B l request reference column)

include R

theorem matrix_smooth (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => B.matrix reference x i j) B.strip.domain := by
  have hm := PrimaryPulseBounds.primaryCovariance_entry_polynomial U B.prefactor
    (fun j => (B.pulse j).frame) (fun j => (B.pulse j).lam) (fun j => (B.pulse j).u)
    (fun j => (B.pulse j).L) R.prefactor (fun j => (B.pulse j).pulse_jets)
    (fun j => (B.pulse j).lam_pos) (fun j => (B.pulse j).u_pos) (fun j => (B.pulse j).L_pos) i j
  exact (hm.smooth reference).comp R.coordinate R.coordinate_mem

theorem scalar_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (referenceScalar B request j reference) B.strip.domain := by
  have hi := SmoothCovariance.contDiffOn_inverse_solution R.matrix_smooth R.request
    (fun x hx => (R.cone x hx).det_ne_zero) j
  have ha := SmoothCovariance.contDiffOn_amplitudes R.matrix_smooth R.target R.cone j
  have hd : ∀ x ∈ B.strip.domain, 2 * SmoothCovariance.amplitudes
      (B.matrix reference x) (B.target reference x) j ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by norm_num) ((R.cone x hx).amplitudes_pos j).ne'
  exact (contDiffOn_const.mul (hi.div (contDiffOn_const.mul ha) hd)).mul R.mask

theorem unit_smoothAt (j : Fin 2) (k : Frequency) {x : Cylinder} (hx : x ∈ B.strip.domain)
    (hs : (l.geometry reference).coordinates k x.1.2.2 ∈ tsupport (l.cutoff reference)) :
    ContDiffAt ℝ ∞ (referenceNativeUnit B l j reference k) x := by
  have hc : ContDiff ℝ ∞ (fun y : Cylinder => l.nativeClock reference k y.1.2.2) :=
    (((l.geometry reference).coordinates_contDiff k).comp contDiff_fst.snd.snd).snd.div_const _
  have hu : ContDiffAt ℝ ∞ (PrimaryPulseBounds.normalizedPulse ((B.pulse j).frame reference)
      ((B.pulse j).lam reference) ((B.pulse j).u reference) ((B.pulse j).L reference))
      ((B.coordinate reference x).1, l.nativeClock reference k x.1.2.2) :=
    ((B.pulse j).pulse_jets.smooth reference).contDiffAt
    (((U.isOpen reference).prod isOpen_Ioo).mem_nhds
      ⟨R.coordinate_mem x hx, R.native_time k x hx hs⟩)
  exact hu.comp x
    ((R.coordinate.contDiffAt (B.strip.isOpen_domain.mem_nhds hx)).prodMk hc.contDiffAt)

/-- Smoothness is derived from the actual native sum, including its
zero germs between support cells. -/
theorem raw_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ ((periodizedPrimary B l).raw request j reference) B.strip.domain := by
  rw [reference_raw_eq_sum]
  apply l.maskedSum_contDiffOn reference (fun x : Cylinder => x.1.2.2) contDiff_fst.snd.snd
    B.strip.isOpen_domain
  intro k x hx hs
  have hg : ContDiff ℝ ∞ (fun y : Cylinder => l.nativeGaussian reference k y.1.2.2) :=
    GaussianTailFlat.profile_contDiff.comp
      ((((l.geometry reference).coordinates_contDiff k).comp contDiff_fst.snd.snd).snd.div_const _)
  exact hg.contDiffAt.smul
    ((R.scalar_smooth j).contDiffAt (B.strip.isOpen_domain.mem_nhds hx) |>.smul
      (CurlClassBounds.complexify.contDiff.contDiffAt.comp x (R.unit_smoothAt j k hx hs)))

theorem raw_tangent {x : Cylinder} (hx : x ∈ B.strip.domain) :
    normalDot (B.base.normal B.strip B.directions reference x)
      ((periodizedPrimary B l).raw request column reference x) = 0 := by
  classical
  rw [reference_raw_formula]
  by_cases hm : l.mask reference x.1.2.2 = 0
  · simp only [hm, zero_smul, smul_zero, normalDot]
    simp
  · have hk : ∃ k, l.nativeMask reference k x.1.2.2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hm
      change (∑' k, l.nativeMask reference k x.1.2.2) = 0
      simp only [h, tsum_zero]
    obtain ⟨k, hk⟩ := hk
    rw [referenceUnit_eq_native B l column reference k x hk]
    have ht : normalDot (B.base.normal B.strip B.directions reference x)
        (CurlClassBounds.complexify (referenceNativeUnit B l column reference k x)) = 0 := by
      rw [SignedWaveUpdate.normalDot_complexify, R.normal_frame k x hx hk]
      exact_mod_cast ((B.pulse column).frame reference).ambient_tangent
        ((B.coordinate reference x).1,
          (B.pulse column).L reference * l.nativeClock reference k x.1.2.2) _
    simp only [smul_smul]
    simpa only [one_smul, Complex.ofReal_one, one_mul, ht, mul_zero] using
      PhysicalParticularWave.normalDot_scaled 1
        (l.gaussian reference x.1.2.2 * (l.mask reference x.1.2.2 * referenceScalar B request
          column reference x))
        (B.base.normal B.strip B.directions reference x)
        (CurlClassBounds.complexify (referenceNativeUnit B l column reference k x))

end SupportedRegular

theorem fast_invariant : CopyAngularInvariance.Invariant ((0, 1) : Cylinder)
    (fun x : Cylinder => x.1.2.2) := by
  intro x t
  simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]

/-- Angular invariance is inherited from the same primary inputs.  The
new clock and native mask depend only on the auxiliary torus coordinate. -/
noncomputable def periodizedAngular {request : ℕ → Cylinder → Vec2} {reference : ℕ}
    (A : B.Angular request reference) : (periodizedPrimary B l).Angular request reference where
  mode := A.mode
  phase := A.phase
  coordinate := (A.coordinate.map Prod.fst).map₂
    (fast_invariant.map (l.clock reference)) Prod.mk
  target := A.target
  request := A.request
  mask := A.mask.map₂ (fast_invariant.map (l.mask reference)) (· * ·)
  normalMotion := A.normalMotion
  action := A.action

variable {reference : ℕ} (V : B.Views reference) (D : V.StateData)

/-- The integer harmonic block is built from the same corrected native
sum.  No independent wave is substituted into the iteration. -/
noncomputable def actualBlock (j : Fin 2) (angularFrequency : ℕ → ℤ) :
    CorrectionState.HarmonicBlock PhysicalResidualBridge.Lift :=
  SignedWaveUpdate.blockOfCoefficients
    ((actualCopyData B l V D j).commonCorrected V.strip V.directions) angularFrequency

theorem actualBlock_eq (j : Fin 2) (angularFrequency : ℕ → ℤ) :
    actualBlock B l V D j angularFrequency = SignedWaveUpdate.blockOfCoefficients
      ((views B l V).exactCoefficients D.request j) angularFrequency := by
  unfold actualBlock
  rw [actual_commonCorrected_eq, stateData_request]

/-- Full-strip realization from support-local native input regularity.
There is no condition on the uncut pulse in inactive periodic gaps. -/
theorem supported_wave_physical (j : Fin 2) (n : ℕ)
    (R : SupportedRegular B l D.referenceRequest reference j)
    (A : B.Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : PhysicalSignedWave.ChartGeometry B.base B.strip B.directions reference
      V.exponent V.referenceScale V.referenceCover)
    (H : PhysicalSignedWave.ChartGeometry
      (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    (hradius : ∀ x ∈ V.strip.domain, 0 < x.1.1)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (vectorMode (((actualCopyData B l V D j).commonCorrected V.strip V.directions).frequency n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).phase n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).amplitude n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) component).re
        =
        V.scale n ^ CoordinateAlgebra.A V.exponent * CylindricalResidual.frame (-(z.2 1))
          (physicalVelocity B l V D j delta (z.1, CylindricalResidual.chart z.2)) component := by
  rw [actual_commonCorrected_eq, stateData_request,
    ← (views B l V).wave_eq_exact D.request j n H]
  have hphi : ContDiffOn ℝ ∞ (((views B l V).coefficients D.request j).phase n) V.strip.domain :=
    contDiffOn_const.mul (R.phase.comp (V.map n).contDiff.contDiffOn hmap)
  have ha : ContDiffOn ℝ ∞
      ((((views B l V).coefficients D.request j).withCutoff (views B l V).cutoff).amplitude n)
      V.strip.domain := by
    apply (((R.raw_smooth j).comp (V.map n).contDiff.contDiffOn hmap).const_smul
      (V.velocity n)).congr
    intro x hx
    exact (views B l V).amplitude_transport D.request D.referenceRequest j n x (D.request_transport
      n x hx)
  have hnrel (x : Cylinder) (hx : x ∈ V.strip.domain) :
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        (((views B l V).coefficients D.request j).phase n) x =
      V.normal n • B.base.normal B.strip B.directions reference (V.map n x) := by
    exact (congrFun H.normal x).symm.trans ((views B l V).normal_transport G n H (hradius x hx)
      ((R.phase.contDiffAt (B.strip.isOpen_domain.mem_nhds (hmap hx))).differentiableAt (by simp)))
  have hn (x : Cylinder) (hx : x ∈ V.strip.domain) :
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        (((views B l V).coefficients D.request j).phase n) x ≠ 0 := by
    rw [hnrel x hx]
    exact smul_ne_zero (PhysicalParticularWave.normalWeight_ne (V.scale_pos n) V.referenceScale_pos
      (V.frequency_ne n) hK) (R.normal_ne _ (hmap hx))
  have ht (x : Cylinder) (hx : x ∈ V.strip.domain) :
      normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        (((views B l V).coefficients D.request j).phase n) x)
        ((((views B l V).coefficients D.request j).withCutoff (views B l V).cutoff).amplitude n x)
          = 0 := by
    rw [hnrel x hx, (views B l V).amplitude_transport D.request D.referenceRequest j n x
      (D.request_transport n x hx), PhysicalParticularWave.normalDot_scaled]
    change (V.normal n : ℂ) * (V.velocity n : ℂ) *
      normalDot (B.base.normal B.strip B.directions reference (V.map n x))
        ((periodizedPrimary B l).raw D.referenceRequest j reference (V.map n x)) = 0
    rw [R.raw_tangent (hmap hx), mul_zero]
  have hp : ∀ y ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
    V.strip.domain,
      B.base.frequency reference * (views B l V).physicalPhase y =
        V.frequency n * ((views B l V).coefficients D.request j).phase n
          ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y) := by
    intro y hy
    change B.base.frequency reference * B.base.phase reference
        ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map y) =
      V.frequency n * ((B.base.frequency reference / V.frequency n) *
        B.base.phase reference (V.map n
          ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y)))
    rw [V.map_graph n hy.1]
    field_simp [V.frequency_ne n]
  have hav : ∀ y ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
    V.strip.domain,
      (views B l V).physicalRaw D.referenceRequest j y = V.scale n ^ (-CoordinateAlgebra.A
        V.exponent) •
        (((views B l V).coefficients D.request j).withCutoff (views B l V).cutoff).amplitude n
          ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y) := by
    intro y hy
    rw [(views B l V).amplitude_transport D.request D.referenceRequest j n _ (D.request_transport _
      _ hy.2)]
    change V.referenceScale ^ (-CoordinateAlgebra.A V.exponent) •
        (periodizedPrimary B l).raw D.referenceRequest j reference
          ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map y)
            =
      V.scale n ^ (-CoordinateAlgebra.A V.exponent) • V.velocity n •
        (periodizedPrimary B l).raw D.referenceRequest j reference
          (V.map n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y))
    rw [V.map_graph n hy.1, smul_smul]
    change V.referenceScale ^ (-CoordinateAlgebra.A V.exponent) • _ =
      (V.scale n ^ (-CoordinateAlgebra.A V.exponent) * V.velocity n) • _
    congr 1
    rw [mul_comm]
    exact (PhysicalParticularWave.ratioPower_cancel (V.scale_pos n) V.referenceScale_pos _).symm
  exact PhysicalCurlCovariance.reference_correctedWave_constructed (V.scale_pos n) V.exponent
    (V.cover n)
    V.strip.isOpen_domain (fun x hx => (hradius x hx).ne') hK (V.frequency_ne n) hphi ha hn ht
    (views B l V).physicalPhase ((views B l V).physicalRaw D.referenceRequest j) hp hav
    ((views B l V).referencePotential_periodic (periodizedAngular B l A) hK j)
    hz hdelta chart hchart component

/-- Pressure uses the same native quotient, normal motion, action and
single Gaussian, with its physical squared-velocity scaling. -/
theorem supported_pressure_physical (j : Fin 2) (n : ℕ)
    (R : SupportedRegular B l D.referenceRequest reference j)
    (A : B.Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : PhysicalSignedWave.ChartGeometry B.base B.strip B.directions reference
      V.exponent V.referenceScale V.referenceCover)
    (H : PhysicalSignedWave.ChartGeometry
      (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (HarmonicCalculus.mode (((actualCopyData B l V D j).commonCorrected V.strip
      V.directions).frequency n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).phase n)
      (((actualCopyData B l V D j).commonCorrected V.strip V.directions).pressure n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)).re =
        V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
          physicalPressure B l V D j delta (z.1, CylindricalResidual.chart z.2) := by
  have hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z
    ∈ B.strip.domain := by
    rw [← V.map_graph n hz.1]
    exact hmap hz.2
  have he := (views B l V).pressure_physical D.request D.referenceRequest j n
    (periodizedAngular B l A) hK G H hz.1
    ((R.phase.contDiffAt (B.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (by
      have ht := D.request_transport n
        ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) hz.2
      simp only [V.map_graph n hz.1] at ht
      exact ht)
    hdelta chart hchart
  rw [(views B l V).pressureMode_eq_exact D.request j n] at he
  simp only [actual_commonCorrected_eq, stateData_request] at he ⊢
  exact he

end SupportLocal

end NavierStokes.ActualPeriodizedSignedRealization
