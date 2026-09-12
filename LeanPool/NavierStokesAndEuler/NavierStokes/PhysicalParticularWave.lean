/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCurlCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualTZ
public import LeanPool.NavierStokesAndEuler.NavierStokes.StateReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledTangentTransport

/-!
# Actual reference particular waves in physical coordinates

The input is the constructed reference Volterra solve.  Curl identities
are conclusions, not compatibility assumptions on solved velocities.
-/

@[expose] public section


namespace NavierStokes.PhysicalParticularWave

open Set Filter Function ProblemStatement HarmonicCalculus
open ParticularWaveAssembly ParticularWaveBounds LinearWaveBounds WeightedClasses
open CommonCoverSolve TorusInverse CopyAngularInvariance
open scoped ContDiff Topology

noncomputable section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Raw common, given by `actualCommonCoefficients D.reference D.charts D.context D.state
D.carrierBlock D.gaussianInput D.aliasInput j D.background`. -/
noncomputable def rawCommon (D : AssemblyData P) (j : ℤ) : WaveCoefficients ((P × ℝ) × Plane) :=
  actualCommonCoefficients D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background

/-- Common potential, given by `(rawCommon D j).curlPotential D.strip D.directions n`. -/
noncomputable def commonPotential (D : AssemblyData P) (j : ℤ) (n : ℕ) :
    ((P × ℝ) × Plane) → ComplexVector :=
  (rawCommon D j).curlPotential D.strip D.directions n

/-- Common pressure, given by `mode ((rawCommon D j).frequency n) ((rawCommon D j).phase n)
((rawCommon D j).pressure n)`. -/
noncomputable def commonPressure (D : AssemblyData P) (j : ℤ) (n : ℕ) :
    ((P × ℝ) × Plane) → ℂ :=
  mode ((rawCommon D j).frequency n) ((rawCommon D j).phase n) ((rawCommon D j).pressure n)

section ActualInputs

variable (D : AssemblyData P) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)

include C

theorem commonRaw_germ (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ D.strip.domain) :
    (rawCommon D j).amplitude n =ᶠ[𝓝 x]
      (fun y => C.slot.cutoff n y •
        (actualCopyCoefficients D.reference D.charts D.context D.state D.carrierBlock
          D.gaussianInput D.aliasInput j D.background D.copy).amplitude n y) := by
  exact (actualCommon_raw_germ D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput C.harmonic_ne C.frequency_ne D.background D.copy
    C.slot.cutoff n x (C.patch_open n) (C.patch_injective n) (C.cutoff_support n)
    (C.domain_patch n x hx) (C.cutoff_germ n hx)).1

theorem commonRaw_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ ((rawCommon D j).amplitude n) D.strip.domain := by
  intro x hx
  have hs := ((C.slot.cutoff_memClass.smooth n).smul (C.local_result.1.smooth n)).contDiffAt
    (D.strip.isOpen_domain.mem_nhds hx)
  exact (hs.congr_of_eventuallyEq (commonRaw_germ D C n hx)).contDiffWithinAt

theorem commonRaw_tangent (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ D.strip.domain) :
    normalDot ((rawCommon D j).normal D.strip D.directions n x)
      ((rawCommon D j).amplitude n x) = 0 := by
  rw [(commonRaw_germ D C n hx).eq_of_nhds]
  change normalDot ((actualCarrier D.background D.carrierBlock j).normal D.strip D.directions n x)
      _ = 0
  have he : normalDot ((actualCarrier D.background D.carrierBlock j).normal D.strip D.directions n
      x)
      (C.slot.cutoff n x •
        (actualCopyCoefficients D.reference D.charts D.context D.state D.carrierBlock
          D.gaussianInput D.aliasInput j D.background D.copy).amplitude n x) =
      (C.slot.cutoff n x : ℂ) * normalDot
        ((actualCarrier D.background D.carrierBlock j).normal D.strip D.directions n x)
        ((actualCopyCoefficients D.reference D.charts D.context D.state D.carrierBlock
          D.gaussianInput D.aliasInput j D.background D.copy).amplitude n x) := by
    simp only [normalDot, Pi.smul_apply, Complex.real_smul]
    ring
  rw [he, C.raw_tangent n x hx, mul_zero]

theorem commonPotential_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (commonPotential D j n) D.strip.domain := by
  exact CurlClassBounds.vectorPotential_contDiffOn (C.background.cylindrical n)
    ((j : ℝ) * D.carrierBlock.frequency n) (C.background.phase_smooth n)
    (commonRaw_smooth D C n) (C.normal_nonzero n)

/-- The constructed common coefficient, including its native cutoff,
gives exactly the wave already used by the assembly. -/
theorem commonPotential_curl (n : ℕ) {x : (P × ℝ) × Plane} (hx : x ∈ D.strip.domain) :
    CurlClassBounds.cylindricalCurl (D.background.radius n) (D.directions.radialField n)
      (fun _ => D.directions.angular) (D.directions.axialField D.strip n)
      (commonPotential D j n) x =
    vectorMode ((D.wave j).frequency n) ((D.wave j).phase n) ((D.wave j).amplitude n) x := by
  exact CurlClassBounds.cylindricalCurl_vectorPotential (C.background.cylindrical n)
    (C.frequency_nonzero n) (C.background.phase_smooth n) (commonRaw_smooth D C n)
    (C.normal_nonzero n) (fun y hy => commonRaw_tangent D C n hy) hx

theorem commonPotential_fullTurn (n : ℕ) (x : (P × ℝ) × Plane) :
    commonPotential D j n (x + (2 * Real.pi) • D.directions.angular) =
      commonPotential D j n x := by
  have ha : Invariant D.directions.angular ((rawCommon D j).amplitude n) := by
    rw [C.background.angular]
    exact angleLift_invariant (actualBandVelocity D.reference D.charts D.context D.state
      D.carrierBlock D.gaussianInput D.aliasInput j n)
  have hΦ : AffinePhase D.directions.angular
      ((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) := by
    rw [C.background.angular]
    exact actualCarrier_affine _ _ _ _
  have hf : ((j : ℝ) * D.carrierBlock.frequency n) *
      ((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n) =
      ((j * D.carrierBlock.angularFrequency n : ℤ) : ℝ) := by
    push_cast
    field_simp [C.frequency_ne n]
  exact PhysicalCurlCovariance.vectorPotential_fullTurn (j * D.carrierBlock.angularFrequency n)
    (C.background.radius_invariant n) (C.background.radial_invariant n) (Invariant.const _)
    (C.background.axial_invariant n) hΦ ha hf x

theorem commonPressure_fullTurn (n : ℕ) (x : (P × ℝ) × Plane) :
    commonPressure D j n (x + (2 * Real.pi) • D.directions.angular) =
      commonPressure D j n x := by
  have hp : Invariant D.directions.angular ((rawCommon D j).pressure n) := by
    rw [C.background.angular]
    exact angleLift_invariant (actualBandPressure D.reference D.charts D.context D.state
      D.carrierBlock D.gaussianInput D.aliasInput j n)
  have hΦ : AffinePhase D.directions.angular
      ((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) := by
    rw [C.background.angular]
    exact actualCarrier_affine _ _ _ _
  have hf : ((j : ℝ) * D.carrierBlock.frequency n) *
      ((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n) =
      ((j * D.carrierBlock.angularFrequency n : ℤ) : ℝ) := by
    push_cast
    field_simp [C.frequency_ne n]
  have he : phaseFactor ((j : ℝ) * D.carrierBlock.frequency n) *
      (((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n *
        (2 * Real.pi) : ℝ) : ℂ) =
      ((j * D.carrierBlock.angularFrequency n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hf' : (((j : ℝ) * D.carrierBlock.frequency n : ℝ) : ℂ) *
        (((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n : ℝ) : ℂ) =
        ((j * D.carrierBlock.angularFrequency n : ℤ) : ℂ) := by exact_mod_cast hf
    unfold phaseFactor
    push_cast
    calc
      _ = ((((j : ℝ) * D.carrierBlock.frequency n : ℝ) : ℂ) *
        (((D.carrierBlock.angularFrequency n : ℝ) / D.carrierBlock.frequency n : ℝ) : ℂ)) *
        (2 * Real.pi * Complex.I) := by push_cast; ring
      _ = _ := by rw [hf']; simp only [Int.cast_mul]
  unfold commonPressure
  change mode ((j : ℝ) * D.carrierBlock.frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) ((rawCommon D j).pressure n)
      (x + (2 * Real.pi) • D.directions.angular) = _
  rw [mode_translate hp hΦ, he, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rfl

end ActualInputs

/-! ## The actual physical changes of band and cover -/

/-- Lift: an abbreviation for `PhysicalResidualBridge.Lift`. -/
abbrev Lift := PhysicalResidualBridge.Lift
/-- Cylinder: an abbreviation for `PhysicalResidualBridge.Cylinder`. -/
abbrev Cylinder := PhysicalResidualBridge.Cylinder
/-- Parameter: an abbreviation for `ℝ × Plane`. -/
abbrev Parameter := ℝ × Plane
/-- Wave space: an abbreviation for `(Parameter × ℝ) × Plane`. -/
abbrev WaveSpace := (Parameter × ℝ) × Plane

/-- The wave solver uses `(R,(T,Z),theta,Y)`. The physical graph theorem
uses `(R,(Z,T),Y,theta)`. This is the literal isometric reordering. -/
noncomputable def waveEquiv : Cylinder ≃ₗᵢ[ℝ] WaveSpace :=
  (PhysicalResidualTZ.swapCylinder.trans
    (StateReindex.cylinder (ParticularWaveBounds.liftAssoc Plane))).trans angleShuffle

@[simp] theorem waveEquiv_apply (x : Cylinder) :
    waveEquiv x = (((x.1.1, (x.1.2.1.2, x.1.2.1.1)), x.2), x.1.2.2) := rfl

/-- Native map, given by `waveEquiv ((PhysicalResidualBridge.commonGraph Q h i).map z)`. -/
noncomputable def nativeMap (h Q : ℝ) (i : ℕ) (z : SpaceTime) : WaveSpace :=
  waveEquiv ((PhysicalResidualBridge.commonGraph Q h i).map z)

/-- Ratio power, given by `Q ^ a / Qr ^ a`. -/
noncomputable def ratioPower (Q Qr a : ℝ) : ℝ := Q ^ a / Qr ^ a

theorem ratioPower_pos {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    0 < ratioPower Q Qr a := div_pos (Real.rpow_pos_of_pos hQ _) (Real.rpow_pos_of_pos hQr _)

theorem ratioPower_cancel {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    ratioPower Q Qr a * Q ^ (-a) = Qr ^ (-a) := by
  unfold ratioPower
  rw [Real.rpow_neg hQ.le, Real.rpow_neg hQr.le]
  field_simp [(Real.rpow_pos_of_pos hQ a).ne', (Real.rpow_pos_of_pos hQr a).ne']

theorem ratioPower_neg_div {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    Qr ^ (-a) / Q ^ (-a) = ratioPower Q Qr a := by
  unfold ratioPower
  rw [Real.rpow_neg hQ.le, Real.rpow_neg hQr.le]
  field_simp [(Real.rpow_pos_of_pos hQ a).ne', (Real.rpow_pos_of_pos hQr a).ne']

theorem ratioPower_mul {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a b : ℝ) :
    ratioPower Q Qr a * ratioPower Q Qr b = ratioPower Q Qr (a + b) := by
  unfold ratioPower
  rw [Real.rpow_add hQ, Real.rpow_add hQr]
  ring

theorem ratioPower_div {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a b : ℝ) :
    ratioPower Q Qr a / ratioPower Q Qr b = ratioPower Q Qr (a - b) := by
  unfold ratioPower
  rw [Real.rpow_sub hQ, Real.rpow_sub hQr]
  field_simp [(Real.rpow_pos_of_pos hQ b).ne', (Real.rpow_pos_of_pos hQr a).ne',
    (Real.rpow_pos_of_pos hQr b).ne']

/-- A band-to-reference change, in the `(Z,T)` order used by PCC.
The slow-coordinate swap is supplied by `waveEquiv`. -/
noncomputable def chartChange (h Q Qr : ℝ) (gap : ℕ) : Lift →L[ℝ] Lift :=
  MeanChartCompatibility.chartLinear (ratioPower Q Qr (1 / 2))
    (((ratioPower Q Qr (CoordinateAlgebra.D h) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ratioPower Q Qr 1 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prodMap
        (coverPower gap).toContinuousLinearMap)

@[simp] theorem chartChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : Lift) :
    chartChange h Q Qr gap x =
      (ratioPower Q Qr (1 / 2) * x.1,
        ((ratioPower Q Qr (CoordinateAlgebra.D h) * x.2.1.1,
          ratioPower Q Qr 1 * x.2.1.2), coverPower gap x.2.2)) := rfl

/-- Cylinder change, given by `((chartChange h Q Qr gap).comp (ContinuousLinearMap.fst ℝ Lift
ℝ)).prod (ContinuousLinearMap.snd ℝ Lift ℝ)`. -/
noncomputable def cylinderChange (h Q Qr : ℝ) (gap : ℕ) : Cylinder →L[ℝ] Cylinder :=
  ((chartChange h Q Qr gap).comp (ContinuousLinearMap.fst ℝ Lift ℝ)).prod
    (ContinuousLinearMap.snd ℝ Lift ℝ)

@[simp] theorem cylinderChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    cylinderChange h Q Qr gap x = (chartChange h Q Qr gap x.1, x.2) := rfl

theorem cylinderChange_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map z) =
      (PhysicalResidualBridge.commonGraph Qr h (i + gap)).map z := by
  rw [PhysicalResidualBridge.commonGraph_map hQ h i hz,
    PhysicalResidualBridge.commonGraph_map hQr h (i + gap) hz]
  apply Prod.ext
  · apply Prod.ext
    · simp only [cylinderChange_apply, chartChange_apply, ← mul_assoc, ratioPower_cancel hQ hQr]
    · apply Prod.ext
      · apply Prod.ext
        · simp only [cylinderChange_apply, chartChange_apply, ← mul_assoc, ratioPower_cancel hQ hQr]
        · change ratioPower Q Qr 1 * ((1 - z.1) / Q) = (1 - z.1) / Qr
          simp only [ratioPower, Real.rpow_one]
          field_simp
      · change coverPower gap ((SlotGeometry.cover ^ i) _) = (SlotGeometry.cover ^ (i + gap)) _
        rw [coverPower_apply, ← _root_.mul_apply_eq_comp, ← pow_add, Nat.add_comm gap i]
  · rfl

/-- Velocity weight, given by `ratioPower Q Qr (CoordinateAlgebra.A h)`. -/
noncomputable def velocityWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (CoordinateAlgebra.A h)
/-- Clock weight, given by `ratioPower Q Qr (CoordinateAlgebra.A h + 1 / 2)`. -/
noncomputable def clockWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (CoordinateAlgebra.A h + 1 / 2)
/-- Source weight, given by `ratioPower Q Qr (2 * CoordinateAlgebra.A h + 1 / 2)`. -/
noncomputable def sourceWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (2 * CoordinateAlgebra.A h + 1 /
    2)
/-- Pressure weight, given by `ratioPower Q Qr (2 * CoordinateAlgebra.A h)`. -/
noncomputable def pressureWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (2 * CoordinateAlgebra.A h)
/-- Normal weight, given by `(Kr / K) * ratioPower Q Qr (1 / 2)`. -/
noncomputable def normalWeight (Q Qr K Kr : ℝ) : ℝ := (Kr / K) * ratioPower Q Qr (1 / 2)

theorem clock_mul_velocity {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    clockWeight h Q Qr * velocityWeight h Q Qr = sourceWeight h Q Qr := by
  unfold clockWeight velocityWeight sourceWeight
  rw [ratioPower_mul hQ hQr]
  congr 1
  ring

/-- Both clock scaling and normal scaling are needed for the physical
pressure weight. Their frequency factors cancel exactly. -/
theorem pressure_scaling {Q Qr K Kr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (h : ℝ) :
    (clockWeight h Q Qr * velocityWeight h Q Qr / normalWeight Q Qr K Kr) * (Kr / K) =
      pressureWeight h Q Qr := by
  rw [clock_mul_velocity hQ hQr]
  unfold normalWeight pressureWeight sourceWeight
  calc
    _ = ratioPower Q Qr (2 * CoordinateAlgebra.A h + 1 / 2) /
        ratioPower Q Qr (1 / 2) := by
      field_simp [hK, hKr, (ratioPower_pos hQ hQr (1 / 2)).ne']
    _ = _ := by
      rw [ratioPower_div hQ hQr]
      congr 1
      ring

theorem linear_change_direction {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) {f : X → E} {g : X → F} {x v : X} {a b : ℝ}
    {u : E} {w : F} (ha : a ≠ 0) (hf : DifferentiableAt ℝ f x)
    (he : (fun y => C (f y)) =ᶠ[𝓝 x] g)
    (hdf : fderiv ℝ f x v = a • u) (hdg : fderiv ℝ g x v = b • w) :
    C u = (b / a) • w := by
  have hd := congrArg (fun L : X →L[ℝ] F => L v) he.fderiv_eq
  change fderiv ℝ (C ∘ f) x v = fderiv ℝ g x v at hd
  rw [fderiv_comp x C.differentiableAt hf, ContinuousLinearMap.fderiv] at hd
  simp only [ContinuousLinearMap.comp_apply, hdf, map_smul, hdg] at hd
  calc
    C u = a⁻¹ • (a • C u) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • (b • w) := by rw [hd]
    _ = (b / a) • w := by rw [smul_smul]; congr 1; ring

theorem cylinderChange_graph_germ {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    (fun y => cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map y)) =ᶠ[𝓝 z]
      (PhysicalResidualBridge.commonGraph Qr h (i + gap)).map := by
  have hn : {y : SpaceTime | 0 < y.2 0} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds hz
  exact eventually_of_mem hn (fun y hy => cylinderChange_graph hQ hQr h i gap hy)

theorem cylinderChange_radial_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.radial (G.map z)) =
      ratioPower Q Qr (1 / 2) • H.radial (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_radial hn) (H.map_radial hr)
  change _ = (Qr ^ (-(1 / 2 : ℝ)) / Q ^ (-(1 / 2 : ℝ))) • _ at he
  rwa [ratioPower_neg_div hQ hQr] at he

theorem cylinderChange_axial_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.axial (G.map z)) =
      ratioPower Q Qr (1 / 2) • H.axial (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_axial hn) (H.map_axial hr)
  change _ = (Qr ^ (-(1 / 2 : ℝ)) / Q ^ (-(1 / 2 : ℝ))) • _ at he
  rwa [ratioPower_neg_div hQ hQr] at he

theorem cylinderChange_temporal_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.temporal (G.map z)) =
      clockWeight h Q Qr • H.temporal (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (mul_pos (Real.rpow_pos_of_pos hQ (-CoordinateAlgebra.A h))
      (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ)))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_temporal hn) (H.map_temporal hr)
  have hG : G.velocityScale * G.radialScale = Q ^ (-(CoordinateAlgebra.A h + 1 / 2)) := by
    change Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) = _
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hH : H.velocityScale * H.radialScale = Qr ^ (-(CoordinateAlgebra.A h + 1 / 2)) := by
    change Qr ^ (-CoordinateAlgebra.A h) * Qr ^ (-(1 / 2 : ℝ)) = _
    rw [← Real.rpow_add hQr]
    congr 1
    ring
  change _ = (H.velocityScale * H.radialScale / (G.velocityScale * G.radialScale)) • _ at he
  rw [hG, hH, ratioPower_neg_div hQ hQr] at he
  exact he

theorem radial_sameRadius (G : PhysicalResidualBridge.ScaledGraph) {x y : Cylinder}
    (hxy : x.1.1 = y.1.1) : G.radial x = G.radial y := by
  simp only [PhysicalResidualBridge.ScaledGraph.radial, hxy]

theorem cylinderChange_radial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {x : Cylinder} (hx : 0 < x.1.1) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.radial x) =
      ratioPower Q Qr (1 / 2) • H.radial (cylinderChange h Q Qr gap x) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  let z : SpaceTime := (0, AxisymmetricResidual.pack (Q ^ (1 / 2 : ℝ) * x.1.1) 0 0)
  have hz : 0 < z.2 0 := by
    simpa only [z, AxisymmetricResidual.pack_zero] using mul_pos (Real.rpow_pos_of_pos hQ (1 / 2))
        hx
  have hn : (G.map z).1.1 = x.1.1 := by
    change Q ^ (-(1 / 2 : ℝ)) * (AxisymmetricResidual.pack (Q ^ (1 / 2 : ℝ) * x.1.1) 0 0) 0 = x.1.1
    rw [AxisymmetricResidual.pack_zero]
    rw [← mul_assoc, ← Real.rpow_add hQ, neg_add_cancel, Real.rpow_zero, one_mul]
  have hr : (H.map z).1.1 = (cylinderChange h Q Qr gap x).1.1 := by
    have he := congrArg (fun y : Cylinder => y.1.1) (cylinderChange_graph hQ hQr h i gap hz)
    change ratioPower Q Qr (1 / 2) * (G.map z).1.1 = (H.map z).1.1 at he
    rw [hn] at he
    exact he.symm
  have he := cylinderChange_radial_graph hQ hQr h i gap hz
  change cylinderChange h Q Qr gap (G.radial (G.map z)) =
    ratioPower Q Qr (1 / 2) • H.radial (H.map z) at he
  rwa [radial_sameRadius G hn, radial_sameRadius H hr] at he

theorem cylinderChange_axial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (x : Cylinder) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.axial x) =
      ratioPower Q Qr (1 / 2) • H.axial (cylinderChange h Q Qr gap x) := by
  exact cylinderChange_axial_graph hQ hQr h i gap
    (z := (0, AxisymmetricResidual.pack 1 0 0)) (by simp)

theorem cylinderChange_temporal {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (x : Cylinder) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.temporal x) =
      clockWeight h Q Qr • H.temporal (cylinderChange h Q Qr gap x) := by
  exact cylinderChange_temporal_graph hQ hQr h i gap
    (z := (0, AxisymmetricResidual.pack 1 0 0)) (by simp)

theorem cylinderChange_angular (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    cylinderChange h Q Qr gap (PhysicalResidualBridge.ScaledGraph.angular x) =
      PhysicalResidualBridge.ScaledGraph.angular (cylinderChange h Q Qr gap x) := by
  change (chartChange h Q Qr gap 0, 1) = (0, 1)
  rw [map_zero]

/-- The normal scale comes from the actual spatial chart differential
and the raw carrier phase, independently of any solved velocity. -/
theorem phaseNormal_chartChange {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (K Kr : ℝ) {x : Cylinder} (hx : 0 < x.1.1)
    {Φ : Cylinder → ℝ} (hΦ : DifferentiableAt ℝ Φ (cylinderChange h Q Qr gap x)) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius G.radial
      PhysicalResidualBridge.ScaledGraph.angular G.axial
      (fun y => (Kr / K) * Φ (cylinderChange h Q Qr gap y)) x =
    normalWeight Q Qr K Kr • phaseNormal PhysicalResidualBridge.ScaledGraph.radius H.radial
      PhysicalResidualBridge.ScaledGraph.angular H.axial Φ (cylinderChange h Q Qr gap x) := by
  exact PhysicalCurlCovariance.phaseNormal_pull
    (Γ := cylinderChange h Q Qr gap) (x := x)
    (R := PhysicalResidualBridge.ScaledGraph.radius) (r :=
        PhysicalResidualBridge.ScaledGraph.radius)
    (Sr := (PhysicalResidualBridge.commonGraph Q h i).radial)
    (Sθ := PhysicalResidualBridge.ScaledGraph.angular) (Sz := (PhysicalResidualBridge.commonGraph Q
        h i).axial)
    (Vr := (PhysicalResidualBridge.commonGraph Qr h (i + gap)).radial)
    (Vθ := PhysicalResidualBridge.ScaledGraph.angular)
    (Vz := (PhysicalResidualBridge.commonGraph Qr h (i + gap)).axial)
    (ratioPower_pos hQ hQr (1 / 2)).ne' hx.ne'
    (cylinderChange h Q Qr gap).differentiableAt
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_radial hQ hQr h i gap hx)
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_angular h Q Qr gap x)
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_axial hQ hQr h i gap x)
    rfl hΦ (Kr / K)

theorem phaseNormal_chartChange_of_phase {Q Qr K Kr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (hK : K ≠ 0) (h : ℝ) (i gap : ℕ) {x : Cylinder} (hx : 0 < x.1.1)
    {Φ Ψ : Cylinder → ℝ} (hΨ : DifferentiableAt ℝ Ψ (cylinderChange h Q Qr gap x))
    (hphase : (fun y => K * Φ y) =ᶠ[𝓝 x] fun y => Kr * Ψ (cylinderChange h Q Qr gap y)) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius G.radial
      PhysicalResidualBridge.ScaledGraph.angular G.axial Φ x =
    normalWeight Q Qr K Kr • phaseNormal PhysicalResidualBridge.ScaledGraph.radius H.radial
      PhysicalResidualBridge.ScaledGraph.angular H.axial Ψ (cylinderChange h Q Qr gap x) := by
  have he : Φ =ᶠ[𝓝 x] fun y => (Kr / K) * Ψ (cylinderChange h Q Qr gap y) := by
    filter_upwards [hphase] with y hy
    apply mul_left_cancel₀ hK
    rw [hy]
    field_simp
  have hn : phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial Φ x =
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (fun y => (Kr / K) * Ψ (cylinderChange h Q Qr gap y)) x := by
    have hD (V : Cylinder → Cylinder) : along V Φ x =
        along V (fun y => (Kr / K) * Ψ (cylinderChange h Q Qr gap y)) x :=
      (along_germ he V).eq_of_nhds
    simp only [phaseNormal, hD]
  exact hn.trans (phaseNormal_chartChange hQ hQr h i gap K Kr hx hΨ)

/-! ## One potential built from the actual reference solve -/

/-- Reference raw, given by `angleLift (referenceVelocity D.reference D.context D.state
D.carrierBlock D.gaussianInput D.aliasInput j)`. -/
noncomputable def referenceRaw (D : AssemblyData Parameter) (j : ℤ) : WaveSpace → ComplexVector :=
  angleLift (referenceVelocity D.reference D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j)

/-- Reference raw pressure, given by `angleLift (ParticularWaveAssembly.referencePressure
D.reference D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j)`. -/
noncomputable def referenceRawPressure (D : AssemblyData Parameter) (j : ℤ) : WaveSpace → ℂ :=
  angleLift (ParticularWaveAssembly.referencePressure D.reference D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j)

/-- Reference frequency, given by `(j : ℝ) * D.carrierBlock.frequency D.reference.band`. -/
noncomputable def referenceFrequency (D : AssemblyData Parameter) (j : ℤ) : ℝ :=
  (j : ℝ) * D.carrierBlock.frequency D.reference.band

/-- Reference phase, given by `(actualCarrier D.background D.carrierBlock j).phase
D.reference.band`. -/
noncomputable def referencePhase (D : AssemblyData Parameter) (j : ℤ) : WaveSpace → ℝ :=
  (actualCarrier D.background D.carrierBlock j).phase D.reference.band

/-- Physical phase, defined pointwise by `referencePhase D j (nativeMap h Qr I z)`. -/
noncomputable def physicalPhase (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ℝ := fun z => referencePhase D j (nativeMap h Qr I z)

/-- Physical raw, defined pointwise by `Qr ^ (-CoordinateAlgebra.A h) • referenceRaw D j
(nativeMap h Qr I z)`. -/
noncomputable def physicalRaw (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ComplexVector :=
  fun z => Qr ^ (-CoordinateAlgebra.A h) • referenceRaw D j (nativeMap h Qr I z)

/-- The native cutoff is already inside the reference common solve.
The potential is taken once, after that solve and before differentiation. -/
noncomputable def referencePotential (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential (referenceFrequency D j)
    (physicalPhase D h Qr I j) (physicalRaw D h Qr I j)

/-- Physical potential, given by `PhysicalCurlCovariance.globalCartesianPotential delta
(referencePotential D h Qr I j)`. -/
noncomputable def physicalPotential (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (j : ℤ) : VelocityField :=
  PhysicalCurlCovariance.globalCartesianPotential delta (referencePotential D h Qr I j)

/-- Physical velocity, given by `SpatialCurl.spatialCurl (physicalPotential D h Qr I delta j)`. -/
noncomputable def physicalVelocity (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (j : ℤ) : VelocityField :=
  SpatialCurl.spatialCurl (physicalPotential D h Qr I delta j)

/-- The finite harmonic sum for a single original spatial label is one
actual Cartesian potential, rather than a collection of bandwise fields. -/
noncomputable def labelPotential (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (N : ℕ) : VelocityField :=
  fun z => ∑ j ∈ modes N, physicalPotential D h Qr I delta j z

/-- Label velocity, given by `SpatialCurl.spatialCurl (labelPotential D h Qr I delta N)`. -/
noncomputable def labelVelocity (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (N : ℕ) : VelocityField :=
  SpatialCurl.spatialCurl (labelPotential D h Qr I delta N)

theorem nativeMap_add_angle (h Q : ℝ) (i : ℕ) (z : SpaceTime) (s : ℝ) :
    nativeMap h Q i (z + s • (0, coordinateVector 1)) =
      nativeMap h Q i z + s • (((0 : Parameter), (1 : ℝ)), (0 : Plane)) := by
  ext <;> simp [nativeMap, waveEquiv_apply, PhysicalResidualBridge.ScaledGraph.map,
    coordinateVector, smul_eq_mul]

theorem physicalPhase_affine (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    AffinePhase ((0 : ℝ), coordinateVector 1)
      ((D.carrierBlock.angularFrequency D.reference.band : ℝ) /
        D.carrierBlock.frequency D.reference.band) (physicalPhase D h Qr I j) := by
  intro z s
  unfold physicalPhase referencePhase
  rw [nativeMap_add_angle]
  exact actualCarrier_affine D.background D.carrierBlock j D.reference.band (nativeMap h Qr I z) s

theorem physicalRaw_invariant (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    Invariant ((0 : ℝ), coordinateVector 1) (physicalRaw D h Qr I j) := by
  intro z s
  unfold physicalRaw
  rw [nativeMap_add_angle]
  congr 1
  exact angleLift_invariant (referenceVelocity D.reference D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j) (nativeMap h Qr I z) s

theorem angle_translate_pack (t r theta z s : ℝ) :
    (t, AxisymmetricResidual.pack r theta z) + s • ((0 : ℝ), coordinateVector 1) =
      (t, AxisymmetricResidual.pack r (theta + s) z) := by
  apply Prod.ext
  · simp
  · ext i
    fin_cases i <;> simp [coordinateVector]

theorem referencePotential_periodic (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ)
    (hk : D.carrierBlock.frequency D.reference.band ≠ 0) (t r z : ℝ) :
    Periodic (fun theta => referencePotential D h Qr I j
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
  intro theta
  have hR : Invariant ((0 : ℝ), coordinateVector 1) LinearWaveResidual.coordinateRadius := by
    intro x s
    simp [LinearWaveResidual.coordinateRadius, coordinateVector]
  have hf : referenceFrequency D j *
      ((D.carrierBlock.angularFrequency D.reference.band : ℝ) /
        D.carrierBlock.frequency D.reference.band) =
      ((j * D.carrierBlock.angularFrequency D.reference.band : ℤ) : ℝ) := by
    unfold referenceFrequency
    push_cast
    field_simp [hk]
  have he := PhysicalCurlCovariance.vectorPotential_fullTurn
    (Vr := LinearWaveResidual.spaceDirection 0)
    (Vθ := LinearWaveResidual.spaceDirection 1)
    (Vz := LinearWaveResidual.spaceDirection 2)
    (j * D.carrierBlock.angularFrequency D.reference.band) hR
    (Invariant.const _) (Invariant.const _) (Invariant.const _)
    (physicalPhase_affine D h Qr I j) (physicalRaw_invariant D h Qr I j) hf
    (t, AxisymmetricResidual.pack r theta z)
  simpa only [referencePotential, PhysicalCurlCovariance.referencePotential, angle_translate_pack]
      using he

/-- These are identities of the input chart at its own reference band. -/
structure ReferenceIdentity (D : AssemblyData Parameter) : Prop where
  parameter : D.charts.parameter D.reference.band = id
  gap : D.charts.gap D.reference.band = 0
  amplitude : D.charts.amplitude D.reference.band = 1

theorem referenceRaw_eq_common (D : AssemblyData Parameter) (H : ReferenceIdentity D) (j : ℤ) :
    referenceRaw D j = (rawCommon D j).amplitude D.reference.band := by
  have hs : residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j
      D.reference.band =
      transportSource (residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
          j D.reference.band)
        (D.charts.parameter D.reference.band) (D.charts.gap D.reference.band)
        (D.charts.amplitude D.reference.band) := by
    rw [H.parameter, H.gap, H.amplitude]
    funext p
    simp [transportSource, coverPower]
  funext x
  have he := actualBandVelocity_eq_reference D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.reference.band hs x.1.1 x.2
  rw [H.parameter, H.gap, H.amplitude] at he
  simp only [id_eq, coverPower, ContinuousLinearEquiv.refl_apply, one_smul] at he
  exact he.symm

/-- Literal input-operator matches at the reference chart. This record
contains no condition on a solved velocity, pressure, potential or curl. -/
structure ReferenceChart (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) : Prop where
  identity : ReferenceIdentity D
  radius : (fun x => D.background.radius D.reference.band (waveEquiv.toContinuousLinearEquiv x)) =
    PhysicalResidualBridge.ScaledGraph.radius
  radial : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (D.directions.radialField D.reference.band) = (PhysicalResidualBridge.commonGraph Qr h
          I).radial
  angular : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (fun _ => D.directions.angular) = PhysicalResidualBridge.ScaledGraph.angular
  axial : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (D.directions.axialField D.strip D.reference.band) = (PhysicalResidualBridge.commonGraph Qr h
          I).axial

/-- Reference domain, given by `waveEquiv ⁻¹' D.strip.domain`. -/
noncomputable def referenceDomain (D : AssemblyData Parameter) : Set Cylinder :=
  waveEquiv ⁻¹' D.strip.domain

theorem referenceDomain_open (D : AssemblyData Parameter) : IsOpen (referenceDomain D) :=
  D.strip.isOpen_domain.preimage waveEquiv.continuous

/-- Lift phase, defined pointwise by `referencePhase D j (waveEquiv x)`. -/
noncomputable def liftPhase (D : AssemblyData Parameter) (j : ℤ) : Cylinder → ℝ :=
  fun x => referencePhase D j (waveEquiv x)

/-- Lift raw, defined pointwise by `referenceRaw D j (waveEquiv x)`. -/
noncomputable def liftRaw (D : AssemblyData Parameter) (j : ℤ) : Cylinder → ComplexVector :=
  fun x => referenceRaw D j (waveEquiv x)

section ReferenceRealization

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ} (H : ReferenceChart D h Qr I)
  {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)

include H C

omit H in
theorem liftPhase_smooth : ContDiffOn ℝ ∞ (liftPhase D j) (referenceDomain D) :=
  (C.background.phase_smooth D.reference.band).comp waveEquiv.contDiff.contDiffOn (fun _ hx => hx)

theorem liftRaw_smooth : ContDiffOn ℝ ∞ (liftRaw D j) (referenceDomain D) := by
  unfold liftRaw
  rw [referenceRaw_eq_common D H.identity]
  exact (commonRaw_smooth D C D.reference.band).comp waveEquiv.contDiff.contDiffOn (fun _ hx => hx)

theorem liftNormal_eq {x : Cylinder} (hx : x ∈ referenceDomain D) :
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius (PhysicalResidualBridge.commonGraph Qr h
        I).radial
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualBridge.commonGraph Qr h I).axial
      (liftPhase D j) x =
      (rawCommon D j).normal D.strip D.directions D.reference.band (waveEquiv x) := by
  have hp := ((C.background.phase_smooth D.reference.band).contDiffAt
    (D.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he := PhysicalCurlCovariance.phaseNormal_reindex waveEquiv.toContinuousLinearEquiv
    (D.background.radius D.reference.band) (D.directions.radialField D.reference.band)
    (fun _ => D.directions.angular) (D.directions.axialField D.strip D.reference.band) hp
  rw [H.radius, H.radial, H.angular, H.axial] at he
  exact he

theorem liftNormal_ne {x : Cylinder} (hx : x ∈ referenceDomain D) :
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius (PhysicalResidualBridge.commonGraph Qr h
        I).radial
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualBridge.commonGraph Qr h I).axial
      (liftPhase D j) x ≠ 0 := by
  rw [liftNormal_eq D H C hx]
  exact C.normal_nonzero D.reference.band (waveEquiv x) hx

theorem liftRaw_tangent {x : Cylinder} (hx : x ∈ referenceDomain D) :
    normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Qr h I).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Qr h I).axial (liftPhase D j) x) (liftRaw D j x) = 0 := by
  rw [liftNormal_eq D H C hx]
  unfold liftRaw
  rw [referenceRaw_eq_common D H.identity]
  exact commonRaw_tangent D C D.reference.band hx

theorem reference_radius_ne {x : Cylinder} (hx : x ∈ referenceDomain D) : x.1.1 ≠ 0 := by
  have he : D.background.radius D.reference.band (waveEquiv x) = x.1.1 := congrFun H.radius x
  rw [← he]
  exact C.background.radius_ne D.reference.band (waveEquiv x) hx

theorem liftPotential_eq {x : Cylinder} (hx : x ∈ referenceDomain D) :
    CurlClassBounds.vectorPotential (referenceFrequency D j)
        PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Qr h I).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Qr h I).axial (liftPhase D j) (liftRaw D j) x =
      commonPotential D j D.reference.band (waveEquiv x) := by
  have hp := ((C.background.phase_smooth D.reference.band).contDiffAt
    (D.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he := PhysicalCurlCovariance.vectorPotential_reindex waveEquiv.toContinuousLinearEquiv
    (referenceFrequency D j) (D.background.radius D.reference.band)
    (D.directions.radialField D.reference.band) (fun _ => D.directions.angular)
    (D.directions.axialField D.strip D.reference.band)
    ((rawCommon D j).amplitude D.reference.band) hp
  rw [H.radius, H.radial, H.angular, H.axial] at he
  unfold liftRaw
  rw [referenceRaw_eq_common D H.identity]
  exact he

theorem referencePotential_eq_common (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : nativeMap h Qr I z ∈ D.strip.domain) :
    referencePotential D h Qr I j z =
      Qr ^ (-h) • commonPotential D j D.reference.band (nativeMap h Qr I z) := by
  have hK : referenceFrequency D j ≠ 0 := C.frequency_nonzero D.reference.band
  have hp := ((liftPhase_smooth D C).contDiffAt ((referenceDomain_open D).mem_nhds
      hx)).differentiableAt (by
      simp)
  have he := PhysicalCurlCovariance.commonGraph_vectorPotential_pull hQr h I hK hK hz hp (liftRaw D
      j)
  simp only [div_self hK, one_mul] at he
  change referencePotential D h Qr I j z = _ at he
  rw [liftPotential_eq D H C hx] at he
  exact he

theorem referencePotential_smoothAt (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : nativeMap h Qr I z ∈ D.strip.domain) :
    ContDiffAt ℝ ∞ (referencePotential D h Qr I j) z := by
  let G := PhysicalResidualBridge.commonGraph Qr h I
  have hm : ContDiffAt ℝ ∞ (nativeMap h Qr I) z :=
    waveEquiv.contDiff.contDiffAt.comp z (G.map_smoothAt (mul_pos (Real.rpow_pos_of_pos hQr _)
        hz).ne')
  have hs := (((commonPotential_smooth D C D.reference.band).contDiffAt
    (D.strip.isOpen_domain.mem_nhds hx)).comp z hm).const_smul (Qr ^ (-h))
  have hn : {y : SpaceTime | 0 < y.2 0} ∩ (nativeMap h Qr I) ⁻¹' D.strip.domain ∈ 𝓝 z :=
    inter_mem ((isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection
        0).continuous).mem_nhds hz)
      (hm.continuousAt (D.strip.isOpen_domain.mem_nhds hx))
  apply hs.congr_of_eventuallyEq
  exact eventually_of_mem hn (fun y hy => referencePotential_eq_common D H C hQr hy.1 hy.2)

theorem reference_physical_velocity (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : nativeMap h Qr I z ∈ D.strip.domain) {delta : ℝ} (hdelta : 0 < delta)
    (chart : PolarCharts.Index) (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart)
    (component : Fin 3) :
    (vectorMode ((D.wave j).frequency D.reference.band) ((D.wave j).phase D.reference.band)
      ((D.wave j).amplitude D.reference.band) (nativeMap h Qr I z) component).re =
      Qr ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
        (physicalVelocity D h Qr I delta j (z.1, CylindricalResidual.chart z.2)) component := by
  let G := PhysicalResidualBridge.commonGraph Qr h I
  let B : Cylinder → ComplexVector := fun x => commonPotential D j D.reference.band (waveEquiv x)
  have hP := referencePotential_smoothAt D H C hQr hz hx
  have hper := referencePotential_periodic D h Qr I j (C.frequency_ne D.reference.band)
  have hA := (PhysicalCurlCovariance.globalCartesianPotential_smoothAt_forward hdelta chart hper
      hchart hP).differentiableAt (by
      simp)
  have hB (i : Fin 3) : DifferentiableAt ℝ (fun x => B x i) (G.map z) := by
    exact (((contDiffOn_pi.mp (commonPotential_smooth D C D.reference.band)) i).contDiffAt
      (D.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by
          simp) |>.comp (G.map z) waveEquiv.differentiableAt
  have hvalue := PhysicalCurlCovariance.globalCartesianPotential_forward_germ hdelta chart
    (referencePotential D h Qr I j) hper hchart
  have hm : ContinuousAt (nativeMap h Qr I) z := waveEquiv.continuous.continuousAt.comp
    ((G.map_smoothAt (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne').continuousAt)
  have hrep : (fun y : SpaceTime => physicalPotential D h Qr I delta j
      (y.1, CylindricalResidual.chart y.2)) =ᶠ[𝓝 z]
      (fun y => CylindricalResidual.frame (y.2 1)
        (PhysicalCurlCovariance.ScaledGraph.realPotential G (Qr ^ (-h)) B y)) := by
    filter_upwards [hvalue,
      (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds
          hz,
      hm (D.strip.isOpen_domain.mem_nhds hx)] with y hv hyr hy
    unfold physicalPotential
    rw [hv, referencePotential_eq_common D H C hQr hyr hy]
    rfl
  have hc := PhysicalCurlCovariance.commonGraph_physical_curl hQr h I hz hB hA hrep component
  have he := PhysicalCurlCovariance.cylindricalCurl_reindex waveEquiv.toContinuousLinearEquiv
    (D.background.radius D.reference.band) (D.directions.radialField D.reference.band)
    (fun _ => D.directions.angular) (D.directions.axialField D.strip D.reference.band)
    (fun i => (((contDiffOn_pi.mp (commonPotential_smooth D C D.reference.band)) i).contDiffAt
      (D.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
  rw [H.radius, H.radial, H.angular, H.axial] at he
  change CurlClassBounds.cylindricalCurl PhysicalResidualBridge.ScaledGraph.radius G.radial
    PhysicalResidualBridge.ScaledGraph.angular G.axial B (G.map z) =
    CurlClassBounds.cylindricalCurl (D.background.radius D.reference.band)
      (D.directions.radialField D.reference.band) (fun _ => D.directions.angular)
      (D.directions.axialField D.strip D.reference.band)
      (commonPotential D j D.reference.band) (nativeMap h Qr I z) at he
  rw [commonPotential_curl D C D.reference.band hx] at he
  rw [he] at hc
  exact hc

end ReferenceRealization

/-! ## Actual solves with the rescaled native clock -/

/-- Parameter change, given by `(ratioPower Q Qr (1 / 2) * p.1, (ratioPower Q Qr 1 * p.2.1,
ratioPower Q Qr (CoordinateAlgebra.D h) * p.2.2))`. -/
noncomputable def parameterChange (h Q Qr : ℝ) (p : Parameter) : Parameter :=
  (ratioPower Q Qr (1 / 2) * p.1,
    (ratioPower Q Qr 1 * p.2.1, ratioPower Q Qr (CoordinateAlgebra.D h) * p.2.2))

theorem parameterChange_smooth (h Q Qr : ℝ) : ContDiff ℝ ∞ (parameterChange h Q Qr) :=
  (contDiff_const.mul contDiff_fst).prodMk
    ((contDiff_const.mul contDiff_snd.fst).prodMk (contDiff_const.mul contDiff_snd.snd))

theorem waveEquiv_cylinderChange (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    waveEquiv (cylinderChange h Q Qr gap x) =
      ((parameterChange h Q Qr (waveEquiv x).1.1, (waveEquiv x).1.2), coverPower gap (waveEquiv
          x).2) := rfl

/-- Reference source, given by `residualSource D.context D.state D.carrierBlock D.gaussianInput
D.aliasInput j D.reference.band`. -/
noncomputable def referenceSource (D : AssemblyData Parameter) (j : ℤ) : Parameter × Plane →
    ComplexVector :=
  residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j D.reference.band

/-- Band amplitude, constructed using `ParticularWaveBounds.commonVelocity`. -/
noncomputable def bandAmplitude (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) : Parameter × Plane → ComplexVector :=
  ParticularWaveBounds.commonVelocity
    (ScaledTangentTransport.transportTangent (D.reference.tangent j) (parameterChange h Q Qr) gap 0
      (clockWeight h Q Qr) (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)))
    (ScaledTangentTransport.transportSource (referenceSource D j) (parameterChange h Q Qr) gap
      (clockWeight h Q Qr) (velocityWeight h Q Qr))
    (CopySolveCompatibility.transportGeometry D.reference.geometry gap 0 (clockWeight h Q Qr)
      (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2)).ne')
    (div_pos D.reference.length_pos (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2))).le
    (D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 (clockWeight h Q Qr))

/-- Band pressure, constructed using `ParticularWaveBounds.commonPressure`. -/
noncomputable def bandPressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) : Parameter × Plane → ℂ :=
  ParticularWaveBounds.commonPressure
    (ScaledTangentTransport.transportTangent (D.reference.tangent j) (parameterChange h Q Qr) gap 0
      (clockWeight h Q Qr) (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)))
    (ScaledTangentTransport.transportSource (referenceSource D j) (parameterChange h Q Qr) gap
      (clockWeight h Q Qr) (velocityWeight h Q Qr))
    (CopySolveCompatibility.transportGeometry D.reference.geometry gap 0 (clockWeight h Q Qr)
      (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2)).ne')
    (div_pos D.reference.length_pos (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2))).le
    (D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 (clockWeight h Q Qr)) K

/-- Continuity of the actual primitive Volterra coefficients and source,
and support inside the reference integration interval. -/
structure ReferenceODE (D : AssemblyData Parameter) (j : ℤ) (U : Set Parameter) : Prop where
  coefficient : ContinuousOn (D.reference.tangent j).linearData.coefficient (U ×ˢ univ)
  forcing : ContinuousOn (D.reference.tangent j).linearData.forcingMap (U ×ˢ univ)
  source : ContinuousOn (referenceSource D j) (U ×ˢ univ)
  cutoff : support D.reference.cutoff ⊆ univ ×ˢ Icc 0 D.reference.length

theorem normalWeight_ne {Q Qr K Kr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) : normalWeight Q Qr K Kr ≠ 0 :=
  mul_ne_zero (div_ne_zero hKr hK) (ratioPower_pos hQ hQr (1 / 2)).ne'

theorem bandAmplitude_eq_reference (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    (p : Parameter) (hp : parameterChange h Q Qr p ∈ U) (Y : Plane) :
    bandAmplitude D h hQ hQr gap K j (p, Y) =
      velocityWeight h Q Qr • referenceVelocity D.reference D.context D.state D.carrierBlock
        D.gaussianInput D.aliasInput j (parameterChange h Q Qr p, coverPower gap Y) := by
  exact ScaledTangentTransport.commonVelocity_zeroEntry (D.reference.tangent j) (referenceSource D
      j)
    (parameterChange h Q Qr) D.reference.geometry gap D.reference.length (clockWeight h Q Qr)
    (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)) D.reference.length_pos
    (ratioPower_pos hQ hQr _) (normalWeight_ne hQ hQr hK hKr)
    R.coefficient R.forcing R.source D.reference.cutoff R.cutoff p hp Y

theorem bandPressure_eq_reference (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    (p : Parameter) (hp : parameterChange h Q Qr p ∈ U) (Y : Plane) :
    bandPressure D h hQ hQr gap K j (p, Y) =
      pressureWeight h Q Qr • ParticularWaveAssembly.referencePressure D.reference D.context
          D.state D.carrierBlock
        D.gaussianInput D.aliasInput j (parameterChange h Q Qr p, coverPower gap Y) := by
  have he := ScaledTangentTransport.commonPressure_zeroEntry (D.reference.tangent j)
      (referenceSource D j)
    (parameterChange h Q Qr) D.reference.geometry gap D.reference.length (clockWeight h Q Qr)
    (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)) (referenceFrequency D j)
        K
    D.reference.length_pos (ratioPower_pos hQ hQr _) (normalWeight_ne hQ hQr hK hKr) hKr hK
    R.coefficient R.forcing R.source D.reference.cutoff R.cutoff p hp Y
  rw [pressure_scaling hQ hQr hK hKr] at he
  exact he

/-- Band raw, defined pointwise by `bandAmplitude D h hQ hQr gap K j ((waveEquiv x).1.1,
(waveEquiv x).2)`. -/
noncomputable def bandRaw (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) : Cylinder → ComplexVector :=
  fun x => bandAmplitude D h hQ hQr gap K j ((waveEquiv x).1.1, (waveEquiv x).2)

/-- Band raw pressure, defined pointwise by `bandPressure D h hQ hQr gap K j ((waveEquiv x).1.1,
(waveEquiv x).2)`. -/
noncomputable def bandRawPressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) : Cylinder → ℂ :=
  fun x => bandPressure D h hQ hQr gap K j ((waveEquiv x).1.1, (waveEquiv x).2)

/-- Band phase, defined pointwise by `(referenceFrequency D j / K) * liftPhase D j
(cylinderChange h Q Qr gap x)`. -/
noncomputable def bandPhase (D : AssemblyData Parameter) (h Q Qr : ℝ) (gap : ℕ) (K : ℝ) (j : ℤ) :
    Cylinder → ℝ := fun x => (referenceFrequency D j / K) * liftPhase D j (cylinderChange h Q Qr
        gap x)

/-- Band velocity as an element of `Cylinder → ComplexVector`. -/
noncomputable def bandVelocity (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) (K : ℝ) (j : ℤ) : Cylinder → ComplexVector :=
  let G := PhysicalResidualBridge.commonGraph Q h i
  vectorMode K (bandPhase D h Q Qr gap K j)
    (CurlClassBounds.realizedCoefficient K PhysicalResidualBridge.ScaledGraph.radius
      G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial (bandPhase D h Q Qr gap K j)
      (bandRaw D h hQ hQr gap K j))

theorem bandRaw_eq_lift (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    (x : Cylinder) (hx : parameterChange h Q Qr (waveEquiv x).1.1 ∈ U) :
    bandRaw D h hQ hQr gap K j x =
      velocityWeight h Q Qr • liftRaw D j (cylinderChange h Q Qr gap x) := by
  exact bandAmplitude_eq_reference D h hQ hQr gap hK j hKr R (waveEquiv x).1.1 hx (waveEquiv x).2

/-- Band domain, given by `{x | 0 < x.1.1 ∧ cylinderChange h Q Qr gap x ∈ referenceDomain D ∧
parameterChange h Q Qr (waveEquiv x).1.1 ∈ U}`. -/
noncomputable def bandDomain (D : AssemblyData Parameter) (h Q Qr : ℝ) (gap : ℕ)
    (U : Set Parameter) : Set Cylinder :=
  {x | 0 < x.1.1 ∧ cylinderChange h Q Qr gap x ∈ referenceDomain D ∧
    parameterChange h Q Qr (waveEquiv x).1.1 ∈ U}

theorem bandDomain_open (D : AssemblyData Parameter) (h Q Qr : ℝ) (gap : ℕ)
    {U : Set Parameter} (hU : IsOpen U) : IsOpen (bandDomain D h Q Qr gap U) :=
  (isOpen_lt continuous_const continuous_fst.fst).inter
    (((referenceDomain_open D).preimage (cylinderChange h Q Qr gap).continuous).inter
      (hU.preimage ((parameterChange_smooth h Q Qr).continuous.comp waveEquiv.continuous.fst.fst)))

theorem normalDot_scaled (s c : ℝ) (n : Space) (a : ComplexVector) :
    normalDot (s • n) (c • a) = (s : ℂ) * (c : ℂ) * normalDot n a := by
  simp [normalDot, Complex.real_smul]
  ring

section BandRealization

variable (D : AssemblyData Parameter) {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
  (i gap : ℕ) (H : ReferenceChart D h Qr (i + gap)) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  {K : ℝ} (hK : K ≠ 0) {U : Set Parameter} (hU : IsOpen U) (R : ReferenceODE D j U)

include H C R hK hQ hQr

omit hQ hQr H hK R in
theorem bandPhase_smooth : ContDiffOn ℝ ∞ (bandPhase D h Q Qr gap K j) (bandDomain D h Q Qr gap U)
    :=
  contDiffOn_const.mul ((liftPhase_smooth D C).comp (s := bandDomain D h Q Qr gap U)
    (cylinderChange h Q Qr gap).contDiff.contDiffOn (fun _ hx => hx.2.1))

theorem bandRaw_smooth : ContDiffOn ℝ ∞ (bandRaw D h hQ hQr gap K j) (bandDomain D h Q Qr gap U) :=
    by
  have hs := ((liftRaw_smooth D H C).comp (cylinderChange h Q Qr gap).contDiff.contDiffOn
    (s := bandDomain D h Q Qr gap U) (fun _ hx => hx.2.1)).const_smul (velocityWeight h Q Qr)
  apply hs.congr
  intro x hx
  exact bandRaw_eq_lift D h hQ hQr gap hK j (C.frequency_nonzero D.reference.band) R x hx.2.2

omit R in
theorem bandNormal_ne {x : Cylinder} (hx : x ∈ bandDomain D h Q Qr gap U) :
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius (PhysicalResidualBridge.commonGraph Q h
        i).radial
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualBridge.commonGraph Q h i).axial
      (bandPhase D h Q Qr gap K j) x ≠ 0 := by
  have hp := ((liftPhase_smooth D C).contDiffAt ((referenceDomain_open D).mem_nhds
      hx.2.1)).differentiableAt (by
      simp)
  have he := phaseNormal_chartChange hQ hQr h i gap K (referenceFrequency D j) hx.1 hp
  change phaseNormal _ _ _ _ (bandPhase D h Q Qr gap K j) x = _ at he
  rw [he]
  exact smul_ne_zero (normalWeight_ne hQ hQr hK (C.frequency_nonzero D.reference.band))
    (liftNormal_ne D H C hx.2.1)

theorem bandRaw_tangent {x : Cylinder} (hx : x ∈ bandDomain D h Q Qr gap U) :
    normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial (bandPhase D h Q Qr gap K j) x)
      (bandRaw D h hQ hQr gap K j x) = 0 := by
  have hp := ((liftPhase_smooth D C).contDiffAt ((referenceDomain_open D).mem_nhds
      hx.2.1)).differentiableAt (by
      simp)
  have he := phaseNormal_chartChange hQ hQr h i gap K (referenceFrequency D j) hx.1 hp
  change phaseNormal _ _ _ _ (bandPhase D h Q Qr gap K j) x = _ at he
  rw [he, bandRaw_eq_lift D h hQ hQr gap hK j (C.frequency_nonzero D.reference.band) R x hx.2.2,
    normalDot_scaled, liftRaw_tangent D H C hx.2.1, mul_zero]

include hU

/-- Every actual transported solve is the view of the same Cartesian
reference curl. The clock, source, cutoff and normal are transported
before solving; no equality of solved velocities is a premise. -/
theorem band_physical_velocity {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph Q h i).source (bandDomain D h Q Qr gap U))
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (bandVelocity D h hQ hQr i gap K j ((PhysicalResidualBridge.commonGraph Q h i).map z)
        component).re =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
        (physicalVelocity D h Qr (i + gap) delta j (z.1, CylindricalResidual.chart z.2)) component
            := by
  have hKr : referenceFrequency D j ≠ 0 := C.frequency_nonzero D.reference.band
  have hphase : ∀ y ∈ (PhysicalResidualBridge.commonGraph Q h i).source (bandDomain D h Q Qr gap U),
      referenceFrequency D j * physicalPhase D h Qr (i + gap) j y =
        K * bandPhase D h Q Qr gap K j ((PhysicalResidualBridge.commonGraph Q h i).map y) := by
    intro y hy
    change referenceFrequency D j * liftPhase D j ((PhysicalResidualBridge.commonGraph Qr h (i +
        gap)).map y) =
      K * ((referenceFrequency D j / K) * liftPhase D j
        (cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map y)))
    rw [cylinderChange_graph hQ hQr h i gap hy.1]
    field_simp
  have hamp : ∀ y ∈ (PhysicalResidualBridge.commonGraph Q h i).source (bandDomain D h Q Qr gap U),
      physicalRaw D h Qr (i + gap) j y =
        Q ^ (-CoordinateAlgebra.A h) • bandRaw D h hQ hQr gap K j
          ((PhysicalResidualBridge.commonGraph Q h i).map y) := by
    intro y hy
    rw [bandRaw_eq_lift D h hQ hQr gap hK j hKr R _ hy.2.2.2,
      cylinderChange_graph hQ hQr h i gap hy.1, smul_smul]
    have hw : Q ^ (-CoordinateAlgebra.A h) * velocityWeight h Q Qr = Qr ^ (-CoordinateAlgebra.A h)
        := by
      rw [mul_comm]
      exact ratioPower_cancel hQ hQr _
    rw [hw]
    rfl
  exact PhysicalCurlCovariance.reference_correctedWave_constructed hQ h i
    (bandDomain_open D h Q Qr gap hU) (fun _ hx => hx.1.ne') hKr hK
    (bandPhase_smooth D gap C) (bandRaw_smooth D hQ hQr i gap H C hK R)
    (fun _ hx => bandNormal_ne D hQ hQr i gap H C hK hx)
    (fun _ hx => bandRaw_tangent D hQ hQr i gap H C hK R hx)
    (physicalPhase D h Qr (i + gap) j) (physicalRaw D h Qr (i + gap) j) hphase hamp
    (referencePotential_periodic D h Qr (i + gap) j (C.frequency_ne D.reference.band))
    hz hdelta chart hchart component

end BandRealization

/-! ## The pressure from the same reference solve -/

/-- Physical pressure coefficient, defined pointwise by `(Qr ^ (-(2 * CoordinateAlgebra.A h)) :
ℝ) • referenceRawPressure D j (nativeMap h Qr I z)`. -/
noncomputable def physicalPressureCoefficient (D : AssemblyData Parameter) (h Qr : ℝ)
    (I : ℕ) (j : ℤ) : SpaceTime → ℂ :=
  fun z => (Qr ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) • referenceRawPressure D j (nativeMap h Qr I z)

/-- Complex physical pressure, given by `mode (referenceFrequency D j) (physicalPhase D h Qr I
j) (physicalPressureCoefficient D h Qr I j)`. -/
noncomputable def complexPhysicalPressure (D : AssemblyData Parameter) (h Qr : ℝ)
    (I : ℕ) (j : ℤ) : SpaceTime → ℂ :=
  mode (referenceFrequency D j) (physicalPhase D h Qr I j) (physicalPressureCoefficient D h Qr I j)

/-- Pressure vector, given by `![0, 0, p z]`. -/
noncomputable def pressureVector (p : SpaceTime → ℂ) (z : SpaceTime) : ComplexVector := ![0, 0, p z]

/-- A scalar is the axial component of its Cartesian coordinate lift;
the frame fixes this component, so the construction has no extra rotation. -/
noncomputable def physicalPressure (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (j : ℤ) : PressureField :=
  fun z => PhysicalCurlCovariance.globalCartesianPotential delta
    (pressureVector (complexPhysicalPressure D h Qr I j)) z 2

/-- Band pressure mode, given by `mode K (bandPhase D h Q Qr gap K j) (bandRawPressure D h hQ
hQr gap K j)`. -/
noncomputable def bandPressureMode (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) : Cylinder → ℂ :=
  mode K (bandPhase D h Q Qr gap K j) (bandRawPressure D h hQ hQr gap K j)

theorem mode_fullTurn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {theta : E} {phi : E → ℝ} {a : E → ℂ} {K slope : ℝ} (m : ℤ)
    (hphi : AffinePhase theta slope phi) (ha : Invariant theta a)
    (hf : K * slope = (m : ℝ)) (x : E) :
    mode K phi a (x + (2 * Real.pi) • theta) = mode K phi a x := by
  have hc : (K : ℂ) * (slope : ℂ) = (m : ℂ) := by exact_mod_cast hf
  have he : phaseFactor K * ((slope * (2 * Real.pi) : ℝ) : ℂ) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold phaseFactor
    push_cast
    calc
      _ = ((K : ℂ) * (slope : ℂ)) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hc]
  rw [mode_translate ha hphi, he, Complex.exp_int_mul_two_pi_mul_I, one_mul]

theorem complexPhysicalPressure_periodic (D : AssemblyData Parameter) (h Qr : ℝ)
    (I : ℕ) (j : ℤ) (hk : D.carrierBlock.frequency D.reference.band ≠ 0) (t r z : ℝ) :
    Periodic (fun theta => complexPhysicalPressure D h Qr I j
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
  intro theta
  have hp : Invariant ((0 : ℝ), coordinateVector 1) (physicalPressureCoefficient D h Qr I j) := by
    intro x s
    unfold physicalPressureCoefficient
    rw [nativeMap_add_angle]
    congr 1
    exact angleLift_invariant (ParticularWaveAssembly.referencePressure D.reference D.context
        D.state
      D.carrierBlock D.gaussianInput D.aliasInput j) (nativeMap h Qr I x) s
  have hf : referenceFrequency D j *
      ((D.carrierBlock.angularFrequency D.reference.band : ℝ) / D.carrierBlock.frequency
          D.reference.band) =
      ((j * D.carrierBlock.angularFrequency D.reference.band : ℤ) : ℝ) := by
    unfold referenceFrequency
    push_cast
    field_simp [hk]
  have he := mode_fullTurn (j * D.carrierBlock.angularFrequency D.reference.band)
    (physicalPhase_affine D h Qr I j) hp hf (t, AxisymmetricResidual.pack r theta z)
  simpa only [complexPhysicalPressure, angle_translate_pack] using he

theorem physicalPressure_forward (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ)
    (hk : D.carrierBlock.frequency D.reference.band ≠ 0) {delta : ℝ} (hdelta : 0 < delta)
    (chart : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    physicalPressure D h Qr I delta j (z.1, CylindricalResidual.chart z.2) =
      (complexPhysicalPressure D h Qr I j z).re := by
  have hper (t r z : ℝ) : Periodic (fun theta => pressureVector (complexPhysicalPressure D h Qr I j)
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
    intro theta
    have hp := complexPhysicalPressure_periodic D h Qr I j hk t r z theta
    simp only [pressureVector, hp]
  have he := (PhysicalCurlCovariance.globalCartesianPotential_forward_germ hdelta chart
    (pressureVector (complexPhysicalPressure D h Qr I j)) hper hz).eq_of_nhds
  unfold physicalPressure
  rw [he]
  simp [CylindricalResidual.frame_apply, PhysicalCurlCovariance.realVector, pressureVector]

theorem bandRawPressure_eq_lift (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    (x : Cylinder) (hx : parameterChange h Q Qr (waveEquiv x).1.1 ∈ U) :
    bandRawPressure D h hQ hQr gap K j x =
      pressureWeight h Q Qr • referenceRawPressure D j (waveEquiv (cylinderChange h Q Qr gap x)) :=
          by
  exact bandPressure_eq_reference D h hQ hQr gap hK j hKr R (waveEquiv x).1.1 hx (waveEquiv x).2

theorem bandPressureMode_eq_physical (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h Q Qr (nativeMap h Q i z).1.1 ∈ U) :
    bandPressureMode D h hQ hQr gap K j ((PhysicalResidualBridge.commonGraph Q h i).map z) =
      (Q ^ (2 * CoordinateAlgebra.A h) : ℝ) • complexPhysicalPressure D h Qr (i + gap) j z := by
  have hraw := bandRawPressure_eq_lift D h hQ hQr gap hK j hKr R
    ((PhysicalResidualBridge.commonGraph Q h i).map z) hp
  rw [cylinderChange_graph hQ hQr h i gap hz] at hraw
  have hc : carrier K (bandPhase D h Q Qr gap K j) ((PhysicalResidualBridge.commonGraph Q h i).map
      z) =
      carrier (referenceFrequency D j) (physicalPhase D h Qr (i + gap) j) z := by
    apply PhysicalCurlCovariance.carrier_eq_of_products
    change K * ((referenceFrequency D j / K) * liftPhase D j
      (cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map z))) =
      referenceFrequency D j * liftPhase D j ((PhysicalResidualBridge.commonGraph Qr h (i +
          gap)).map z)
    rw [cylinderChange_graph hQ hQr h i gap hz]
    field_simp
  have hw : pressureWeight h Q Qr = Q ^ (2 * CoordinateAlgebra.A h) * Qr ^ (-(2 *
      CoordinateAlgebra.A h)) := by
    unfold pressureWeight ratioPower
    rw [Real.rpow_neg hQr.le, div_eq_mul_inv]
  unfold bandPressureMode complexPhysicalPressure HarmonicCalculus.mode
  rw [hraw, hc, hw]
  simp only [physicalPressureCoefficient, Complex.real_smul, Complex.ofReal_mul, nativeMap]
  ring

theorem band_physical_pressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) {K : ℝ} (hK : K ≠ 0) (j : ℤ)
    (hKr : referenceFrequency D j ≠ 0) {U : Set Parameter} (R : ReferenceODE D j U)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h Q Qr (nativeMap h Q i z).1.1 ∈ U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (bandPressureMode D h hQ hQr gap K j ((PhysicalResidualBridge.commonGraph Q h i).map z)).re =
      Q ^ (2 * CoordinateAlgebra.A h) *
        physicalPressure D h Qr (i + gap) delta j (z.1, CylindricalResidual.chart z.2) := by
  have hk : D.carrierBlock.frequency D.reference.band ≠ 0 := by
    intro hh
    apply hKr
    simp [referenceFrequency, hh]
  rw [bandPressureMode_eq_physical D h hQ hQr i gap hK j hKr R hz hp,
    physicalPressure_forward D h Qr (i + gap) j hk hdelta chart hchart]
  simp [Complex.real_smul]

/-! ## Finite harmonic assembly uses one potential -/

/-- Label band velocity, given by `∑ j ∈ modes N, (bandVelocity D h hQ hQr i gap (frequency j) j
x component).re`. -/
noncomputable def labelBandVelocity (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) (frequency : ℤ → ℝ) (N : ℕ)
    (x : Cylinder) (component : Fin 3) : ℝ :=
  ∑ j ∈ modes N, (bandVelocity D h hQ hQr i gap (frequency j) j x component).re

/-- Label band pressure, given by `∑ j ∈ modes N, (bandPressureMode D h hQ hQr gap (frequency j)
j x).re`. -/
noncomputable def labelBandPressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (frequency : ℤ → ℝ) (N : ℕ)
    (x : Cylinder) : ℝ := ∑ j ∈ modes N, (bandPressureMode D h hQ hQr gap (frequency j) j x).re

/-- Label pressure, defined pointwise by `∑ j ∈ modes N, physicalPressure D h Qr I delta j z`. -/
noncomputable def labelPressure (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ)
    (delta : ℝ) (N : ℕ) : PressureField :=
  fun z => ∑ j ∈ modes N, physicalPressure D h Qr I delta j z

theorem spatialCurl_finset_sum {ι : Type} (S : Finset ι) (A : ι → VelocityField)
    {z : SpaceTime} (hA : ∀ i ∈ S, DifferentiableAt ℝ (A i) z) :
    SpatialCurl.spatialCurl (fun w => ∑ i ∈ S, A i w) z =
      ∑ i ∈ S, SpatialCurl.spatialCurl (A i) z := by
  have hs : ∀ i ∈ S, DifferentiableAt ℝ (fun y : Space => A i (z.1, y)) z.2 :=
    fun i hi => (hA i hi).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  change SpatialCurl.curl (fun y : Space => ∑ i ∈ S, A i (z.1, y)) z.2 =
    ∑ i ∈ S, SpatialCurl.curl (fun y : Space => A i (z.1, y)) z.2
  simp only [SpatialCurl.curl, fderiv_fun_sum hs, map_sum]

theorem label_physical_velocity (D : AssemblyData Parameter) {h Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) (H : ReferenceChart D h Qr (i + gap))
    {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) (frequency : ℤ → ℝ)
    (hfrequency : ∀ j ∈ modes N, frequency j ≠ 0) {U : Set Parameter} (hU : IsOpen U)
    (R : ∀ j ∈ modes N, ReferenceODE D j U) {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph Q h i).source (bandDomain D h Q Qr gap U))
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    labelBandVelocity D h hQ hQr i gap frequency N ((PhysicalResidualBridge.commonGraph Q h i).map
        z) component =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
        (labelVelocity D h Qr (i + gap) delta N (z.1, CylindricalResidual.chart z.2)) component :=
            by
  have href : nativeMap h Qr (i + gap) z ∈ D.strip.domain := by
    have hx := hz.2.2.1
    rw [cylinderChange_graph hQ hQr h i gap hz.1] at hx
    exact hx
  have hA (j : ℤ) (hj : j ∈ modes N) :
      DifferentiableAt ℝ (physicalPotential D h Qr (i + gap) delta j) (z.1,
          CylindricalResidual.chart z.2) :=
    (PhysicalCurlCovariance.globalCartesianPotential_smoothAt_forward hdelta chart
      (referencePotential_periodic D h Qr (i + gap) j ((C j hj).frequency_ne D.reference.band))
          hchart
      (referencePotential_smoothAt D H (C j hj) hQr hz.1 href)).differentiableAt (by simp)
  have hsum := spatialCurl_finset_sum (modes N)
    (fun j => physicalPotential D h Qr (i + gap) delta j) hA
  unfold labelVelocity labelPotential labelBandVelocity
  rw [hsum]
  have hframe : CylindricalResidual.frame (-(z.2 1))
      (∑ j ∈ modes N, SpatialCurl.spatialCurl (physicalPotential D h Qr (i + gap) delta j)
        (z.1, CylindricalResidual.chart z.2)) component =
      ∑ j ∈ modes N, CylindricalResidual.frame (-(z.2 1))
        (SpatialCurl.spatialCurl (physicalPotential D h Qr (i + gap) delta j)
          (z.1, CylindricalResidual.chart z.2)) component :=
    map_sum ((AxisymmetricFields.projection component).comp (CylindricalResidual.frame (-(z.2 1))))
        _ _
  rw [hframe, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact band_physical_velocity D hQ hQr i gap H (C j hj) (hfrequency j hj) hU (R j hj) hz hdelta
      chart hchart component

theorem label_physical_pressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i gap : ℕ) {N : ℕ} (frequency : ℤ → ℝ)
    (hfrequency : ∀ j ∈ modes N, frequency j ≠ 0)
    (hreference : ∀ j ∈ modes N, referenceFrequency D j ≠ 0) {U : Set Parameter}
    (R : ∀ j ∈ modes N, ReferenceODE D j U) {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h Q Qr (nativeMap h Q i z).1.1 ∈ U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    labelBandPressure D h hQ hQr gap frequency N ((PhysicalResidualBridge.commonGraph Q h i).map z)
        =
      Q ^ (2 * CoordinateAlgebra.A h) *
        labelPressure D h Qr (i + gap) delta N (z.1, CylindricalResidual.chart z.2) := by
  unfold labelBandPressure labelPressure
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact band_physical_pressure D h hQ hQr i gap (hfrequency j hj) j (hreference j hj)
    (R j hj) hz hp hdelta chart hchart

/-! ## Axis preservation follows from vanishing of the actual source -/

theorem referenceVelocity_zero_of_source (D : AssemblyData Parameter) (j : ℤ) (p : Parameter)
    (hf : ∀ Y : Plane, referenceSource D j (p, Y) = 0) (Y : Plane) :
    referenceVelocity D.reference D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j
        (p, Y) = 0 := by
  unfold referenceVelocity ParticularWaveBounds.commonVelocity periodizedCopies
  trans ∑' _ : Frequency, (0 : ComplexVector)
  · apply tsum_congr
    intro copy
    change D.reference.cutoff (D.reference.geometry.coordinates copy Y) •
      complexCopyVelocity (D.reference.tangent j) (referenceSource D j)
        D.reference.geometry D.reference.length_pos.le copy (p, Y) = 0
    rw [complexCopyVelocity_zero_of_path (D.reference.tangent j) (referenceSource D j)
      D.reference.geometry D.reference.length_pos.le copy p Y (fun v hv => hf _), smul_zero]
  · exact tsum_zero

theorem referencePotential_zero_of_source (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ)
    (hQr : 0 < Qr) {delta : ℝ}
    (hf : ∀ p : Parameter, p.1 ≤ Qr ^ (-(1 / 2 : ℝ)) * delta →
      ∀ Y : Plane, referenceSource D j (p, Y) = 0)
    (z : SpaceTime) (hz : z.2 0 ≤ delta) : referencePotential D h Qr I j z = 0 := by
  have hp : (nativeMap h Qr I z).1.1.1 ≤ Qr ^ (-(1 / 2 : ℝ)) * delta := by
    change Qr ^ (-(1 / 2 : ℝ)) * z.2 0 ≤ Qr ^ (-(1 / 2 : ℝ)) * delta
    exact mul_le_mul_of_nonneg_left hz (Real.rpow_pos_of_pos hQr _).le
  have ha : physicalRaw D h Qr I j z = 0 := by
    change Qr ^ (-CoordinateAlgebra.A h) • referenceVelocity D.reference D.context D.state
      D.carrierBlock D.gaussianInput D.aliasInput j ((nativeMap h Qr I z).1.1, (nativeMap h Qr I
          z).2) = 0
    rw [referenceVelocity_zero_of_source D j _ (hf _ hp), smul_zero]
  ext component
  simp [referencePotential, PhysicalCurlCovariance.referencePotential,
      CurlClassBounds.vectorPotential,
    HarmonicCalculus.vectorMode, HarmonicCalculus.mode, CurlClassBounds.coefficient,
    CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross, ha]

theorem physicalVelocity_axis_zero_of_source (D : AssemblyData Parameter) (h Qr : ℝ)
    (I : ℕ) (j : ℤ) (hQr : 0 < Qr) {delta : ℝ} (hdelta : 0 < delta)
    (hf : ∀ p : Parameter, p.1 ≤ Qr ^ (-(1 / 2 : ℝ)) * delta →
      ∀ Y : Plane, referenceSource D j (p, Y) = 0)
    (t : ℝ) (x : Space) (hx₀ : x 0 = 0) (hx₁ : x 1 = 0) :
    physicalVelocity D h Qr I delta j (t, x) = 0 :=
  PhysicalCurlCovariance.cartesianVelocity_axis_zero hdelta
    (referencePotential_zero_of_source D h Qr I j hQr hf) t x hx₀ hx₁

/-- All allowed covering indices refer to one fixed reference cover.
In particular `i` may be a native index or a common refinement. -/
theorem label_velocity_on_cover (D : AssemblyData Parameter) {h Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i I : ℕ) (hi : i ≤ I) (H : ReferenceChart D h Qr I)
    {N : ℕ} {α κ : ℝ} (C : D.controls N α κ) (frequency : ℤ → ℝ)
    (hfrequency : ∀ j ∈ modes N, frequency j ≠ 0) {U : Set Parameter} (hU : IsOpen U)
    (R : ∀ j ∈ modes N, ReferenceODE D j U) {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph Q h i).source (bandDomain D h Q Qr (I - i) U))
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    labelBandVelocity D h hQ hQr i (I - i) frequency N
      ((PhysicalResidualBridge.commonGraph Q h i).map z) component =
      Q ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
        (labelVelocity D h Qr I delta N (z.1, CylindricalResidual.chart z.2)) component := by
  have hcover : i + (I - i) = I := by omega
  have H' : ReferenceChart D h Qr (i + (I - i)) := by simpa only [hcover] using H
  simpa only [hcover] using label_physical_velocity D hQ hQr i (I - i) H' C frequency hfrequency hU
      R
    hz hdelta chart hchart component

theorem label_pressure_on_cover (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (i I : ℕ) (hi : i ≤ I) {N : ℕ} (frequency : ℤ → ℝ)
    (hfrequency : ∀ j ∈ modes N, frequency j ≠ 0)
    (hreference : ∀ j ∈ modes N, referenceFrequency D j ≠ 0) {U : Set Parameter}
    (R : ∀ j ∈ modes N, ReferenceODE D j U) {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h Q Qr (nativeMap h Q i z).1.1 ∈ U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    labelBandPressure D h hQ hQr (I - i) frequency N ((PhysicalResidualBridge.commonGraph Q h
        i).map z) =
      Q ^ (2 * CoordinateAlgebra.A h) *
        labelPressure D h Qr I delta N (z.1, CylindricalResidual.chart z.2) := by
  have hcover : i + (I - i) = I := by omega
  simpa only [hcover] using label_physical_pressure D h hQ hQr i (I - i) frequency hfrequency
      hreference R
    hz hp hdelta chart hchart

/-! ## Regularity of the constructed physical fields -/

theorem referenceRawPressure_eq_common (D : AssemblyData Parameter) (H : ReferenceIdentity D)
    {j : ℤ} (hj : j ≠ 0) (hfrequency : ∀ n, D.carrierBlock.frequency n ≠ 0) :
    referenceRawPressure D j = (rawCommon D j).pressure D.reference.band := by
  have hs : residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j
      D.reference.band =
      transportSource (residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
          j D.reference.band)
        (D.charts.parameter D.reference.band) (D.charts.gap D.reference.band)
        (D.charts.amplitude D.reference.band) := by
    rw [H.parameter, H.gap, H.amplitude]
    funext p
    simp [transportSource, coverPower]
  funext x
  have he := actualBandPressure_eq_reference D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput hj D.reference.band hfrequency hs x.1.1 x.2
  rw [H.parameter, H.gap, H.amplitude] at he
  simp only [id_eq, coverPower, ContinuousLinearEquiv.refl_apply, one_mul,
    div_self (hfrequency D.reference.band), one_smul] at he
  exact he.symm

section PhysicalRegularity

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ} (H : ReferenceChart D h Qr I)
  {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
  (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart)

include H C hQr hz hx hdelta hchart

theorem physicalPotential_smoothAt : ContDiffAt ℝ ∞ (physicalPotential D h Qr I delta j)
    (z.1, CylindricalResidual.chart z.2) :=
  PhysicalCurlCovariance.globalCartesianPotential_smoothAt_forward hdelta chart
    (referencePotential_periodic D h Qr I j (C.frequency_ne D.reference.band)) hchart
    (referencePotential_smoothAt D H C hQr hz hx)

theorem physicalVelocity_smoothAt : ContDiffAt ℝ ∞ (physicalVelocity D h Qr I delta j)
    (z.1, CylindricalResidual.chart z.2) :=
  SpatialCurl.contDiffAt_spatialCurl (physicalPotential_smoothAt D H C hQr hz hx hdelta chart
      hchart) (by
      simp)

omit hdelta hchart in
theorem complexPhysicalPressure_smoothAt : ContDiffAt ℝ ∞ (complexPhysicalPressure D h Qr I j) z :=
    by
  let G := PhysicalResidualBridge.commonGraph Qr h I
  have hm : ContDiffAt ℝ ∞ (nativeMap h Qr I) z := waveEquiv.contDiff.contDiffAt.comp z
    (G.map_smoothAt (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne')
  have hpref : ContDiffAt ℝ ∞ (referenceRawPressure D j) (nativeMap h Qr I z) := by
    rw [referenceRawPressure_eq_common D H.identity C.harmonic_ne C.frequency_ne]
    exact (C.common_classes.2.smooth D.reference.band).contDiffAt (D.strip.isOpen_domain.mem_nhds
        hx)
  have hp : ContDiffAt ℝ ∞ (physicalPressureCoefficient D h Qr I j) z :=
    (hpref.comp z hm).const_smul (Qr ^ (-(2 * CoordinateAlgebra.A h)))
  have hphi : ContDiffAt ℝ ∞ (physicalPhase D h Qr I j) z :=
    ((C.background.phase_smooth D.reference.band).contDiffAt (D.strip.isOpen_domain.mem_nhds
        hx)).comp z hm
  exact hp.mul ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffAt z hphi)).cexp)

theorem physicalPressure_smoothAt : ContDiffAt ℝ ∞ (physicalPressure D h Qr I delta j)
    (z.1, CylindricalResidual.chart z.2) := by
  have hv : ContDiffAt ℝ ∞ (pressureVector (complexPhysicalPressure D h Qr I j)) z := by
    apply contDiffAt_pi.mpr
    intro component
    fin_cases component
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact complexPhysicalPressure_smoothAt D H C hQr hz hx
  have hper (t r z : ℝ) : Periodic (fun theta => pressureVector (complexPhysicalPressure D h Qr I j)
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
    intro theta
    simp only [pressureVector, complexPhysicalPressure_periodic D h Qr I j
      (C.frequency_ne D.reference.band) t r z theta]
  exact (AxisymmetricFields.projection 2).contDiff.comp_contDiffAt _
    (PhysicalCurlCovariance.globalCartesianPotential_smoothAt_forward hdelta chart hper hchart hv)

end PhysicalRegularity

theorem labelPotential_smoothAt (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
    (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    ContDiffAt ℝ ∞ (labelPotential D h Qr I delta N) (z.1, CylindricalResidual.chart z.2) := by
  apply ContDiffAt.sum
  intro j hj
  exact physicalPotential_smoothAt D H (C j hj) hQr hz hx hdelta chart hchart

theorem labelVelocity_smoothAt (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
    (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    ContDiffAt ℝ ∞ (labelVelocity D h Qr I delta N) (z.1, CylindricalResidual.chart z.2) :=
  SpatialCurl.contDiffAt_spatialCurl (labelPotential_smoothAt D H C hQr hz hx hdelta chart hchart)
      (by
      simp)

theorem labelPressure_smoothAt (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
    (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    ContDiffAt ℝ ∞ (labelPressure D h Qr I delta N) (z.1, CylindricalResidual.chart z.2) := by
  apply ContDiffAt.sum
  intro j hj
  exact physicalPressure_smoothAt D H (C j hj) hQr hz hx hdelta chart hchart

theorem labelVelocity_divergence (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
    (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    spatialDivergence (labelVelocity D h Qr I delta N) z.1 (CylindricalResidual.chart z.2) = 0 := by
  have hs := (labelPotential_smoothAt D H C hQr hz hx hdelta chart hchart).comp
    (CylindricalResidual.chart z.2) (contDiffAt_const.prodMk contDiffAt_id)
  exact SpatialCurl.spatialDivergence_spatialCurl _ _ _
    (hs.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)

/-! ## Substitution of the actual target-band residual source -/

/-- Transported residual source, constructed using `ScaledTangentTransport.transportSource`. -/
noncomputable def transportedResidualSource (D : AssemblyData Parameter) (h Q Qr : ℝ)
    (gap : ℕ) (j : ℤ) : Parameter × Plane → ComplexVector :=
  ScaledTangentTransport.transportSource (referenceSource D j) (parameterChange h Q Qr) gap
    (clockWeight h Q Qr) (velocityWeight h Q Qr)

/-- Residual band amplitude, constructed using `ParticularWaveBounds.commonVelocity`. -/
noncomputable def residualBandAmplitude (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) (n : ℕ) :
    Parameter × Plane → ComplexVector :=
  ParticularWaveBounds.commonVelocity
    (ScaledTangentTransport.transportTangent (D.reference.tangent j) (parameterChange h Q Qr) gap 0
      (clockWeight h Q Qr) (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)))
    (residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j n)
    (CopySolveCompatibility.transportGeometry D.reference.geometry gap 0 (clockWeight h Q Qr)
      (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2)).ne')
    (div_pos D.reference.length_pos (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2))).le
    (D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 (clockWeight h Q Qr))

/-- Residual band pressure, constructed using `ParticularWaveBounds.commonPressure`. -/
noncomputable def residualBandPressure (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) (n : ℕ) :
    Parameter × Plane → ℂ :=
  ParticularWaveBounds.commonPressure
    (ScaledTangentTransport.transportTangent (D.reference.tangent j) (parameterChange h Q Qr) gap 0
      (clockWeight h Q Qr) (velocityWeight h Q Qr) (normalWeight Q Qr K (referenceFrequency D j)))
    (residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j n)
    (CopySolveCompatibility.transportGeometry D.reference.geometry gap 0 (clockWeight h Q Qr)
      (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2)).ne')
    (div_pos D.reference.length_pos (ratioPower_pos hQ hQr (CoordinateAlgebra.A h + 1 / 2))).le
    (D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 (clockWeight h Q Qr)) K

theorem residualBandAmplitude_eq (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) (n : ℕ)
    (hsource : residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j n =
      transportedResidualSource D h Q Qr gap j) :
    residualBandAmplitude D h hQ hQr gap K j n = bandAmplitude D h hQ hQr gap K j := by
  unfold residualBandAmplitude bandAmplitude
  rw [hsource]
  rfl

theorem residualBandPressure_eq (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (K : ℝ) (j : ℤ) (n : ℕ)
    (hsource : residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j n =
      transportedResidualSource D h Q Qr gap j) :
    residualBandPressure D h hQ hQr gap K j n = bandPressure D h hQ hQr gap K j := by
  unfold residualBandPressure bandPressure
  rw [hsource]
  rfl

theorem transportedResidualSource_apply (D : AssemblyData Parameter) (h : ℝ) {Q Qr : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (gap : ℕ) (j : ℤ) (x : Parameter × Plane) :
    transportedResidualSource D h Q Qr gap j x =
      sourceWeight h Q Qr • referenceSource D j (parameterChange h Q Qr x.1, coverPower gap x.2) :=
          by
  unfold transportedResidualSource ScaledTangentTransport.transportSource
  rw [clock_mul_velocity hQ hQr]

/-- Equality with the target block's literal carrier follows from the
primitive unmodulated phase identity and its shared integer angular label. -/
theorem bandPhase_eq_actualCarrier (D : AssemblyData Parameter) (h Q Qr : ℝ)
    (gap n : ℕ) (j : ℤ) (hj : j ≠ 0) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hphase : ∀ p Y, D.carrierBlock.frequency n * D.carrierBlock.phase n (p, Y) =
      D.carrierBlock.frequency D.reference.band * D.carrierBlock.phase D.reference.band
        (parameterChange h Q Qr p, coverPower gap Y))
    (hangular : D.carrierBlock.angularFrequency n = D.carrierBlock.angularFrequency
        D.reference.band) :
    bandPhase D h Q Qr gap ((j : ℝ) * D.carrierBlock.frequency n) j =
      fun x => (actualCarrier D.background D.carrierBlock j).phase n (waveEquiv x) := by
  funext x
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj) (hfrequency n)
  apply mul_left_cancel₀ hK
  have hn := actualCarrier_phase D.background D.carrierBlock j hfrequency n
    ((waveEquiv x).1.1, (waveEquiv x).2) (waveEquiv x).1.2
  have hr := actualCarrier_phase D.background D.carrierBlock j hfrequency D.reference.band
    (parameterChange h Q Qr (waveEquiv x).1.1, coverPower gap (waveEquiv x).2) (waveEquiv x).1.2
  change ((j : ℝ) * D.carrierBlock.frequency n) *
    (actualCarrier D.background D.carrierBlock j).phase n (waveEquiv x) = _ at hn
  change referenceFrequency D j * liftPhase D j (cylinderChange h Q Qr gap x) = _ at hr
  rw [hphase, hangular] at hn
  unfold bandPhase
  calc
    _ = referenceFrequency D j * liftPhase D j (cylinderChange h Q Qr gap x) := by
      field_simp [hfrequency n]
    _ = _ := hr.trans hn.symm

end
end NavierStokes.PhysicalParticularWave
