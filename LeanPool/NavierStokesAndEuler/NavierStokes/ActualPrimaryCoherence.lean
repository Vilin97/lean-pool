/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeStateCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalStateCoherence

/-!
# Coherence of the constructed primary waves

The phase, coefficient, cutoff, and chart in this file are the actual
`CorrectionInitialization.ActualPrimary` constructors.  Their differentiated
curl correction and Gaussian term are transported on the whole free lift.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualPrimaryCoherence

open Set Function Filter HarmonicCalculus
open scoped Topology ContDiff InnerProductSpace

open CorrectionInitialization
open CorrectionInitialization.ActualPrimary

section ExactCalculus

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An invertible chart transports the actual derivative, including at
points where Lean's derivative is defined to be zero. -/
theorem phaseNormal_equiv (e : E ≃L[ℝ] F) {l : ℝ} (hl : l ≠ 0)
    (r : E → ℝ) (R : F → ℝ) (Sr St Sz : E → E) (Vr Vt Vz : F → F)
    (hr : ∀ x, R (e x) = l * r x)
    (hDr : ∀ x, e (Sr x) = l • Vr (e x))
    (hDt : ∀ x, e (St x) = Vt (e x))
    (hDz : ∀ x, e (Sz x) = l • Vz (e x)) (b : ℝ) (Φ : F → ℝ) (x : E) :
    phaseNormal r Sr St Sz (fun y => b * Φ (e y)) x =
      (b*l) • phaseNormal R Vr Vt Vz Φ (e x) := by
  have hd1 := PhysicalResidualNaturality.along_pull e b l Sr Vr Φ x (hDr x)
  have hd2 := PhysicalResidualNaturality.along_pull e b 1 St Vt Φ x (by simpa using hDt x)
  have hd3 := PhysicalResidualNaturality.along_pull e b l Sz Vz Φ x (hDz x)
  simp only [smul_eq_mul, mul_one] at hd1 hd2 hd3
  have hcancel (z : ℝ) : l * (b * (l⁻¹ * z)) = b*z := by
    rw [mul_left_comm l b, mul_inv_cancel_left₀ hl]
  ext i
  fin_cases i <;> simp [phaseNormal, hd1, hd2, hd3,
    smul_eq_mul, hr, div_eq_mul_inv, mul_inv_rev]
  ring_nf
  simp only [mul_left_comm, mul_comm]
  simp only [hcancel]

theorem cylindricalCurl_equiv (e : E ≃L[ℝ] F) {l : ℝ} (hl : l ≠ 0)
    (r : E → ℝ) (R : F → ℝ) (Sr St Sz : E → E) (Vr Vt Vz : F → F)
    (hr : ∀ x, R (e x) = l * r x)
    (hDr : ∀ x, e (Sr x) = l • Vr (e x))
    (hDt : ∀ x, e (St x) = Vt (e x))
    (hDz : ∀ x, e (Sz x) = l • Vz (e x)) (c : ℝ) (a : F → ComplexVector) (x : E) :
    CurlClassBounds.cylindricalCurl r Sr St Sz (fun y => c • a (e y)) x =
      (c*l) • CurlClassBounds.cylindricalCurl R Vr Vt Vz a (e x) := by
  have hd1 i := PhysicalResidualNaturality.along_pull e c l Sr Vr (fun y => a y i) x (hDr x)
  have hd2 i := PhysicalResidualNaturality.along_pull e c 1 St Vt (fun y => a y i) x (by
      simpa using hDt x)
  have hd3 i := PhysicalResidualNaturality.along_pull e c l Sz Vz (fun y => a y i) x (hDz x)
  have hc : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  simp only [Complex.real_smul, mul_one, Complex.ofReal_mul] at hd1 hd2 hd3
  have hcancel (z : ℂ) : (l:ℂ) * ((c:ℂ) * ((l:ℂ)⁻¹ * z)) = (c:ℂ)*z := by
    rw [mul_left_comm (l:ℂ) (c:ℂ), mul_inv_cancel_left₀ hc]
  ext i
  fin_cases i <;> simp [CurlClassBounds.cylindricalCurl, Pi.smul_apply,
    hd1, hd2, hd3, Complex.real_smul,
    hr, Complex.ofReal_mul, mul_inv_rev] <;> ring_nf <;>
    simp [mul_assoc, mul_comm, hc]

theorem realizedCoefficient_equiv (e : E ≃L[ℝ] F) {l b K L : ℝ}
    (hl : l ≠ 0) (hb : b ≠ 0) (hK : K ≠ 0) (hKL : K * b = L)
    (r : E → ℝ) (R : F → ℝ) (Sr St Sz : E → E) (Vr Vt Vz : F → F)
    (hr : ∀ x, R (e x) = l * r x)
    (hDr : ∀ x, e (Sr x) = l • Vr (e x))
    (hDt : ∀ x, e (St x) = Vt (e x))
    (hDz : ∀ x, e (Sz x) = l • Vz (e x)) (c : ℝ)
    (Φ : F → ℝ) (a : F → ComplexVector) (x : E) :
    CurlClassBounds.realizedCoefficient K r Sr St Sz
      (fun y => b * Φ (e y)) (fun y => c • a (e y)) x =
      c • CurlClassBounds.realizedCoefficient L R Vr Vt Vz Φ a (e x) := by
  have hcoef : CurlClassBounds.coefficient r Sr St Sz
      (fun y => b * Φ (e y)) (fun y => c • a (e y)) =
      fun y => (c/(b*l)) • CurlClassBounds.coefficient R Vr Vt Vz Φ a (e y) := by
    funext y
    unfold CurlClassBounds.coefficient
    rw [phaseNormal_equiv e hl r R Sr St Sz Vr Vt Vz hr hDr hDt hDz]
    exact PhysicalCurlCovariance.normalCoefficient_scale _ _ (mul_ne_zero hb hl) c
  rw [CurlClassBounds.realizedCoefficient, hcoef, CurlClassBounds.curlRemainder,
    cylindricalCurl_equiv e hl r R Sr St Sz Vr Vt Vz hr hDr hDt hDz]
  have hs : (1/K) * (c/(b*l)*l) = c * (1/L) := by
    rw [← hKL]
    field_simp
  simp only [CurlClassBounds.realizedCoefficient, CurlClassBounds.curlRemainder,
    smul_add, smul_comm Complex.I, smul_smul, hs]

end ExactCalculus

/-! ## The literal absolute chart and its directions -/

/-- Chart point: an abbreviation for `LocalSignedRequest.Point × ℝ`. -/
abbrev ChartPoint := LocalSignedRequest.Point × ℝ
/-- Absolute: an abbreviation for `AbsolutePoint × ℝ`. -/
abbrev Absolute := AbsolutePoint × ℝ

/-- Absolute chart, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required
compatibility proofs. -/
noncomputable def absoluteChart (n : ℕ) : ChartPoint ≃L[ℝ] Absolute where
  toFun x := (toAbsolute n x.1, x.2)
  invFun x := (fromAbsolute n x.1, x.2)
  left_inv x := Prod.ext (fromAbsolute_toAbsolute n x.1) rfl
  right_inv x := Prod.ext (toAbsolute_fromAbsolute n x.1) rfl
  map_add' x y := by ext <;> simp [toAbsolute, mul_add]
  map_smul' c x := by ext <;> simp [toAbsolute, mul_assoc, mul_comm]
  continuous_toFun := ((toAbsolute_smooth n).continuous.comp continuous_fst).prodMk continuous_snd
  continuous_invFun := ((fromAbsolute_smooth n).continuous.comp continuous_fst).prodMk
      continuous_snd

@[simp] theorem absoluteChart_apply (n : ℕ) (x : ChartPoint) :
    absoluteChart n x = (toAbsolute n x.1, x.2) := rfl

@[simp] theorem absoluteChart_symm_apply (n : ℕ) (x : Absolute) :
    (absoluteChart n).symm x = (fromAbsolute n x.1, x.2) := rfl

/-- Absolute radius, given by `x.1.1.1`. -/
noncomputable def absoluteRadius (x : Absolute) : ℝ := x.1.1.1

/-- Absolute radial, given by `(((1,(0,0)), RadialPullback.radialJacobian
(ChartScales.radialExponent h) x.1.1.1 • radialVector), 0)`. -/
noncomputable def absoluteRadial (x : Absolute) : Absolute :=
  (((1,(0,0)), RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1.1.1 •
      radialVector), 0)

/-- Absolute axial, given by `(((0,(1,0)),0),0)`. -/
noncomputable def absoluteAxial (_ : Absolute) : Absolute := (((0,(1,0)),0),0)
/-- Absolute angular, given by `(0,1)`. -/
noncomputable def absoluteAngular (_ : Absolute) : Absolute := (0,1)
/-- Absolute fast, given by `(((0,(0,0)),temporalVector),0)`. -/
noncomputable def absoluteFast (_ : Absolute) : Absolute := (((0,(0,0)),temporalVector),0)

theorem cover_inverse_radial (i : ℕ) (a : ℝ) :
    (CommonCoverSolve.coverPower i).symm ((ChartScales.Lambda^i * a) • radialVector) = a •
        radialVector := by
  apply (CommonCoverSolve.coverPower i).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
  rw [show CommonCoverSolve.coverPower i radialVector = ChartScales.Lambda^i • radialVector from
    CommonBaseContext.coverPower_radial i, smul_smul]
  congr 1
  ring

theorem cover_inverse_temporal (i : ℕ) (a : ℝ) :
    (CommonCoverSolve.coverPower i).symm ((ChartScales.Tg^i * a) • temporalVector) = a •
        temporalVector := by
  apply (CommonCoverSolve.coverPower i).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
  rw [show CommonCoverSolve.coverPower i temporalVector = ChartScales.Tg^i • temporalVector from
    CommonBaseContext.coverPower_temporal i, smul_smul]
  congr 1
  ring

theorem sqrt_radialJacobian {q : ℝ} (hq : 0 < q) (d R : ℝ) :
    q^(d/2) * RadialPullback.radialJacobian d R =
      Real.sqrt q * RadialPullback.radialJacobian d (Real.sqrt q * R) := by
  simp only [RadialPullback.radialJacobian,
    TemporalStateCoherence.mul_rpow_pos_left (Real.sqrt_pos.mpr hq)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq.le]
  have he : q^(d/2) = q^(1/2:ℝ) * q^((1/2:ℝ)*(d-1)) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  rw [he]
  ring

theorem absoluteChart_radius (n : ℕ) (x : ChartPoint) :
    absoluteRadius (absoluteChart n x) = Real.sqrt (ChartScales.Q n) * x.1.1 := rfl

theorem absoluteChart_radial (B n : ℕ) (x : ChartPoint) :
    absoluteChart n ((PrimaryResidualClass.directions (commonContext B)).radialField n x) =
      Real.sqrt (ChartScales.Q n) • absoluteRadial (absoluteChart n x) := by
  have he : (PrimaryResidualClass.directions (commonContext B)).radialField n x =
      ((1, ((0,0), ((ChartScales.Lambda ^ CommonWindow.index h n *
        ChartScales.Q n ^ (ChartScales.radialExponent h / 2)) *
        RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1.1) • radialVector)),0) :=
            by
    simp [LinearWaveBounds.GraphDirections.radialField, PrimaryResidualClass.directions,
      commonContext, CommonBaseContext.context, CommonBaseContext.operators,
      CorrectionState.graphOperators, CommonBaseContext.reconstruction,
      CommonBaseContext.radialFrequency, smul_smul, radialVector]
    rfl
  rw [he]
  change (toAbsolute n
    (1, ((0,0), ((ChartScales.Lambda ^ CommonWindow.index h n *
      ChartScales.Q n ^ (ChartScales.radialExponent h / 2)) *
      RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1.1) • radialVector)),0) = _
  simp only [toAbsolute, mul_zero, mul_one]
  rw [mul_assoc, cover_inverse_radial, sqrt_radialJacobian (ChartScales.Q_pos n)]
  simp [absoluteRadial, absoluteChart_apply, toAbsolute, smul_smul]

theorem absoluteChart_axial (B n : ℕ) (U : LocalSignedRequest.SlowRegion (2 * h)) (x : ChartPoint) :
    absoluteChart n ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x) =
      Real.sqrt (ChartScales.Q n) • absoluteAxial (absoluteChart n x) := by
  have he : ChartScales.Q n ^ CoordinateAlgebra.D h * ChartScales.Q n ^ h = Real.sqrt
      (ChartScales.Q n) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n), Real.sqrt_eq_rpow]
    congr 1
    unfold CoordinateAlgebra.D
    ring
  have hx : (PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x =
      ((0, ((0,ChartScales.Q n ^ h),0)),0) := by
    change ChartScales.Q n ^ h • ((0, ((0,1),0)),0) = _
    simp
  rw [hx]
  change (toAbsolute n (0, ((0,ChartScales.Q n ^ h),0)),0) = _
  simp [toAbsolute, absoluteAxial, he]

theorem absoluteChart_angular (B n : ℕ) (x : ChartPoint) :
    absoluteChart n (PrimaryResidualClass.directions (commonContext B)).angular =
      absoluteAngular (absoluteChart n x) := by
  change (toAbsolute n 0,1) = (0,1)
  simp [toAbsolute]

theorem absoluteChart_fast (B n : ℕ) (x : ChartPoint) :
    absoluteChart n ((PrimaryResidualClass.directions (commonContext B)).fastField n x) =
      ChartScales.Q n ^ (1+h) • absoluteFast (absoluteChart n x) := by
  have he : (PrimaryResidualClass.directions (commonContext B)).fastField n x =
      ((0, ((0,0), (ChartScales.Tg ^ CommonWindow.index h n *
        ChartScales.Q n ^ (1+h)) • temporalVector)),0) := by
    simp [LinearWaveBounds.GraphDirections.fastField, PrimaryResidualClass.directions,
      commonContext, CommonBaseContext.context, CommonBaseContext.operators,
      CorrectionState.graphOperators, CommonBaseContext.fastCoefficient, temporalVector]
    rfl
  rw [he]
  change (toAbsolute n (0, ((0,0),
    (ChartScales.Tg ^ CommonWindow.index h n * ChartScales.Q n ^ (1+h)) • temporalVector)),0) = _
  simp only [toAbsolute, mul_zero]
  rw [cover_inverse_temporal]
  simp [absoluteFast]

/-! ## The actual cut coefficient, corrected wave, and Gaussian field -/

variable {B N0 : ℕ}

/-- Absolute cut amplitude, given by `periodicGaussian j L x.1.2 • absoluteAmplitude j L x.1`. -/
noncomputable def absoluteCutAmplitude (j : Fin 2) (L : Label B N0) (x : Absolute) : ComplexVector
    :=
  periodicGaussian j L x.1.2 • absoluteAmplitude j L x.1

/-- Absolute exact amplitude, constructed using `CurlClassBounds.realizedCoefficient`. -/
noncomputable def absoluteExactAmplitude (j : Fin 2) (L : Label B N0) : Absolute → ComplexVector :=
  CurlClassBounds.realizedCoefficient 1 absoluteRadius absoluteRadial absoluteAngular absoluteAxial
    (absolutePhase j L) (absoluteCutAmplitude j L)

/-- Absolute velocity, defined pointwise by `(vectorMode 1 (absolutePhase j L)
(absoluteExactAmplitude j L) x i).re`. -/
noncomputable def absoluteVelocity (j : Fin 2) (L : Label B N0) (x : Absolute) : Fin 3 → ℝ :=
  fun i => (vectorMode 1 (absolutePhase j L) (absoluteExactAmplitude j L) x i).re

/-- Absolute gaussian coefficient, given by `along absoluteFast (fun y => periodicGaussian j L
y.1.2) x • absoluteAmplitude j L x.1`. -/
noncomputable def absoluteGaussianCoefficient (j : Fin 2) (L : Label B N0) (x : Absolute) :
    ComplexVector :=
  along absoluteFast (fun y => periodicGaussian j L y.1.2) x • absoluteAmplitude j L x.1

/-- Absolute gaussian, defined pointwise by `(vectorMode 1 (absolutePhase j L)
(absoluteGaussianCoefficient j L) x i).re`. -/
noncomputable def absoluteGaussian (j : Fin 2) (L : Label B N0) (x : Absolute) : Fin 3 → ℝ :=
  fun i => (vectorMode 1 (absolutePhase j L) (absoluteGaussianCoefficient j L) x i).re

theorem cutAmplitude_representation (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n =
      fun x => ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteCutAmplitude j L (absoluteChart n
          x) := by
  funext x
  simp only [LinearWaveBounds.WaveCoefficients.withCutoff, chartCutoff, chartCoefficients,
    absoluteCutAmplitude, absoluteChart_apply, smul_smul]
  rw [mul_comm]

theorem phase_representation (j : Fin 2) (L : Label B N0) (n : ℕ) :
    (chartCoefficients j L).phase n =
      fun x => (1 / (ChartScales.carrier h n : ℝ)) * absolutePhase j L (absoluteChart n x) := by
  funext x
  simp [chartCoefficients, absoluteChart_apply, div_eq_mul_inv, mul_comm]

/-- Full-fiber transport of the coefficient actually used by the iteration.
No equality of corrected fields, nor a tangency assertion, is an input. -/
theorem exactAmplitude_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (piece U j L).exactCoefficients.amplitude n x =
      ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteExactAmplitude j L (absoluteChart n x) := by
  have hk : (ChartScales.carrier h n : ℝ) ≠ 0 := (chartCoefficients_frequency_pos j L n).ne'
  change CurlClassBounds.realizedCoefficient (ChartScales.carrier h n) (fun y : ChartPoint => y.1.1)
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n)
    ((chartCoefficients j L).phase n)
    (((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n) x = _
  rw [phase_representation, cutAmplitude_representation]
  exact realizedCoefficient_equiv (absoluteChart n) (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne'
    (one_div_ne_zero hk) hk (mul_one_div_cancel hk) _ _ _ _ _ _ _ _
    (absoluteChart_radius n) (absoluteChart_radial B n) (absoluteChart_angular B n)
    (absoluteChart_axial B n U) _ _ _ x

theorem piece_velocity_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (piece U j L).velocity n x =
      ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteVelocity j L (absoluteChart n x) := by
  funext i
  change ((piece U j L).exactCoefficients.amplitude n x i *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) x).re = _
  rw [exactAmplitude_representation, chartCoefficients_carrier]
  simp only [absoluteVelocity, vectorMode, mode, Pi.smul_apply, Complex.real_smul,
    absoluteChart_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im,
    zero_mul, add_zero]
  ring

theorem gaussianCoefficient_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    LinearWaveBounds.excludedSlotError (piece U j L).directions (piece U j L).cutoff
      (piece U j L).coefficients.amplitude 0 n x =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h + 1/2) • absoluteGaussianCoefficient j L
          (absoluteChart n x) := by
  have hd := PhysicalResidualNaturality.along_pull (absoluteChart n) 1
    (ChartScales.Q n ^ (1+h)) ((PrimaryResidualClass.directions (commonContext B)).fastField n)
    absoluteFast (fun y => periodicGaussian j L y.1.2) x (absoluteChart_fast B n x)
  simp only [one_mul, smul_eq_mul, absoluteChart_apply] at hd
  have hs : ChartScales.Q n ^ (1+h) * ChartScales.Q n ^ CoordinateAlgebra.A h =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h + 1/2) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  change along ((PrimaryResidualClass.directions (commonContext B)).fastField n)
    (fun y => periodicGaussian j L (toAbsolute n y.1).2) x •
      (ChartScales.Q n ^ CoordinateAlgebra.A h • absoluteAmplitude j L (toAbsolute n x.1)) + (1 -
          _) • (0 : ComplexVector) = _
  rw [smul_zero, add_zero]
  rw [hd]
  simp only [absoluteGaussianCoefficient, smul_smul, absoluteChart_apply]
  rw [mul_right_comm, hs]

theorem piece_excluded_representation (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (piece U j L).excluded n x =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h + 1/2) • absoluteGaussian j L (absoluteChart n
          x) := by
  funext i
  change (LinearWaveBounds.excludedSlotError (piece U j L).directions (piece U j L).cutoff
    (piece U j L).coefficients.amplitude 0 n x i *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) x).re = _
  rw [gaussianCoefficient_representation, chartCoefficients_carrier]
  simp only [absoluteGaussian, vectorMode, mode, Pi.smul_apply, Complex.real_smul,
    absoluteChart_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im,
    zero_mul, add_zero]
  ring

/-! ## Exact comparison of two genuine common-cover bands -/

theorem band_power_cancel (n m : ℕ) (a : ℝ) :
    ChartScales.Q m ^ a * (ChartScales.Q n / ChartScales.Q m) ^ a = ChartScales.Q n ^ a := by
  rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos (ChartScales.Q_pos m) a).ne'

theorem toAbsolute_bandChart (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : LocalSignedRequest.Point) :
    toAbsolute m (GaugeStateCoherence.bandChartEquiv h n m k x) = toAbsolute n x := by
  simp only [GaugeStateCoherence.bandChartEquiv_apply, toAbsolute,
    GaugeStateCoherence.bandSlowEquiv_apply]
  apply Prod.ext
  · apply Prod.ext
    · change Real.sqrt (ChartScales.Q m) * (GaugeStateCoherence.bandScale n m * x.1) =
        Real.sqrt (ChartScales.Q n) * x.1
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← mul_assoc]
      rw [GaugeStateCoherence.bandScale, band_power_cancel]
    · apply Prod.ext
      · change ChartScales.Q m ^ CoordinateAlgebra.D h *
          ((ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h * x.2.1.2) = _
        rw [← mul_assoc, band_power_cancel]
      · change ChartScales.Q m * ((ChartScales.Q n / ChartScales.Q m) * x.2.1.1) = _
        rw [← mul_assoc, mul_div_cancel₀ _ (ChartScales.Q_pos m).ne']
  · change (CommonCoverSolve.coverPower (CommonWindow.index h m)).symm
      (TemporalMeanUpdate.coverMap k x.2.2) = _
    apply (CommonCoverSolve.coverPower (CommonWindow.index h m)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ← hi, Nat.add_comm,
      CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply,
      MeanChartCompatibility.coverMap_eq_coverPower]

theorem piece_velocity_band (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : ChartPoint) :
    (piece U j L).velocity n x = GaugeStateCoherence.bandVelocityScale h n m •
      (piece U j L).velocity m (GaugeStateCoherence.bandChartEquiv h n m k x.1,x.2) := by
  rw [piece_velocity_representation, piece_velocity_representation]
  simp only [absoluteChart_apply, toAbsolute_bandChart n m k hi, smul_smul]
  congr 1
  rw [GaugeStateCoherence.bandVelocityScale, mul_comm, band_power_cancel]

theorem band_pressure_cancel (n m : ℕ) :
    (GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m) *
      ChartScales.Q m ^ (2 * CoordinateAlgebra.A h) = ChartScales.Q n ^ (2 * CoordinateAlgebra.A h)
          := by
  rw [GaugeStateCoherence.bandVelocityScale, ← Real.rpow_add (div_pos (ChartScales.Q_pos n)
      (ChartScales.Q_pos m))]
  rw [show CoordinateAlgebra.A h + CoordinateAlgebra.A h = 2 * CoordinateAlgebra.A h by ring,
    mul_comm, band_power_cancel]

theorem band_source_cancel (n m : ℕ) :
    (GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m *
      GaugeStateCoherence.bandScale n m) * ChartScales.Q m ^ (2 * CoordinateAlgebra.A h + 1/2) =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A h + 1/2) := by
  rw [GaugeStateCoherence.bandVelocityScale, GaugeStateCoherence.bandScale,
    ← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)),
    ← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
  rw [show CoordinateAlgebra.A h + CoordinateAlgebra.A h + 1/2 = 2 * CoordinateAlgebra.A h + 1/2 by
      ring,
    mul_comm, band_power_cancel]

theorem piece_pressure_band (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : ChartPoint) :
    (piece U j L).pressure n x =
      (GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m) *
        (piece U j L).pressure m (GaugeStateCoherence.bandChartEquiv h n m k x.1,x.2) := by
  rw [piece_pressure_representation, piece_pressure_representation,
    toAbsolute_bandChart n m k hi, ← mul_assoc, band_pressure_cancel]

theorem piece_excluded_band (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : ChartPoint) :
    (piece U j L).excluded n x =
      (GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m *
        GaugeStateCoherence.bandScale n m) •
      (piece U j L).excluded m (GaugeStateCoherence.bandChartEquiv h n m k x.1,x.2) := by
  rw [piece_excluded_representation, piece_excluded_representation]
  simp only [absoluteChart_apply, toAbsolute_bandChart n m k hi, smul_smul]
  rw [band_source_cancel]

/-! ## Ordinary regularity before restricting to a bounded strip -/

/-- Positive chart, given by `{x | 0 < x.1.2.1.1}`. -/
noncomputable def positiveChart : Set ChartPoint := {x | 0 < x.1.2.1.1}
/-- Positive radial chart, given by `{x | 0 < x.1.1 ∧ 0 < x.1.2.1.1}`. -/
noncomputable def positiveRadialChart : Set ChartPoint := {x | 0 < x.1.1 ∧ 0 < x.1.2.1.1}
/-- Positive absolute, given by `{x | 0 < x.1.1.2.2}`. -/
noncomputable def positiveAbsolute : Set Absolute := {x | 0 < x.1.1.2.2}
/-- Positive radial absolute, given by `{x | 0 < x.1.1.1 ∧ 0 < x.1.1.2.2}`. -/
noncomputable def positiveRadialAbsolute : Set Absolute := {x | 0 < x.1.1.1 ∧ 0 < x.1.1.2.2}

theorem positiveChart_open : IsOpen positiveChart :=
  isOpen_lt continuous_const continuous_fst.snd.fst.fst
theorem positiveRadialChart_open : IsOpen positiveRadialChart :=
  (isOpen_lt continuous_const continuous_fst.fst).inter positiveChart_open
theorem positiveAbsolute_open : IsOpen positiveAbsolute :=
  isOpen_lt continuous_const continuous_fst.fst.snd.snd
theorem positiveRadialAbsolute_open : IsOpen positiveRadialAbsolute :=
  (isOpen_lt continuous_const continuous_fst.fst.fst).inter positiveAbsolute_open

theorem frequencySlow_smoothAt (B n : ℕ) {p : PhaseCalculus.Slow}
    (hR : 0 < p.1) (hT : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (BaseContextAssembly.frequencySlow certificate modulation upper B n) p := by
  have hs := (BaseContextAssembly.physicalComponent_smoothAt certificate modulation upper B n 1
    (x := BaseContextAssembly.insertSlow p) hT).comp p
        BaseContextAssembly.insertSlow.contDiff.contDiffAt
  have he : (fun y => BaseContextAssembly.frequencySlow certificate modulation upper B n y) =ᶠ[𝓝 p]
      (fun y => (ChartScales.Q n ^ CoordinateAlgebra.A h *
        FinalSlowBase.velocity certificate modulation upper B
          (BaseContextAssembly.physicalPoint h n (BaseContextAssembly.insertSlow y)) 1) / y.1) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hR,
      (isOpen_lt continuous_const continuous_snd.snd).mem_nhds hT] with y hyR hyT
    have hh := BaseContextAssembly.angularBase_physical certificate modulation upper B n
      (x := BaseContextAssembly.insertSlow y) hyT hyR
    apply (eq_div_iff hyR.ne').mpr
    simp only [BaseContextAssembly.base, BaseContextAssembly.frequencyBase,
      BaseContextAssembly.frequencySlow, BaseContextAssembly.insertSlow,
      BaseContextAssembly.slowCoordinates_apply, mul_comm] at hh ⊢
    exact hh
  exact (hs.div contDiffAt_fst hR.ne').congr_of_eventuallyEq he

theorem axialSlow_smoothAt (B n : ℕ) {p : PhaseCalculus.Slow} (hT : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (BaseContextAssembly.axialSlow certificate modulation upper B n) p := by
  have hs := (BaseContextAssembly.physicalComponent_smoothAt certificate modulation upper B n 2
    (x := BaseContextAssembly.insertSlow p) hT).comp p
        BaseContextAssembly.insertSlow.contDiff.contDiffAt
  have he : (fun y => BaseContextAssembly.axialSlow certificate modulation upper B n y) =ᶠ[𝓝 p]
      (fun y => ChartScales.Q n ^ CoordinateAlgebra.A h *
        FinalSlowBase.velocity certificate modulation upper B
          (BaseContextAssembly.physicalPoint h n (BaseContextAssembly.insertSlow y)) 2) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hT] with y hyT
    exact BaseContextAssembly.axialBase_physical certificate modulation upper B n
      (x := BaseContextAssembly.insertSlow y) hyT
  exact hs.congr_of_eventuallyEq he

theorem absoluteAmplitude_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (fun x : Absolute => absoluteAmplitude j L x.1) positiveAbsolute := by
  have hg : ContDiff ℝ ∞ (fun x : Absolute => (nativeSlow L x.1,x.1.2)) :=
    ((nativeSlow_smooth L).comp contDiff_fst).prodMk contDiff_fst.snd
  have hm : MapsTo (fun x : Absolute => (nativeSlow L x.1,x.1.2)) positiveAbsolute
      WaveEdgeExtension.nativeSlowDomain := by
    intro x hx
    exact div_pos hx (ChartScales.Q_pos _)
  exact ((uncutAmplitude_smooth j L).comp hg.contDiffOn hm).const_smul _

theorem absolutePressureCoefficient_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (fun x : Absolute => absolutePressure j L x.1) positiveAbsolute := by
  have hg : ContDiff ℝ ∞ (fun x : Absolute => (nativeSlow L x.1,x.1.2)) :=
    ((nativeSlow_smooth L).comp contDiff_fst).prodMk contDiff_fst.snd
  have hm : MapsTo (fun x : Absolute => (nativeSlow L x.1,x.1.2)) positiveAbsolute
      WaveEdgeExtension.nativeSlowDomain := by
    intro x hx
    exact div_pos hx (ChartScales.Q_pos _)
  exact ((uncutPressure_smooth j L).comp hg.contDiffOn hm).const_smul _

theorem absoluteCutoff_smooth (j : Fin 2) (L : Label B N0) :
    ContDiff ℝ ∞ (fun x : Absolute => periodicGaussian j L x.1.2) :=
  (periodicGaussian_smooth j L).comp contDiff_fst.snd

theorem absoluteCutAmplitude_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteCutAmplitude j L) positiveAbsolute :=
  (absoluteCutoff_smooth j L).contDiffOn.smul (absoluteAmplitude_smooth j L)

theorem absolutePhase_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absolutePhase j L) positiveRadialAbsolute := by
  intro x hx
  have hR : 0 < (nativeSlow L x.1).1 := div_pos hx.1 (Real.sqrt_pos.mpr (ChartScales.Q_pos _))
  have hT : 0 < (nativeSlow L x.1).2.2 := div_pos hx.2 (ChartScales.Q_pos _)
  have hp := ((nativeSlow_smooth L).comp contDiff_fst).contDiffAt (x := x)
  have hF : ContDiffAt ℝ ∞ (fun y : Absolute => (phases B N0 j).phase.F L (nativeSlow L y.1)) x :=
    (frequencySlow_smoothAt B _ hR hT).comp x hp
  have hG : ContDiffAt ℝ ∞ (fun y : Absolute => (phases B N0 j).phase.G L (nativeSlow L y.1)) x :=
    (axialSlow_smoothAt B _ hT).comp x hp
  have hc : ContDiffAt ℝ ∞ (fun y : Absolute =>
      PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff y.1.2) x :=
    ((PeriodicPhaseAssembly.periodicClock_contDiff (geometry j L) (clockWindow L)).comp
        contDiff_fst.snd).contDiffAt
  have hP : ContDiffAt ℝ ∞ (fun y : Absolute => periodicPhase j L (nativeSlow L y.1) y.1.2) x :=
    ((contDiffAt_const.mul hp.snd.fst).add (contDiffAt_const.mul hp.fst)).sub
      (hc.mul ((contDiffAt_const.mul hF).add (contDiffAt_const.mul hG)))
  exact ((contDiffAt_const.mul contDiffAt_snd).add (contDiffAt_const.mul hP)).contDiffWithinAt

theorem absoluteRadial_smooth : ContDiffOn ℝ ∞ absoluteRadial positiveRadialAbsolute := by
  intro x hx
  have hr : ContDiffAt ℝ ∞ (fun y : Absolute =>
      RadialPullback.radialJacobian (ChartScales.radialExponent h) y.1.1.1) x :=
    contDiffAt_const.mul (contDiffAt_fst.fst.fst.rpow_const_of_ne hx.1.ne')
  exact ((contDiffAt_const.prodMk (hr.smul contDiffAt_const)).prodMk
      contDiffAt_const).contDiffWithinAt

/-- Absolute normal, given by `phaseNormal absoluteRadius absoluteRadial absoluteAngular
absoluteAxial (absolutePhase j L)`. -/
noncomputable def absoluteNormal (j : Fin 2) (L : Label B N0) : Absolute → ProblemStatement.Space :=
  phaseNormal absoluteRadius absoluteRadial absoluteAngular absoluteAxial (absolutePhase j L)

theorem absoluteNormal_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteNormal j L) positiveRadialAbsolute := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact HarmonicCalculus.contDiffOn_along positiveRadialAbsolute_open absoluteRadial_smooth
      (absolutePhase_smooth j L)
  · exact (HarmonicCalculus.contDiffOn_along positiveRadialAbsolute_open contDiffOn_const
      (absolutePhase_smooth j L)).div
      contDiffOn_fst.fst.fst (fun x hx => hx.1.ne')
  · exact HarmonicCalculus.contDiffOn_along positiveRadialAbsolute_open contDiffOn_const
      (absolutePhase_smooth j L)

theorem absolutePhase_angular (j : Fin 2) (L : Label B N0) :
    CopyAngularInvariance.AffinePhase ((0 : AbsolutePoint),1)
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L : ℝ)
      (absolutePhase j L) := by
  intro x t
  simp only [absolutePhase, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero,
    Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one]
  ring

theorem absoluteNormal_ne (j : Fin 2) (L : Label B N0) {x : Absolute}
    (hx : x ∈ positiveRadialAbsolute) : absoluteNormal j L x ≠ 0 := by
  have hd := (absolutePhase_angular j L).directional_eq
    (((absolutePhase_smooth j L).contDiffAt (positiveRadialAbsolute_open.mem_nhds
        hx)).differentiableAt (by
        simp))
  have hc : absoluteNormal j L x 1 =
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L : ℝ) /
          x.1.1.1 := by
    simpa only [absoluteNormal, phaseNormal, absoluteAngular, absoluteRadius, along,
      PiLp.single_apply, Matrix.cons_val_one, Matrix.cons_val_zero] using congrArg (fun a : ℝ => a
          / x.1.1.1) hd
  have hp : (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L
      : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (PrimaryGeometryAssembly.angularMode_ne_zero certificate modulation
        (choice B N0).prepared j L)
  intro hz
  have hh := congrArg (fun v : ProblemStatement.Space => v 1) hz
  change absoluteNormal j L x 1 = 0 at hh
  rw [hc] at hh
  exact div_ne_zero hp hx.1.ne' hh

theorem absoluteExactAmplitude_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteExactAmplitude j L) positiveRadialAbsolute := by
  have ha : ContDiffOn ℝ ∞ (absoluteCutAmplitude j L) positiveRadialAbsolute :=
    (absoluteCutAmplitude_smooth j L).mono (fun _ hx => hx.2)
  have hb := CurlClassBounds.normalCoefficient_contDiffOn (absoluteNormal_smooth j L) ha
    (fun _ hx => absoluteNormal_ne j L hx)
  have hc := CurlClassBounds.cylindricalCurl_contDiffOn positiveRadialAbsolute_open
    (R := absoluteRadius) (Vθ := absoluteAngular) (Vz := absoluteAxial)
    (contDiffOn_fst.fst.fst.inv (fun x hx => hx.1.ne')) absoluteRadial_smooth
    contDiffOn_const contDiffOn_const hb
  exact ha.add ((hc.const_smul Complex.I).const_smul (1 / (1 : ℝ)))

theorem absoluteVelocity_smooth_radial (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteVelocity j L) positiveRadialAbsolute := by
  apply contDiffOn_pi.mpr
  intro i
  exact Complex.reCLM.contDiff.comp_contDiffOn
    (HarmonicCalculus.contDiffOn_mode 1 (absolutePhase_smooth j L)
      (contDiffOn_pi.mp (absoluteExactAmplitude_smooth j L) i))

/-- Amplitude radius, given by `PrimaryTargetBounds.profileRadius h (nativeSlow L x.1)`. -/
noncomputable def amplitudeRadius (L : Label B N0) (x : Absolute) : ℝ :=
  PrimaryTargetBounds.profileRadius h (nativeSlow L x.1)

theorem amplitudeRadius_smoothAt (L : Label B N0) {x : Absolute}
    (hx : x ∈ positiveAbsolute) : ContDiffAt ℝ ∞ (amplitudeRadius L) x := by
  have hy : 0 < (nativeSlow L x.1).2.2 :=
    div_pos hx (ChartScales.Q_pos _)
  have hp : ContDiffAt ℝ ∞ (fun y : Absolute => nativeSlow L y.1) x :=
    ((nativeSlow_smooth L).comp contDiff_fst).contDiffAt
  have hq := BaseChartJets.normalizedCoordinates_q_pos outgoing.data.h_pos outgoing.data.h_lt_half
      hy
  have hs := (BaseChartJets.normalizedCoordinates_smoothAt outgoing.data.h_pos
      outgoing.data.h_lt_half hy).comp x hp
  exact hp.fst.div (hs.fst.sqrt hq.ne') (Real.sqrt_pos.mpr hq).ne'

theorem absoluteAmplitude_zero_outside (j : Fin 2) (L : Label B N0) (x : Absolute)
    (hx : amplitudeRadius L x ∉ Ioo (PrimaryTargetBounds.leftRadius nominal)
        (PrimaryTargetBounds.rightRadius nominal)) :
    absoluteAmplitude j L x.1 = 0 := by
  change _ • (∑' k : TorusInverse.Frequency, CurlClassBounds.complexify
    (WaveEdgeExtension.nativeExtension nominal (outerRawVelocity j L)
      (nativeSlow L x.1,(geometry j L).coordinates k x.1.2))) = 0
  have hz : (∑' k : TorusInverse.Frequency, CurlClassBounds.complexify
    (WaveEdgeExtension.nativeExtension nominal (outerRawVelocity j L)
      (nativeSlow L x.1,(geometry j L).coordinates k x.1.2))) = 0 := by
    simpa only [tsum_zero] using (tsum_congr (fun k : TorusInverse.Frequency =>
      show CurlClassBounds.complexify (WaveEdgeExtension.nativeExtension nominal (outerRawVelocity
          j L)
        (nativeSlow L x.1,(geometry j L).coordinates k x.1.2)) = 0 by
          rw [WaveEdgeExtension.nativeExtension_outside nominal _
            (x := (nativeSlow L x.1,(geometry j L).coordinates k x.1.2)) hx, map_zero]))
  rw [hz, smul_zero]

theorem absolutePressure_zero_outside (j : Fin 2) (L : Label B N0) (x : Absolute)
    (hx : amplitudeRadius L x ∉ Ioo (PrimaryTargetBounds.leftRadius nominal)
        (PrimaryTargetBounds.rightRadius nominal)) :
    absolutePressure j L x.1 = 0 := by
  change _ • (∑' k : TorusInverse.Frequency,
    WaveEdgeExtension.nativeExtension nominal (outerRawPressure j L)
      (nativeSlow L x.1,(geometry j L).coordinates k x.1.2)) = 0
  have hz : (∑' k : TorusInverse.Frequency,
    WaveEdgeExtension.nativeExtension nominal (outerRawPressure j L)
      (nativeSlow L x.1,(geometry j L).coordinates k x.1.2)) = 0 := by
    simpa only [tsum_zero] using (tsum_congr (fun k : TorusInverse.Frequency =>
      show WaveEdgeExtension.nativeExtension nominal (outerRawPressure j L)
        (nativeSlow L x.1,(geometry j L).coordinates k x.1.2) = 0 from
          WaveEdgeExtension.nativeExtension_outside nominal _ hx))
  rw [hz, smul_zero]

theorem absolutePair_zero_germ_outside (j : Fin 2) (L : Label B N0) {x : Absolute}
    (hT : x ∈ positiveAbsolute)
    (hx : amplitudeRadius L x ∉ Icc (PrimaryTargetBounds.leftRadius nominal)
        (PrimaryTargetBounds.rightRadius nominal)) :
    ((fun y : Absolute => absoluteAmplitude j L y.1) =ᶠ[𝓝 x] fun _ => 0) ∧
    ((fun y : Absolute => absolutePressure j L y.1) =ᶠ[𝓝 x] fun _ => 0) := by
  have hn : ∀ᶠ y in 𝓝 x, amplitudeRadius L y ∉
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) :=
    (amplitudeRadius_smoothAt L hT).continuousAt.eventually (isClosed_Icc.isOpen_compl.mem_nhds hx)
  constructor
  · filter_upwards [hn] with y hy
    exact absoluteAmplitude_zero_outside j L y (fun hh => hy ⟨hh.1.le,hh.2.le⟩)
  · filter_upwards [hn] with y hy
    exact absolutePressure_zero_outside j L y (fun hh => hy ⟨hh.1.le,hh.2.le⟩)

theorem absoluteVelocity_tsupport (j : Fin 2) (L : Label B N0) :
    tsupport (absoluteVelocity j L) ⊆ tsupport (absoluteCutAmplitude j L) := by
  have hc : tsupport (absoluteExactAmplitude j L) ⊆ tsupport (absoluteCutAmplitude j L) := by
    unfold absoluteExactAmplitude CurlClassBounds.realizedCoefficient CurlClassBounds.curlRemainder
    exact (tsupport_add _ _).trans (union_subset subset_rfl
      ((tsupport_smul_subset_right _ _).trans ((tsupport_smul_subset_right _ _).trans
        ((CurlClassBounds.cylindricalCurl_tsupport_subset _ _ _ _ _).trans
          (CurlClassBounds.coefficient_tsupport_subset _ _ _ _ _ _)))))
  apply Subset.trans _ hc
  apply closure_mono
  intro x hx hz
  apply hx
  funext i
  simp [absoluteVelocity, vectorMode, mode, hz]

theorem absoluteVelocity_zero_germ_outside (j : Fin 2) (L : Label B N0) {x : Absolute}
    (hT : x ∈ positiveAbsolute)
    (hx : amplitudeRadius L x ∉ Icc (PrimaryTargetBounds.leftRadius nominal)
        (PrimaryTargetBounds.rightRadius nominal)) :
    absoluteVelocity j L =ᶠ[𝓝 x] fun _ => 0 := by
  have ha := (absolutePair_zero_germ_outside j L hT hx).1
  have hc : absoluteCutAmplitude j L =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ha] with y hy
    simp [absoluteCutAmplitude, hy]
  exact notMem_tsupport_iff_eventuallyEq.mp
    (fun hm => (notMem_tsupport_iff_eventuallyEq.mpr hc) (absoluteVelocity_tsupport j L hm))

theorem amplitudeRadius_nonpositive (L : Label B N0) {x : Absolute} (hx : x.1.1.1 ≤ 0) :
    amplitudeRadius L x ≤ 0 := by
  change ((x.1.1.1 / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L))) /
    Real.sqrt _) ≤ 0
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg hx (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem amplitudeRadius_outside_nonpositive (L : Label B N0) {x : Absolute} (hx : x.1.1.1 ≤ 0) :
    amplitudeRadius L x ∉ Icc (PrimaryTargetBounds.leftRadius nominal)
        (PrimaryTargetBounds.rightRadius nominal) := by
  intro hi
  exact (not_lt_of_ge (amplitudeRadius_nonpositive L hx))
    ((PrimaryTargetBounds.leftRadius_pos nominal).trans_le hi.1)

theorem absoluteVelocity_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteVelocity j L) positiveAbsolute := by
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact ((absoluteVelocity_smooth_radial j L).contDiffAt
      (positiveRadialAbsolute_open.mem_nhds ⟨hr,hx⟩)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (absoluteVelocity_zero_germ_outside j L hx
        (amplitudeRadius_outside_nonpositive L (le_of_not_gt hr)))).contDiffWithinAt

theorem absolutePressureMode_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absolutePressureMode j L) positiveAbsolute := by
  have hp : ContDiffOn ℝ ∞ (fun y : Absolute => absolutePressure j L y.1) positiveRadialAbsolute :=
    (absolutePressureCoefficient_smooth j L).mono (fun _ hx => hx.2)
  have hs : ContDiffOn ℝ ∞ (absolutePressureMode j L) positiveRadialAbsolute :=
    Complex.reCLM.contDiff.comp_contDiffOn (HarmonicCalculus.contDiffOn_mode 1
        (absolutePhase_smooth j L)
      ((absoluteCutoff_smooth j L).contDiffOn.smul hp))
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact (hs.contDiffAt (positiveRadialAbsolute_open.mem_nhds ⟨hr,hx⟩)).contDiffWithinAt
  · have hp := (absolutePair_zero_germ_outside j L hx
      (amplitudeRadius_outside_nonpositive L (le_of_not_gt hr))).2
    have hz : absolutePressureMode j L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hp] with y hy
      simp [absolutePressureMode, mode, hy]
    exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

theorem piece_velocity_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).velocity n) positiveChart := by
  have hm : MapsTo (absoluteChart n) positiveChart positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (((absoluteVelocity_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm).const_smul
    (ChartScales.Q n ^ CoordinateAlgebra.A h)).congr
      (fun x _ => piece_velocity_representation U j L n x)

theorem piece_pressure_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).pressure n) positiveChart := by
  have hm : MapsTo (absoluteChart n) positiveChart positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (contDiffOn_const.mul
    ((absolutePressureMode_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm)).congr
      (fun x _ => piece_pressure_representation U j L n x)

theorem absoluteTangent_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteTangent j L) positiveAbsolute := by
  have ha : ContDiffOn ℝ ∞ (absoluteCutAmplitude j L) positiveRadialAbsolute :=
    (absoluteCutAmplitude_smooth j L).mono (fun _ hx => hx.2)
  have hs : ContDiffOn ℝ ∞ (absoluteTangent j L) positiveRadialAbsolute := by
    apply contDiffOn_pi.mpr
    intro i
    exact Complex.reCLM.contDiff.comp_contDiffOn (HarmonicCalculus.contDiffOn_mode 1
      (absolutePhase_smooth j L) (contDiffOn_pi.mp ha i))
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact (hs.contDiffAt (positiveRadialAbsolute_open.mem_nhds ⟨hr,hx⟩)).contDiffWithinAt
  · have hp := (absolutePair_zero_germ_outside j L hx
      (amplitudeRadius_outside_nonpositive L (le_of_not_gt hr))).1
    have hz : absoluteTangent j L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hp] with y hy
      funext i
      simp [absoluteTangent, vectorMode, mode, hy]
    exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

theorem piece_tangentVelocity_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).tangentVelocity n) positiveChart := by
  have hm : MapsTo (absoluteChart n) positiveChart positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (((absoluteTangent_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm).const_smul
    (ChartScales.Q n ^ CoordinateAlgebra.A h)).congr
      (fun x _ => piece_tangent_representation U j L n x)

theorem absoluteGaussianCoefficient_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteGaussianCoefficient j L) positiveAbsolute := by
  have hd : ContDiffOn ℝ ∞ (along absoluteFast (fun y => periodicGaussian j L y.1.2))
      positiveAbsolute :=
    HarmonicCalculus.contDiffOn_along positiveAbsolute_open contDiffOn_const
      (absoluteCutoff_smooth j L).contDiffOn
  exact hd.smul (absoluteAmplitude_smooth j L)

theorem absoluteGaussian_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (absoluteGaussian j L) positiveAbsolute := by
  have ha : ContDiffOn ℝ ∞ (absoluteGaussianCoefficient j L) positiveRadialAbsolute :=
    (absoluteGaussianCoefficient_smooth j L).mono (fun _ hx => hx.2)
  have hs : ContDiffOn ℝ ∞ (absoluteGaussian j L) positiveRadialAbsolute := by
    apply contDiffOn_pi.mpr
    intro i
    exact Complex.reCLM.contDiff.comp_contDiffOn (HarmonicCalculus.contDiffOn_mode 1
      (absolutePhase_smooth j L) (contDiffOn_pi.mp ha i))
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact (hs.contDiffAt (positiveRadialAbsolute_open.mem_nhds ⟨hr,hx⟩)).contDiffWithinAt
  · have hp := (absolutePair_zero_germ_outside j L hx
      (amplitudeRadius_outside_nonpositive L (le_of_not_gt hr))).1
    have hz : absoluteGaussian j L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hp] with y hy
      funext i
      simp [absoluteGaussian, absoluteGaussianCoefficient, vectorMode, mode, hy]
    exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

theorem piece_excluded_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).excluded n) positiveChart := by
  have hm : MapsTo (absoluteChart n) positiveChart positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (((absoluteGaussian_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm).const_smul
    (ChartScales.Q n ^ (2 * CoordinateAlgebra.A h + 1/2))).congr
      (fun x _ => piece_excluded_representation U j L n x)

theorem amplitudeRadius_chart (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1) :
    amplitudeRadius L (absoluteChart n x) = x.1.1 / VariableGaugeMean.qLength (2*h) x.1.2.1 := by
  change PrimaryTargetBounds.profileRadius h (nativeSlow L (toAbsolute n x.1)) = _
  rw [nativeSlow_toAbsolute_eq_slowChange,
    ActualSignedGeometry.profileRadius_slowChange (F := outgoing)
      (ChartScales.Q_pos n) (ChartScales.Q_pos _) hT hR]
  unfold PrimaryTargetBounds.profileRadius VariableGaugeMean.qLength
  rw [BaseChartJets.normalizedCoordinates_eq]
  rfl

theorem piece_velocity_zero_germ_nonpositive (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1) (hR : x.1.1 ≤ 0) :
    (piece U j L).velocity n =ᶠ[𝓝 x] fun _ => 0 := by
  have ht : absoluteChart n x ∈ positiveAbsolute := mul_pos (ChartScales.Q_pos n) hT
  have hr : (absoluteChart n x).1.1.1 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hR
  have hz := (absoluteVelocity_zero_germ_outside j L ht (amplitudeRadius_outside_nonpositive L
      hr)).comp_tendsto
    (absoluteChart n).continuous.continuousAt
  filter_upwards [hz] with y hy
  change absoluteVelocity j L (absoluteChart n y) = 0 at hy
  rw [piece_velocity_representation, hy, smul_zero]

theorem piece_velocity_support (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1) (hne : (piece U j L).velocity n x ≠ 0) :
    x.1.1 ∈ Icc (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.leftRadius nominal)
      (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.rightRadius nominal) := by
  have hr : 0 < x.1.1 := by
    by_contra hh
    exact hne ((piece_velocity_zero_germ_nonpositive U j L n hT (le_of_not_gt hh)).self_of_nhds)
  have ht : absoluteChart n x ∈ positiveAbsolute := mul_pos (ChartScales.Q_pos n) hT
  have hm : amplitudeRadius L (absoluteChart n x) ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
    by_contra hh
    have hz := (absoluteVelocity_zero_germ_outside j L ht hh).self_of_nhds
    apply hne
    rw [piece_velocity_representation, hz, smul_zero]
  rw [amplitudeRadius_chart L n hT hr] at hm
  have hq : 0 < VariableGaugeMean.qLength (2*h) x.1.2.1 :=
    VariableGaugeMean.qLength_pos (by linarith [outgoing.data.h_pos])
      (by linarith [outgoing.data.h_lt_half]) hT
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hq).mp hm.1,
    by simpa only [mul_comm] using (div_le_iff₀ hq).mp hm.2⟩

/-! ## Periodicity on the genuine common covers -/

section PeriodicCalculus

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem along_translate (w : E) {f : E → F} {V : E → E}
    (hf : ∀ x, f (x + w) = f x) (hV : ∀ x, V (x + w) = V x) (x : E) :
    along V f (x+w) = along V f x := by
  unfold along
  rw [← fderiv_comp_add_right w, show (fun y => f (y+w)) = f from funext hf, hV]

theorem phaseNormal_translate (w : E) {R Φ : E → ℝ} {Vr Vt Vz : E → E}
    (hR : ∀ x, R (x + w) = R x) (hΦ : ∀ x, Φ (x + w) = Φ x)
    (hr : ∀ x, Vr (x + w) = Vr x) (ht : ∀ x, Vt (x + w) = Vt x)
    (hz : ∀ x, Vz (x + w) = Vz x) (x : E) :
    phaseNormal R Vr Vt Vz Φ (x+w) = phaseNormal R Vr Vt Vz Φ x := by
  simp only [phaseNormal, hR, along_translate w hΦ hr,
    along_translate w hΦ ht, along_translate w hΦ hz]

theorem cylindricalCurl_translate (w : E) {R : E → ℝ} {Vr Vt Vz : E → E}
    {a : E → ComplexVector} (hR : ∀ x, R (x + w) = R x)
    (ha : ∀ x, a (x + w) = a x) (hr : ∀ x, Vr (x + w) = Vr x)
    (ht : ∀ x, Vt (x + w) = Vt x) (hz : ∀ x, Vz (x + w) = Vz x) (x : E) :
    CurlClassBounds.cylindricalCurl R Vr Vt Vz a (x+w) =
      CurlClassBounds.cylindricalCurl R Vr Vt Vz a x := by
  have hi i : ∀ y, a (y+w) i = a y i := fun y => congrFun (ha y) i
  have hdr i := along_translate w (f := fun y => a y i) (hi i) hr x
  have hdt i := along_translate w (f := fun y => a y i) (hi i) ht x
  have hdz i := along_translate w (f := fun y => a y i) (hi i) hz x
  simp only [CurlClassBounds.cylindricalCurl, hR, ha,
    hdr, hdt, hdz]

theorem realizedCoefficient_translate (w : E) (K : ℝ) {R Φ : E → ℝ}
    {Vr Vt Vz : E → E} {a : E → ComplexVector}
    (hR : ∀ x, R (x + w) = R x) (hΦ : ∀ x, Φ (x + w) = Φ x)
    (ha : ∀ x, a (x + w) = a x) (hr : ∀ x, Vr (x + w) = Vr x)
    (ht : ∀ x, Vt (x + w) = Vt x) (hz : ∀ x, Vz (x + w) = Vz x) (x : E) :
    CurlClassBounds.realizedCoefficient K R Vr Vt Vz Φ a (x+w) =
      CurlClassBounds.realizedCoefficient K R Vr Vt Vz Φ a x := by
  have hc : ∀ y, CurlClassBounds.coefficient R Vr Vt Vz Φ a (y+w) =
      CurlClassBounds.coefficient R Vr Vt Vz Φ a y := by
    intro y
    simp only [CurlClassBounds.coefficient, phaseNormal_translate w hR hΦ hr ht hz, ha]
  simp only [CurlClassBounds.realizedCoefficient, CurlClassBounds.curlRemainder,
    ha, cylindricalCurl_translate w hR hc hr ht hz]

end PeriodicCalculus

/-- Chart deck, given by `((0, ((0,0), TorusAverages.latticePoint k)),0)`. -/
noncomputable def chartDeck (k : TorusInverse.Frequency) : ChartPoint :=
  ((0, ((0,0), TorusAverages.latticePoint k)),0)

theorem native_copy_sum_periodic {E : Type} [NormedAddCommGroup E]
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (f : TorusInverse.Plane → E) (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    (∑' a : TorusInverse.Frequency, f ((geometry j L).coordinates a
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm (Y + TorusAverages.latticePoint
          k)))) =
    ∑' a : TorusInverse.Frequency, f ((geometry j L).coordinates a
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm Y)) := by
  simp only [chartGeometry_coordinates n j L hi]
  change PeriodizedWaveBounds.copySum (fun a Z => f ((chartGeometry n j L).coordinates a Z))
    (Y + TorusAverages.latticePoint k) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (chartGeometry n j L).gap k))
  intro a Z
  exact congrArg f ((chartGeometry n j L).coordinates_deck a k Z)

theorem native_clock_periodic (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency) :
    PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm (Y + TorusAverages.latticePoint
          k)) =
    PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff
      ((CommonCoverSolve.coverPower (CommonWindow.index h n)).symm Y) :=
  native_copy_sum_periodic j L n hi (fun z => (clockWindow L).cutoff z * z.2) Y k

theorem chart_phase_periodic (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (chartCoefficients j L).phase n (x + chartDeck k) = (chartCoefficients j L).phase n x := by
  simp only [chartCoefficients, absolutePhase, periodicPhase, nativeSlow, toAbsolute,
    chartDeck, Prod.fst_add, Prod.snd_add, add_zero, native_clock_periodic j L n hi]

theorem chart_amplitude_periodic (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (chartCoefficients j L).amplitude n (x + chartDeck k) = (chartCoefficients j L).amplitude n x
        := by
  simp only [chartCoefficients, absoluteAmplitude, nativeSlow, toAbsolute,
    chartDeck, Prod.fst_add, Prod.snd_add, add_zero, uncutAmplitude]
  exact congrArg (fun a : ComplexVector => ChartScales.Q n ^ CoordinateAlgebra.A h •
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) • a))
    (native_copy_sum_periodic j L n hi
      (fun z => CurlClassBounds.complexify (attachedRawVelocity j L (nativeSlow L (toAbsolute n
          x.1), z)))
      x.1.2.2 k)

theorem chart_pressure_periodic (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (chartCoefficients j L).pressure n (x + chartDeck k) = (chartCoefficients j L).pressure n x :=
        by
  simp only [chartCoefficients, absolutePressure, nativeSlow, toAbsolute,
    chartDeck, Prod.fst_add, Prod.snd_add, add_zero, uncutPressure]
  exact congrArg (fun a : ℂ => ChartScales.Q n ^ (2*CoordinateAlgebra.A h) •
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2*CoordinateAlgebra.A h)) • a))
    (native_copy_sum_periodic j L n hi
      (fun z => attachedRawPressure j L (nativeSlow L (toAbsolute n x.1), z)) x.1.2.2 k)

theorem chart_cutoff_periodic (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    chartCutoff j L n (x + chartDeck k) = chartCutoff j L n x := by
  simp only [chartCutoff, periodicGaussian, toAbsolute, chartDeck, Prod.snd_add,
    Prod.fst_add, native_clock_periodic j L n hi]

theorem chart_radial_periodic (B n : ℕ) (k : TorusInverse.Frequency) (x : ChartPoint) :
    (PrimaryResidualClass.directions (commonContext B)).radialField n (x+chartDeck k) =
      (PrimaryResidualClass.directions (commonContext B)).radialField n x := by
  apply (absoluteChart n).injective
  rw [absoluteChart_radial, absoluteChart_radial]
  simp [absoluteRadial, absoluteChart_apply, toAbsolute, chartDeck]

theorem piece_exactAmplitude_periodic (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (piece U j L).exactCoefficients.amplitude n (x+chartDeck k) =
      (piece U j L).exactCoefficients.amplitude n x := by
  apply realizedCoefficient_translate (chartDeck k)
  · intro y
    change (y+chartDeck k).1.1 = y.1.1
    simp [chartDeck]
  · exact chart_phase_periodic j L n hi k
  · intro y
    change chartCutoff j L n (y+chartDeck k) • (chartCoefficients j L).amplitude n (y+chartDeck k)
        = _
    rw [chart_cutoff_periodic j L n hi k, chart_amplitude_periodic j L n hi k]
    rfl
  · exact chart_radial_periodic B n k
  · intro y; rfl
  · intro y; rfl

theorem piece_velocity_periodic (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (piece U j L).velocity n (x+chartDeck k) = (piece U j L).velocity n x := by
  funext i
  change ((piece U j L).exactCoefficients.amplitude n (x+chartDeck k) i *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) (x+chartDeck
        k)).re = _
  rw [piece_exactAmplitude_periodic U j L n hi k]
  simp only [carrier, chart_phase_periodic j L n hi k]
  rfl

theorem piece_tangentVelocity_periodic (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (piece U j L).tangentVelocity n (x+chartDeck k) = (piece U j L).tangentVelocity n x := by
  funext i
  change ((chartCutoff j L n (x+chartDeck k) • (chartCoefficients j L).amplitude n (x+chartDeck k))
      i *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) (x+chartDeck
        k)).re = _
  rw [chart_cutoff_periodic j L n hi k, chart_amplitude_periodic j L n hi k]
  simp only [carrier, chart_phase_periodic j L n hi k]
  rfl

theorem piece_pressure_periodic (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (piece U j L).pressure n (x+chartDeck k) = (piece U j L).pressure n x := by
  change ((chartCutoff j L n (x+chartDeck k) • (chartCoefficients j L).pressure n (x+chartDeck k)) *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) (x+chartDeck
        k)).re = _
  rw [chart_cutoff_periodic j L n hi k, chart_pressure_periodic j L n hi k]
  simp only [carrier, chart_phase_periodic j L n hi k]
  rfl

theorem piece_excluded_periodic (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint) :
    (piece U j L).excluded n (x+chartDeck k) = (piece U j L).excluded n x := by
  have hd := along_translate (chartDeck k) (chart_cutoff_periodic j L n hi k)
    (show ∀ y, (piece U j L).directions.fastField n (y+chartDeck k) =
      (piece U j L).directions.fastField n y from fun _ => rfl) x
  funext i
  change ((along ((piece U j L).directions.fastField n) (chartCutoff j L n) (x+chartDeck k) •
    (chartCoefficients j L).amplitude n (x+chartDeck k) + (1-chartCutoff j L n (x+chartDeck k)) •
      (0 : ComplexVector)) i * carrier ((chartCoefficients j L).frequency n)
      ((chartCoefficients j L).phase n) (x+chartDeck k)).re = _
  rw [hd, chart_amplitude_periodic j L n hi k, chart_cutoff_periodic j L n hi k]
  simp only [carrier, chart_phase_periodic j L n hi k]
  rfl

theorem radius_mem_of_amplitudeRadius_mem (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1)
    (hm : amplitudeRadius L (absoluteChart n x) ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    x.1.1 ∈ Icc (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.leftRadius nominal)
      (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.rightRadius nominal) := by
  have hr : 0 < x.1.1 := by
    by_contra hh
    exact amplitudeRadius_outside_nonpositive L
      (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_not_gt hh)) hm
  rw [amplitudeRadius_chart L n hT hr] at hm
  have hq : 0 < VariableGaugeMean.qLength (2*h) x.1.2.1 :=
    VariableGaugeMean.qLength_pos (by linarith [outgoing.data.h_pos])
      (by linarith [outgoing.data.h_lt_half]) hT
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hq).mp hm.1,
    by simpa only [mul_comm] using (div_le_iff₀ hq).mp hm.2⟩

theorem piece_pressure_support (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1) (hne : (piece U j L).pressure n x ≠ 0) :
    x.1.1 ∈ Icc (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.leftRadius nominal)
      (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.rightRadius nominal) := by
  apply radius_mem_of_amplitudeRadius_mem L n hT
  by_contra hh
  have hp := (absolutePair_zero_germ_outside j L (mul_pos (ChartScales.Q_pos n) hT)
      hh).2.self_of_nhds
  change absolutePressure j L (toAbsolute n x.1) = 0 at hp
  apply hne
  rw [piece_pressure_representation]
  simp [absolutePressureMode, mode, hp]

theorem piece_excluded_support (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hT : 0 < x.1.2.1.1) (hne : (piece U j L).excluded n x ≠ 0) :
    x.1.1 ∈ Icc (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.leftRadius nominal)
      (VariableGaugeMean.qLength (2*h) x.1.2.1 * PrimaryTargetBounds.rightRadius nominal) := by
  apply radius_mem_of_amplitudeRadius_mem L n hT
  by_contra hh
  have hp := (absolutePair_zero_germ_outside j L (mul_pos (ChartScales.Q_pos n) hT)
      hh).1.self_of_nhds
  change absoluteAmplitude j L (toAbsolute n x.1) = 0 at hp
  apply hne
  rw [piece_excluded_representation]
  ext i
  simp [absoluteGaussian, absoluteGaussianCoefficient, vectorMode, mode, hp]

/-! ## Tangency of the actual native pulse -/

theorem constructed_frame_normal {ι : Type} {D : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (P : PrimaryPulseBounds.PhaseConstruction D) (i : ι)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (D.slot P.V P.openV).carrier i) :
    (P.frame i).normal z = P.phase.normal i z := by
  have hB : 0 < P.B i := lt_of_lt_of_le (by linarith [P.b_pos]) (P.B_bound i).1
  have hn := (PhaseEstimates.normal_lower_bounds hB (P.K_unit i)
    (P.error_small i z hz) (P.normal_close i z hz)).2.2.1
  exact PrimaryODE.FrameData.ofNormalLocal_normal _ _ _ _ _ _ _ _ hn

theorem native_pulse_tangent (j : Fin 2) (L : Label B N0) {x : ActualSignedGeometry.Native}
    (hx : x ∈ (ActualSignedGeometry.nativeDomain certificate modulation (choice B
        N0).prepared).carrier L) :
    ⟪(phases B N0 j).phase.normal L (x.1,x.2.2), cutVelocity j L x⟫_ℝ = 0 := by
  have hz : (x.1,x.2.2) ∈
      ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).slot
        (phases B N0 j).V (phases B N0 j).openV).carrier L :=
    ⟨hx.1.1, (phases B N0 j).interval L ⟨hx.2.2.1.le, hx.2.2.2.le⟩⟩
  have htime : (phases B N0 j).L L * (pulseCoordinates L x).2 = x.2.2 := by
    change (phases B N0 0).L L * (x.2.2 / (phases B N0 0).L L) = x.2.2
    exact mul_div_cancel₀ _ ((phases B N0 0).L_pos L).ne'
  simp only [cutVelocity, rawVelocity, inner_smul_right, PrimaryPulseBounds.normalizedPulse,
    htime]
  dsimp only [pulseCoordinates]
  rw [← constructed_frame_normal (phases B N0 j) L hz]
  rw [PrimaryODE.FrameData.ambient_tangent]
  simp

theorem cutVelocity_native_mem (j : Fin 2) (L : Label B N0) {x : ActualSignedGeometry.Native}
    (hT : 0 < x.1.2.2)
    (hr : PrimaryTargetBounds.profileRadius h x.1 ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal))
    (hne : cutVelocity j L x ≠ 0) :
    x ∈ (ActualSignedGeometry.nativeDomain certificate modulation (choice B N0).prepared).carrier L
        := by
  have hraw : rawVelocity j L x ≠ 0 := by
    intro he; exact hne (by simp [cutVelocity,he])
  have hg : GaussianTailFlat.profile (pulseCoordinates L x).2 ≠ 0 := by
    intro he; exact hne (by simp [cutVelocity,gaussian,he])
  have hm : spatialMask L x.1 ≠ 0 := by
    intro he
    apply hraw
    simp [rawVelocity, PartitionedCovariance.amplitude, he]
  have hu : PartitionedCovariance.cutoff slots.radius x.2.1 ≠ 0 := by
    intro he
    apply hraw
    simp [rawVelocity, PartitionedCovariance.amplitude, he]
  apply ActualSignedGeometry.nativeCutoff_nonzero_mem certificate modulation (choice B N0).prepared
    slots.radius_pos L hT hr
  have hh := mul_ne_zero (mul_ne_zero hm hu) hg
  rw [spatialMask_eq] at hh
  exact hh

theorem cutVelocity_core (j : Fin 2) (L : Label B N0) {x : ActualSignedGeometry.Native}
    (hx : cutVelocity j L x ≠ 0) : x.2 ∈ (clockWindow L).core := by
  apply outerRawVelocity_core j L x
  intro he
  exact hx (by rw [cutVelocity_eq_outer, he, smul_zero])

theorem commonAmplitude_eq_copy (j : Fin 2) (L : Label B N0) (p : PhaseCalculus.Slow)
    (Y : TorusInverse.Plane) (k : TorusInverse.Frequency)
    (hk : cutVelocity j L (p, (geometry j L).coordinates k Y) ≠ 0) :
    commonAmplitude j L p Y =
      CurlClassBounds.complexify (cutVelocity j L (p,(geometry j L).coordinates k Y)) := by
  unfold commonAmplitude
  apply tsum_eq_single k
  intro m hmk
  have hm : cutVelocity j L (p,(geometry j L).coordinates m Y) = 0 := by
    by_contra hh
    have he := (copyCells j L).unique 0 m k (p,Y) (cutVelocity_core j L hh) (cutVelocity_core j L
        hk)
    exact hmk he
  rw [hm,map_zero]

theorem chart_radial_swap (B n : ℕ) (x : ChartPoint) :
    PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions (commonContext
        B)).radialField n x) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        (PhysicalResidualTZ.swapCylinder x) := by
  simp [PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
    PrimaryResidualClass.directions, commonContext, CommonBaseContext.context,
    CommonBaseContext.operators, CorrectionState.graphOperators,
    CommonBaseContext.reconstruction, CommonBaseContext.radialFrequency,
    LinearWaveBounds.GraphDirections.radialField, PhysicalResidualBridge.ScaledGraph.radial,
    PhysicalResidualBridge.commonGraph, GraphCalculus.radialSpeed, RadialPullback.radialJacobian,
        PhysicalGraphBounds.radialDirection, TorusInverse.vector]
  ring

theorem chart_axial_swap (B n : ℕ) (U : LocalSignedRequest.SlowRegion (2 * h)) (x : ChartPoint) :
    PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (PhysicalResidualTZ.swapCylinder x) := by
  change PhysicalResidualTZ.swapCylinder (ChartScales.Q n ^ h • (((0,((0,1),0)),0) : ChartPoint)) =
      _
  simp [PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
    PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualBridge.commonGraph]

theorem chart_normal_view (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L)) (x :
        ChartPoint) :
    (chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x =
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
          j L n (CommonWindow.index h n)) (PhysicalResidualTZ.swapCylinder x) := by
  have hp : (chartCoefficients j L).phase n = fun y =>
      1 * ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
        j L n (CommonWindow.index h n) (PhysicalResidualTZ.swapCylinder y) := by
    funext y
    simpa only [one_mul] using chartCoefficients_phase_view j L n hi y
  change phaseNormal _ _ _ _ ((chartCoefficients j L).phase n) x = _
  rw [hp]
  have he := phaseNormal_equiv
    PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv one_ne_zero
    (fun y : ChartPoint => y.1.1) PhysicalResidualBridge.ScaledGraph.radius
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (fun _ => (one_mul _).symm) (fun y => by simpa using chart_radial_swap B n y)
    (fun _ => rfl) (fun y => by simp only [one_smul]; exact chart_axial_swap B n U y) 1
    (ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
      j L n (CommonWindow.index h n)) x
  simp only [one_mul, one_smul] at he ⊢
  exact he

theorem chart_phase_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).phase n) positiveRadialChart := by
  have hm : MapsTo (absoluteChart n) positiveRadialChart positiveRadialAbsolute := by
    intro x hx
    exact ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1,
      mul_pos (ChartScales.Q_pos n) hx.2⟩
  exact ((absolutePhase_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm).div_const _

theorem chart_amplitude_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).amplitude n) positiveChart := by
  have hm : MapsTo (absoluteChart n) positiveChart positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact ((absoluteAmplitude_smooth j L).comp (absoluteChart n).contDiff.contDiffOn hm).const_smul _

theorem chart_cutoff_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiff ℝ ∞ (chartCutoff j L n) :=
  (periodicGaussian_smooth j L).comp (((toAbsolute_smooth n).comp contDiff_fst).snd)

theorem piece_domain_positive (U : LocalSignedRequest.SlowRegion (2 * h)) :
    (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)).domain ⊆
      positiveRadialChart := by
  intro x hx
  have he := (BaseContextAssembly.nativeStrip_mem nominal U x.1).mp hx
  exact ⟨BaseContextAssembly.nativeStrip_radius nominal U hx, U.time_pos _ he.1⟩

theorem piece_phase_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).phase n)
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)).domain :=
  (chart_phase_smooth j L n).mono (piece_domain_positive U)

theorem piece_amplitude_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).amplitude n)
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)).domain :=
  (chart_amplitude_smooth j L n).mono (fun _ hx => (piece_domain_positive U hx).2)

theorem chart_normal_copy (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ChartPoint)
    (hx : (nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k (toAbsolute n x.1).2) ∈
      (ActualSignedGeometry.nativeDomain certificate modulation (choice B N0).prepared).carrier L) :
    (chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x =
      PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
          L))
        (ChartScales.carrier h n) (ChartScales.carrier h (BaseChartJets.cellBand L)) •
          (phases B N0 j).phase.normal L
            (nativeSlow L (toAbsolute n x.1), ((geometry j L).coordinates k (toAbsolute n
                x.1).2).2) := by
  have hp : ActualSignedGeometry.copyPoint slots vectors_det
      (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
      n (CommonWindow.index h n) k (ActualSignedGeometry.cylinderNative
          (PhysicalResidualTZ.swapCylinder x)) =
      (nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k (toAbsolute n x.1).2) :=
    (chart_nativePoint j L n hi k x.1).symm
  have hc : ActualSignedGeometry.copyPoint slots vectors_det
      (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
      n (CommonWindow.index h n) k (ActualSignedGeometry.cylinderNative
          (PhysicalResidualTZ.swapCylinder x)) ∈
      (ActualSignedGeometry.nativeDomain certificate modulation (choice B N0).prepared).carrier L
          := by
    rwa [hp]
  have hg := (ActualSignedGeometry.preparedView_normal_germ certificate modulation slots
    (choice B N0).prepared j L n (CommonWindow.index h n) k hc).self_of_nhds
  dsimp only at hg
  rw [chart_normal_view U j L n hi x]
  refine hg.trans ?_
  erw [ActualSignedGeometry.phaseNormal_pulseCoordinates, hp]
  rfl

theorem cutAmplitude_inside (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint)
    (hr : amplitudeRadius L (absoluteChart n x) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    ((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n x =
      (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) •
          commonAmplitude j L (nativeSlow L (toAbsolute n x.1)) (toAbsolute n x.1).2 := by
  change periodicGaussian j L (toAbsolute n x.1).2 •
    (ChartScales.Q n ^ CoordinateAlgebra.A h •
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) •
        uncutAmplitude j L (nativeSlow L (toAbsolute n x.1)) (toAbsolute n x.1).2)) = _
  calc
    _ = (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) •
          (periodicGaussian j L (toAbsolute n x.1).2 •
            uncutAmplitude j L (nativeSlow L (toAbsolute n x.1)) (toAbsolute n x.1).2) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := congrArg (fun a : ComplexVector =>
      (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) • a)
      (periodic_cutoff_amplitude j L (nativeSlow L (toAbsolute n x.1)) hr (toAbsolute n x.1).2)

theorem cutAmplitude_outside (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint)
    (hr : amplitudeRadius L (absoluteChart n x) ∉
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    ((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n x = 0 := by
  have hz := absoluteAmplitude_zero_outside j L (absoluteChart n x) hr
  change chartCutoff j L n x • (ChartScales.Q n ^ CoordinateAlgebra.A h •
    absoluteAmplitude j L (absoluteChart n x).1) = 0
  rw [hz,smul_zero,smul_zero]

theorem piece_cutAmplitude_tangent (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    {x : ChartPoint} (hT : 0 < x.1.2.1.1) :
    normalDot ((chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x)
      (((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n x) = 0 := by
  classical
  by_cases hr : amplitudeRadius L (absoluteChart n x) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · rw [cutAmplitude_inside j L n x hr]
    by_cases hc : ∃ k : TorusInverse.Frequency,
        cutVelocity j L (nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k (toAbsolute
            n x.1).2) ≠ 0
    · obtain ⟨k,hk⟩ := hc
      have ht : 0 < (nativeSlow L (toAbsolute n x.1)).2.2 :=
        div_pos (mul_pos (ChartScales.Q_pos n) hT) (ChartScales.Q_pos _)
      have hm := cutVelocity_native_mem j L
        (x := (nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k (toAbsolute n x.1).2))
            ht hr hk
      rw [commonAmplitude_eq_copy j L _ _ k hk, chart_normal_copy U j L n hi k x hm,
        PhysicalParticularWave.normalDot_scaled, SignedWaveUpdate.normalDot_complexify,
        native_pulse_tangent j L hm, Complex.ofReal_zero, mul_zero]
    · push Not at hc
      have hz : commonAmplitude j L (nativeSlow L (toAbsolute n x.1)) (toAbsolute n x.1).2 = 0 := by
        simp only [commonAmplitude,hc,map_zero,tsum_zero]
      rw [hz,smul_zero]
      simp [normalDot]
  · rw [cutAmplitude_outside j L n x hr]
    simp [normalDot]


/-- Chart radius linear, given by `(ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.fst
ℝ _ ℝ)`. -/
noncomputable def chartRadiusLinear : ChartPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.fst ℝ _ ℝ)

/-- Chart radial curve, constructed using `PhysicalResidualTZ.swapCylinder`. -/
noncomputable def chartRadialCurve (n : ℕ) (r : ℝ) : ChartPoint :=
  PhysicalResidualTZ.swapCylinder
    (PhysicalCurlCovariance.ScaledGraph.radialCurve
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)) r)

theorem chartRadialCurve_smoothAt (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (chartRadialCurve n) r :=
  PhysicalResidualTZ.swapCylinder.contDiff.contDiffAt.comp r
    (PhysicalCurlCovariance.ScaledGraph.radialCurve_smoothAt _ hr)

theorem chart_radial_curve (B n : ℕ) :
    (PrimaryResidualClass.directions (commonContext B)).radialField n =
      fun x => chartRadialCurve n (chartRadiusLinear x) := by
  funext x
  apply PhysicalResidualTZ.swapCylinder.injective
  rw [chart_radial_swap]
  simp only [chartRadialCurve, PhysicalResidualTZ.swapCylinder_swapCylinder]
  rfl

theorem chart_radial_aux_derivative (B n : ℕ) {x : ChartPoint} (hx : x.1.1 ≠ 0)
    (v : ChartPoint) (hv : v.1.1 = 0) :
    fderiv ℝ ((PrimaryResidualClass.directions (commonContext B)).radialField n) x v = 0 := by
  rw [chart_radial_curve]
  change fderiv ℝ (chartRadialCurve n ∘ chartRadiusLinear) x v = 0
  rw [fderiv_comp x ((chartRadialCurve_smoothAt n hx).differentiableAt (by simp))
    chartRadiusLinear.differentiableAt, ContinuousLinearMap.fderiv]
  change fderiv ℝ (chartRadialCurve n) x.1.1 v.1.1 = 0
  rw [hv,map_zero]

theorem piece_geometry (U : LocalSignedRequest.SlowRegion (2 * h)) (B n : ℕ) :
    CurlClassBounds.CylindricalGeometry positiveRadialChart (fun x : ChartPoint => x.1.1)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n) := by
  have ha : (PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n =
      fun _ : ChartPoint => ((0,((0,ChartScales.Q n ^ h),0)),0) := by
    funext x
    change ChartScales.Q n ^ h • (((0,((0,1),0)),0) : ChartPoint) = _
    simp
  rw [ha]
  refine ⟨positiveRadialChart_open, chartRadiusLinear.contDiff.contDiffOn,
    fun _ hx => hx.1.ne', ?_, contDiffOn_const, contDiffOn_const, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chart_radial_curve]
    intro x hx
    exact ((chartRadialCurve_smoothAt n hx.1.ne').comp x
      chartRadiusLinear.contDiff.contDiffAt).contDiffWithinAt
  · intro x hx
    change fderiv ℝ chartRadiusLinear x _ = 1
    rw [ContinuousLinearMap.fderiv, chart_radial_curve]
    rfl
  · intro x hx
    change fderiv ℝ chartRadiusLinear x _ = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ chartRadiusLinear x _ = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    rw [chart_radial_aux_derivative B n hx.1.ne' _ rfl]
    simp
  · intro x hx
    rw [chart_radial_aux_derivative B n hx.1.ne' _ rfl]
    simp
  · intro x hx
    simp


theorem chart_normal_absolute (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x =
      ((1 / (ChartScales.carrier h n : ℝ)) * Real.sqrt (ChartScales.Q n)) •
        absoluteNormal j L (absoluteChart n x) := by
  change phaseNormal (fun y : ChartPoint => y.1.1)
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
    ((chartCoefficients j L).phase n) x = _
  rw [phase_representation]
  exact phaseNormal_equiv (absoluteChart n) (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne'
    _ _ _ _ _ _ _ _ (absoluteChart_radius n) (absoluteChart_radial B n)
    (absoluteChart_angular B n) (absoluteChart_axial B n U) _ _ x

theorem absoluteCutAmplitude_tangent (j : Fin 2) (L : Label B N0) {x : Absolute}
    (hx : x ∈ positiveAbsolute) :
    normalDot (absoluteNormal j L x) (absoluteCutAmplitude j L x) = 0 := by
  let n := BaseChartJets.cellBand L
  have ht : 0 < ((absoluteChart n).symm x).1.2.1.1 := div_pos hx (ChartScales.Q_pos n)
  have he := piece_cutAmplitude_tangent standardRegion j L n
    (CommonWindow.index_le_native h n) ht
  rw [chart_normal_absolute, cutAmplitude_representation] at he
  simp only [ContinuousLinearEquiv.apply_symm_apply] at he
  rw [PhysicalParticularWave.normalDot_scaled] at he
  have hK : (ChartScales.carrier h n : ℝ) ≠ 0 := (chartCoefficients_frequency_pos j L n).ne'
  have hc : (((1 / (ChartScales.carrier h n : ℝ)) * Real.sqrt (ChartScales.Q n) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (one_div_ne_zero hK)
      (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne')
  have ha : ((ChartScales.Q n ^ CoordinateAlgebra.A h : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).ne'
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hc ha)

/-- Tangency holds on every band.  A valid native cover proves it first,
then the exact absolute normal and amplitude laws remove any index restriction. -/
theorem piece_tangent (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hx : x ∈ positiveChart) :
    normalDot ((chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x)
      (((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n x) = 0 := by
  rw [chart_normal_absolute, cutAmplitude_representation, PhysicalParticularWave.normalDot_scaled,
    absoluteCutAmplitude_tangent j L (mul_pos (ChartScales.Q_pos n) hx), mul_zero]

theorem piece_normal_ne (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hx : x ∈ positiveRadialChart) :
    (chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n x ≠ 0 := by
  rw [chart_normal_absolute]
  apply smul_ne_zero
  · exact mul_ne_zero (one_div_ne_zero (chartCoefficients_frequency_pos j L n).ne')
      (Real.sqrt_pos.mpr (ChartScales.Q_pos n)).ne'
  · exact absoluteNormal_ne j L ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1,
      mul_pos (ChartScales.Q_pos n) hx.2⟩

theorem piece_exactAmplitude_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).exactCoefficients.amplitude n) positiveRadialChart := by
  have hm : MapsTo (absoluteChart n) positiveRadialChart positiveRadialAbsolute := by
    intro x hx
    exact ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1,
      mul_pos (ChartScales.Q_pos n) hx.2⟩
  exact (((absoluteExactAmplitude_smooth j L).comp (absoluteChart n).contDiff.contDiffOn
      hm).const_smul
    (ChartScales.Q n ^ CoordinateAlgebra.A h)).congr
      (fun x _ => exactAmplitude_representation U j L n x)

theorem piece_complexVelocity_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (vectorMode ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase
        n)
      ((piece U j L).exactCoefficients.amplitude n)) positiveRadialChart := by
  apply contDiffOn_pi.mpr
  intro i
  exact HarmonicCalculus.contDiffOn_mode _ (chart_phase_smooth j L n)
    (contDiffOn_pi.mp (piece_exactAmplitude_smooth U j L n) i)

theorem piece_complex_divergence (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hx : x ∈ positiveRadialChart) :
    cylindricalDivergence (fun y : ChartPoint => y.1.1)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
      (vectorMode ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n)
        ((piece U j L).exactCoefficients.amplitude n)) x = 0 := by
  exact CurlClassBounds.realizedCoefficient_divergence (piece_geometry U B n)
    (chartCoefficients_frequency_pos j L n).ne' (chart_phase_smooth j L n)
    ((chart_cutoff_smooth j L n).contDiffOn.smul
      ((chart_amplitude_smooth j L n).mono (fun _ hy => hy.2)))
    (fun _ hy => piece_normal_ne U j L n hy) (fun _ hy => piece_tangent U j L n hy.2) hx

/-- Literal real corrected field, with the radial connection term included. -/
theorem piece_full_divergence (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint}
    (hx : x ∈ positiveRadialChart) :
    cylindricalDivergence (fun y : ChartPoint => y.1.1)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
      (fun y i => ((piece U j L).velocity n y i : ℂ)) x = 0 := by
  change cylindricalDivergence _ _ _ _
    (fun y i => PrimaryResidualClass.realProjection
      (vectorMode ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n)
        ((piece U j L).exactCoefficients.amplitude n) y i)) x = 0
  rw [PrimaryResidualClass.divergence_map PrimaryResidualClass.realProjection _ _ _ _
    (fun i => ((contDiffOn_pi.mp (piece_complexVelocity_smooth U j L n) i).contDiffAt
      (positiveRadialChart_open.mem_nhds hx)).differentiableAt (by simp)),
    piece_complex_divergence U j L n hx, map_zero]

/-- The absolute free lift evaluated on the actual physical cylindrical graph. -/
noncomputable def physicalLift (z : ProblemStatement.SpaceTime) : Absolute :=
  (((z.2 0, (z.2 2, 1-z.1)),
    (z.2 0)^ChartScales.radialExponent h • PhysicalGraphBounds.radialDirection +
      z.1 • PhysicalGraphBounds.timeDirection), z.2 1)

theorem absoluteChart_physical (n : ℕ) {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    absoluteChart n (PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z)) =
      physicalLift z := by
  apply (absoluteChart n).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, PhysicalResidualBridge.commonGraph_eq_physicalToChart
      h n _ hr,
    MeanChartCompatibility.physicalToChart_apply, MeanChartCompatibility.coverMap_eq_coverPower]
  simp only [absoluteChart_symm_apply, fromAbsolute, physicalLift,
      PhysicalResidualBridge.absoluteLift,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
        MeanChartCompatibility.chartScale,
    Real.rpow_neg (ChartScales.Q_pos n).le, Real.rpow_one, Real.sqrt_eq_rpow, div_eq_mul_inv]
  ext <;> ring

/-- Physical phase, defined pointwise by `absolutePhase j L (physicalLift z)`. -/
noncomputable def physicalPhase (j : Fin 2) (L : Label B N0) : ProblemStatement.SpaceTime → ℝ :=
  fun z => absolutePhase j L (physicalLift z)

/-- Physical amplitude, defined pointwise by `absoluteCutAmplitude j L (physicalLift z)`. -/
noncomputable def physicalAmplitude (j : Fin 2) (L : Label B N0) : ProblemStatement.SpaceTime →
    ComplexVector :=
  fun z => absoluteCutAmplitude j L (physicalLift z)

/-- Lifted phase, defined pointwise by `(chartCoefficients j L).phase n
(PhysicalResidualTZ.swapCylinder x)`. -/
noncomputable def liftedPhase (j : Fin 2) (L : Label B N0) (n : ℕ) : ChartPoint → ℝ :=
  fun x => (chartCoefficients j L).phase n (PhysicalResidualTZ.swapCylinder x)

/-- Lifted amplitude, defined pointwise by `((chartCoefficients j L).withCutoff (chartCutoff j
L)).amplitude n (PhysicalResidualTZ.swapCylinder x)`. -/
noncomputable def liftedAmplitude (j : Fin 2) (L : Label B N0) (n : ℕ) : ChartPoint → ComplexVector
    :=
  fun x => ((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n
    (PhysicalResidualTZ.swapCylinder x)

/-- Lifted domain, given by `PhysicalResidualTZ.swapCylinder ⁻¹' positiveRadialChart`. -/
noncomputable def liftedDomain : Set ChartPoint :=
  PhysicalResidualTZ.swapCylinder ⁻¹' positiveRadialChart

theorem liftedDomain_open : IsOpen liftedDomain :=
  positiveRadialChart_open.preimage PhysicalResidualTZ.swapCylinder.continuous

theorem liftedPhase_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (liftedPhase j L n) liftedDomain :=
  (chart_phase_smooth j L n).comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn
    (fun _ hx => hx)

theorem liftedAmplitude_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (liftedAmplitude j L n) liftedDomain := by
  have hc : ContDiffOn ℝ ∞
      (((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n) positiveRadialChart :=
    (chart_cutoff_smooth j L n).contDiffOn.smul
      ((chart_amplitude_smooth j L n).mono (fun _ hx => hx.2))
  exact hc.comp PhysicalResidualTZ.swapCylinder.contDiff.contDiffOn (fun _ hx => hx)

theorem chart_normal_lifted (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (chartCoefficients j L).normal (piece U j L).strip (piece U j L).directions n
        (PhysicalResidualTZ.swapCylinder x) =
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (liftedPhase j L n) x := by
  have he := phaseNormal_equiv PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv one_ne_zero
    (fun y : ChartPoint => y.1.1) PhysicalResidualBridge.ScaledGraph.radius
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (fun _ => (one_mul _).symm) (fun y => by simpa using chart_radial_swap B n y)
    (fun _ => rfl) (fun y => by simp only [one_smul]; exact chart_axial_swap B n U y) 1
    (liftedPhase j L n) (PhysicalResidualTZ.swapCylinder x)
  simp only [liftedPhase, one_mul, one_smul] at he ⊢
  exact he

theorem lifted_realized (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) (x : ChartPoint) :
    (piece U j L).exactCoefficients.amplitude n (PhysicalResidualTZ.swapCylinder x) =
      CurlClassBounds.realizedCoefficient ((chartCoefficients j L).frequency n)
        PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (liftedPhase j L n) (liftedAmplitude j L n) x := by
  have he := realizedCoefficient_equiv PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv
    one_ne_zero one_ne_zero (chartCoefficients_frequency_pos j L n).ne' (mul_one _)
    (fun y : ChartPoint => y.1.1) PhysicalResidualBridge.ScaledGraph.radius
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField (piece U j L).strip n)
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (fun _ => (one_mul _).symm) (fun y => by simpa using chart_radial_swap B n y)
    (fun _ => rfl) (fun y => by simp only [one_smul]; exact chart_axial_swap B n U y) 1
    (liftedPhase j L n) (liftedAmplitude j L n) (PhysicalResidualTZ.swapCylinder x)
  simp only [liftedPhase, liftedAmplitude, one_mul, one_smul] at he ⊢
  exact he

theorem physicalPhase_eq (j : Fin 2) (L : Label B N0) (n : ℕ)
    {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    physicalPhase j L z = (chartCoefficients j L).frequency n * liftedPhase j L n
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z) :=
          by
  rw [liftedPhase, chartCoefficients_phase]
  exact congrArg (absolutePhase j L) (absoluteChart_physical n hr).symm

theorem physicalAmplitude_eq (j : Fin 2) (L : Label B N0) (n : ℕ)
    {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    physicalAmplitude j L z = ChartScales.Q n ^ (-CoordinateAlgebra.A h) • liftedAmplitude j L n
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z) :=
          by
  rw [liftedAmplitude, cutAmplitude_representation]
  dsimp only
  rw [absoluteChart_physical n hr, smul_smul,
    ← Real.rpow_add (ChartScales.Q_pos n), neg_add_cancel, Real.rpow_zero, one_smul]
  rfl

/-- Physical angular, given by `(0,ProblemStatement.coordinateVector 1)`. -/
noncomputable def physicalAngular : ProblemStatement.SpaceTime :=
  (0,ProblemStatement.coordinateVector 1)

theorem physicalLift_angular (z : ProblemStatement.SpaceTime) (s : ℝ) :
    physicalLift (z+s • physicalAngular) = physicalLift z + s • ((0 : AbsolutePoint),1) := by
  ext <;> simp [physicalLift, physicalAngular, ProblemStatement.coordinateVector]

theorem physicalPhase_angular (j : Fin 2) (L : Label B N0) :
    CopyAngularInvariance.AffinePhase physicalAngular
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L : ℝ)
      (physicalPhase j L) := by
  intro x t
  exact (congrArg (absolutePhase j L) (physicalLift_angular x t)).trans
    (absolutePhase_angular j L (physicalLift x) t)

theorem physicalAmplitude_angular (j : Fin 2) (L : Label B N0) :
    CopyAngularInvariance.Invariant physicalAngular (physicalAmplitude j L) := by
  intro x t
  change absoluteCutAmplitude j L (physicalLift (x+t • physicalAngular)) = _
  rw [physicalLift_angular]
  simp [absoluteCutAmplitude,physicalAmplitude]

/-- Physical potential, given by `PhysicalCurlCovariance.referencePotential 1 (physicalPhase j
L) (physicalAmplitude j L)`. -/
noncomputable def physicalPotential (j : Fin 2) (L : Label B N0) :
    ProblemStatement.SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential 1 (physicalPhase j L) (physicalAmplitude j L)

theorem physicalPotential_periodic (j : Fin 2) (L : Label B N0) (t r z : ℝ) :
    Periodic (fun θ => physicalPotential j L (t,AxisymmetricResidual.pack r θ z)) (2*Real.pi) := by
  have hR : CopyAngularInvariance.Invariant physicalAngular LinearWaveResidual.coordinateRadius :=
      by
    intro x s
    simp [physicalAngular, LinearWaveResidual.coordinateRadius, ProblemStatement.coordinateVector]
  have hturn := PhysicalCurlCovariance.vectorPotential_fullTurn
    (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j L)
    hR (CopyAngularInvariance.Invariant.const (0,ProblemStatement.coordinateVector 0))
    (CopyAngularInvariance.Invariant.const physicalAngular)
    (CopyAngularInvariance.Invariant.const (0,ProblemStatement.coordinateVector 2))
    (physicalPhase_angular j L) (physicalAmplitude_angular j L) (one_mul _)
  intro θ
  have hp : ((t,AxisymmetricResidual.pack r θ z) : ProblemStatement.SpaceTime) +
      (2*Real.pi) • physicalAngular = (t,AxisymmetricResidual.pack r (θ+2*Real.pi) z) := by
    apply Prod.ext
    · simp [physicalAngular]
    · ext i
      fin_cases i <;> simp [physicalAngular, ProblemStatement.coordinateVector]
  have he := hturn (t,AxisymmetricResidual.pack r θ z)
  simp only [hp] at he
  exact he

/-- One fixed radius for each original label, chosen from its actual
physical scale and the positive inner support radius. -/
noncomputable def physicalAxisRadius (L : Label B N0) : ℝ :=
  Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) * PrimaryTargetBounds.leftRadius nominal / 4

theorem physicalAxisRadius_pos (L : Label B N0) : 0 < physicalAxisRadius L :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos _)) (PrimaryTargetBounds.leftRadius_pos
      nominal))
    (by norm_num)

theorem absoluteAmplitude_zero_mask (j : Fin 2) (L : Label B N0) (x : AbsolutePoint)
    (hx : spatialMask L (nativeSlow L x) = 0) : absoluteAmplitude j L x = 0 := by
  have hraw (Y : TorusInverse.Plane) : rawVelocity j L (nativeSlow L x,Y) = 0 := by
    simp [rawVelocity, PartitionedCovariance.amplitude, hx]
  have hsum : uncutAmplitude j L (nativeSlow L x) x.2 = 0 := by
    unfold uncutAmplitude
    have hh (k : TorusInverse.Frequency) :
        attachedRawVelocity j L (nativeSlow L x, (geometry j L).coordinates k x.2) = 0 := by
      simp [attachedRawVelocity, WaveEdgeExtension.nativeExtension, WaveEdgeExtension.extension,
        outerRawVelocity, hraw]
    simp only [hh,map_zero,tsum_zero]
  simp [absoluteAmplitude,hsum]

theorem physicalAmplitude_zero_axis (j : Fin 2) (L : Label B N0) (z : ProblemStatement.SpaceTime)
    (hz : z.2 0 ≤ physicalAxisRadius L) : physicalAmplitude j L z = 0 := by
  have hr : amplitudeRadius L (physicalLift z) ∉
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) ∨
      spatialMask L (nativeSlow L (physicalLift z).1) = 0 := by
    by_cases hm : spatialMask L (nativeSlow L (physicalLift z).1) = 0
    · exact Or.inr hm
    left
    have hq := (spatialMask_q_range L _ hm).1
    have hs : 1/2 < Real.sqrt (SimilarityCoordinates.coordinateQ (2*h)
      ((nativeSlow L (physicalLift z).1).2.2,(nativeSlow L (physicalLift z).1).2.1)) := by
      apply (Real.lt_sqrt (by norm_num)).2
      linarith
    have hu : (nativeSlow L (physicalLift z).1).1 ≤ PrimaryTargetBounds.leftRadius nominal / 4 := by
      change z.2 0 / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) ≤ _
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (ChartScales.Q_pos _))).2
      convert! hz using 1
      unfold physicalAxisRadius
      ring
    intro hx
    have hx1 := hx.1
    simp only [amplitudeRadius, PrimaryTargetBounds.profileRadius,
        BaseChartJets.normalizedCoordinates_eq,
      SimilarityHomogeneity.chartQ] at hx1
    have hn := (lt_div_iff₀ (lt_trans (by norm_num : (0:ℝ)<1/2) hs)).mp hx1
    have hp := PrimaryTargetBounds.leftRadius_pos nominal
    nlinarith
  have he : absoluteAmplitude j L (physicalLift z).1 = 0 := by
    rcases hr with hr | hr
    · exact absoluteAmplitude_zero_outside j L (physicalLift z) hr
    · exact absoluteAmplitude_zero_mask j L (physicalLift z).1 hr
  simp [physicalAmplitude, absoluteCutAmplitude, he]

theorem physicalPotential_zero_axis (j : Fin 2) (L : Label B N0) (z : ProblemStatement.SpaceTime)
    (hz : z.2 0 ≤ physicalAxisRadius L) : physicalPotential j L z = 0 := by
  have ha := physicalAmplitude_zero_axis j L z hz
  ext i
  simp [physicalPotential, PhysicalCurlCovariance.referencePotential,
    CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross,ha]


theorem periodic_value_of_polar_eq {E : Type} (f : TorusInverse.Plane → E)
    (hf : ∀ r, Periodic (fun θ => f (r, θ)) (2 * Real.pi))
    {r θ : ℝ} (hr : r ≠ 0) {q : TorusInverse.Plane} (hqr : q.1 = r)
    (hq : PolarCharts.polar q = PolarCharts.polar (r, θ)) : f q = f (r,θ) := by
  have hc : Real.cos q.2 = Real.cos θ := by
    apply mul_left_cancel₀ hr
    simpa only [PolarCharts.polar,hqr] using congrArg Prod.fst hq
  have hs : Real.sin q.2 = Real.sin θ := by
    apply mul_left_cancel₀ hr
    simpa only [PolarCharts.polar,hqr] using congrArg Prod.snd hq
  obtain ⟨n,hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
  have he : q.2 = θ+n*(2*Real.pi) := by nlinarith [hn]
  rw [← Prod.eta q,hqr,he]
  exact ((hf r).int_mul n) θ

/-- The complete periodic potential gives a forward representation at every
positive cylindrical radius, including angles outside the chosen inverse chart. -/
theorem globalPotential_forward {a : ℝ} (ha : 0 < a)
    (B : ProblemStatement.SpaceTime → ComplexVector)
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t,AxisymmetricResidual.pack r θ z)) (2*Real.pi))
    (hzero : ∀ z : ProblemStatement.SpaceTime, z.2 0 ≤ a → B z = 0)
    {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    PhysicalCurlCovariance.globalCartesianPotential a B (z.1,CylindricalResidual.chart z.2) =
      CylindricalResidual.frame (z.2 1) (PhysicalCurlCovariance.realVector (B z)) := by
  classical
  have he : PhysicalGraphBounds.radialProjection (z.1,CylindricalResidual.chart z.2) =
      PolarCharts.polar (z.2 0,z.2 1) := by
    simp [PhysicalGraphBounds.radialProjection_apply,CylindricalResidual.chart,PolarCharts.polar]
  by_cases hc : ∃ j : PolarCharts.Index, PolarCharts.polar (z.2 0,z.2 1) ∈ PolarCharts.chartDomain
      a j
  · obtain ⟨j,hj⟩ := hc
    rw [PhysicalCurlCovariance.globalCartesianPotential_eq_local ha B hper j (by
        simpa only [he] using hj)]
    let f : TorusInverse.Plane → ProblemStatement.Space := fun p =>
      CylindricalResidual.frame p.2 (PhysicalCurlCovariance.realVector
        (B (z.1,AxisymmetricResidual.pack p.1 p.2 (z.2 2))))
    have hf (r : ℝ) : Periodic (fun θ => f (r,θ)) (2*Real.pi) := by
      intro θ
      dsimp only [f]
      rw [PhysicalCurlCovariance.frame_periodic θ]
      have he := hper z.1 r (z.2 2) θ
      dsimp only at he
      rw [he]
    have hqr : (PolarCharts.chart a j (PolarCharts.polar (z.2 0,z.2 1))).1 = z.2 0 := by
      rw [PolarCharts.chart_eq_localChart ha j hj,PolarCharts.localChart_apply,
        PolarCharts.radius_polar,abs_of_pos hr]
    have hp := periodic_value_of_polar_eq f hf hr.ne' hqr (PolarCharts.polar_chart ha j hj)
    have hpack : AxisymmetricResidual.pack (z.2 0) (z.2 1) (z.2 2) = z.2 := by
      ext i
      fin_cases i <;> simp
    calc
      _ = f (PolarCharts.chart a j (PolarCharts.polar (z.2 0,z.2 1))) := by
        simp only [PhysicalCurlCovariance.cartesianPotential,
            PhysicalCurlCovariance.polarCoordinates,
          PhysicalCurlCovariance.polarInput,he,f]
        simp only [CylindricalResidual.chart,AxisymmetricResidual.pack_two]
      _ = f (z.2 0,z.2 1) := hp
      _ = _ := by dsimp only [f]; rw [hpack]
  · have hn : ‖PolarCharts.polar (z.2 0,z.2 1)‖ ≤ a/4 := by
      obtain ⟨j,hj⟩ := PolarCharts.exists_rotate_fst_ge (p := PolarCharts.polar (z.2 0,z.2 1))
          le_rfl
      apply le_of_not_gt
      intro hh
      exact hc ⟨j,lt_of_lt_of_le hh hj⟩
    have hz : z.2 0 ≤ a := by
      have hb := PolarCharts.radius_le_two_norm (PolarCharts.polar (z.2 0,z.2 1))
      rw [PolarCharts.radius_polar,abs_of_pos hr] at hb
      linarith
    have hc' : ¬∃ j : PolarCharts.Index,
        PhysicalGraphBounds.radialProjection (z.1,CylindricalResidual.chart z.2) ∈
            PolarCharts.chartDomain a j := by
      simpa only [he] using hc
    rw [PhysicalCurlCovariance.globalCartesianPotential,dite_eq_right hc',hzero z hz]
    have hp : AxisymmetricResidual.pack 0 0 0 = (0 : ProblemStatement.Space) := by
      ext i
      fin_cases i <;> simp
    simp [PhysicalCurlCovariance.realVector,hp]

theorem globalPotential_forward_germ {a : ℝ} (ha : 0 < a)
    (B : ProblemStatement.SpaceTime → ComplexVector)
    (hper : ∀ t r z : ℝ, Periodic (fun θ => B (t,AxisymmetricResidual.pack r θ z)) (2*Real.pi))
    (hzero : ∀ z : ProblemStatement.SpaceTime, z.2 0 ≤ a → B z = 0)
    {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    (fun y => PhysicalCurlCovariance.globalCartesianPotential a B (y.1,CylindricalResidual.chart
        y.2)) =ᶠ[𝓝 z]
      (fun y => CylindricalResidual.frame (y.2 1) (PhysicalCurlCovariance.realVector (B y))) :=
  eventually_of_mem ((isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection
      0).continuous).mem_nhds hr)
    (fun _ hy => globalPotential_forward ha B hper hzero hy)


/-! ## One actual Cartesian potential for every primary label -/

theorem physical_source (n : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hr : 0 < z.2 0) :
    z ∈ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).source
        liftedDomain := by
  refine ⟨hr,?_⟩
  change (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z ∈
      liftedDomain
  rw [PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos n) h _ hr]
  change 0 < ChartScales.Q n ^ (-(1/2:ℝ)) * z.2 0 ∧ 0 < (1-z.1) / ChartScales.Q n
  exact ⟨mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr,
    div_pos (sub_pos.mpr ht) (ChartScales.Q_pos n)⟩

theorem liftedNormal_ne (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint} (hx : x ∈
    liftedDomain) :
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
      (liftedPhase j L n) x ≠ 0 := by
  rw [← chart_normal_lifted standardRegion j L n x]
  exact piece_normal_ne standardRegion j L n hx

theorem lifted_tangent (j : Fin 2) (L : Label B N0) (n : ℕ) {x : ChartPoint} (hx : x ∈
    liftedDomain) :
    normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
      (liftedPhase j L n) x) (liftedAmplitude j L n x) = 0 := by
  rw [← chart_normal_lifted standardRegion j L n x]
  exact piece_tangent standardRegion j L n hx.2

theorem liftedPotential_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (CurlClassBounds.vectorPotential ((chartCoefficients j L).frequency n)
      PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
      (liftedPhase j L n) (liftedAmplitude j L n)) liftedDomain :=
  CurlClassBounds.vectorPotential_contDiffOn
    (PhysicalCurlCovariance.ScaledGraph.geometry _ liftedDomain_open (fun _ hx => hx.1.ne')) _
    (liftedPhase_smooth j L n) (liftedAmplitude_smooth j L n) (fun _ hx => liftedNormal_ne j L n hx)

theorem physicalPotential_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (physicalPotential j L) {z : ProblemStatement.SpaceTime | z.1 < 1 ∧ 0 < z.2 0}
        := by
  have he := PhysicalCurlCovariance.referencePotential_eq_on (ChartScales.Q_pos 0) h
      (CommonWindow.index h 0)
    liftedDomain_open one_ne_zero (chartCoefficients_frequency_pos j L 0).ne'
    (liftedPhase_smooth j L 0) (liftedAmplitude j L 0) (physicalPhase j L) (physicalAmplitude j L)
    (fun z hz => by simpa only [one_mul] using physicalPhase_eq j L 0 hz.1)
    (fun z hz => physicalAmplitude_eq j L 0 hz.1)
  intro z hz
  have hs := physical_source 0 hz.1 hz.2
  have hm := (PhysicalResidualBridge.commonGraph (ChartScales.Q 0) h (CommonWindow.index h
      0)).map_smoothAt
    (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos 0) _) hz.2).ne'
  have hc := ((liftedPotential_smooth j L 0).contDiffAt (liftedDomain_open.mem_nhds hs.2)).comp z hm
  apply ContDiffAt.contDiffWithinAt
  apply (hc.const_smul (ChartScales.Q 0 ^ (-h))).congr_of_eventuallyEq
  exact eventually_of_mem
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q 0) h (CommonWindow.index h 0)).source_open
      (Real.rpow_pos_of_pos (ChartScales.Q_pos 0) _) liftedDomain_open |>.mem_nhds hs)
    (fun _ hy => he hy)

/-- No band index occurs in this Cartesian potential.  The cutoff is the
original periodic Gaussian, and the polar chart is chosen from its full-turn-compatible values. -/
noncomputable def cartesianPotential (j : Fin 2) (L : Label B N0) : ProblemStatement.VelocityField
    :=
  PhysicalCurlCovariance.globalCartesianPotential (physicalAxisRadius L) (physicalPotential j L)

/-- Cartesian velocity, given by `SpatialCurl.spatialCurl (cartesianPotential j L)`. -/
noncomputable def cartesianVelocity (j : Fin 2) (L : Label B N0) : ProblemStatement.VelocityField :=
  SpatialCurl.spatialCurl (cartesianPotential j L)

theorem cartesianPotential_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (cartesianPotential j L) {z : ProblemStatement.SpaceTime | z.1 < 1} :=
  (PhysicalCurlCovariance.globalCartesianPotential_smoothOn (physicalAxisRadius_pos L) isOpen_Iio
    (physicalPotential_smooth j L) (physicalPotential_periodic j L) (physicalPotential_zero_axis j
        L)).mono
      (fun _ hz => ⟨hz,trivial⟩)

theorem cartesianVelocity_axis_zero (j : Fin 2) (L : Label B N0) (t : ℝ) (x :
    ProblemStatement.Space)
    (hx : x 0 = 0) (hy : x 1 = 0) : cartesianVelocity j L (t,x) = 0 := by
  apply PhysicalCurlCovariance.spatialCurl_zero_of_zero_near
  apply PhysicalCurlCovariance.globalCartesianPotential_zero_germ (physicalAxisRadius_pos L)
    (physicalPotential_zero_axis j L)
  simpa only [PhysicalGraphBounds.radialProjection_apply,PolarCharts.radius,hx,hy,
    zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_zero] using physicalAxisRadius_pos L

/-- Every actual band velocity is the rotating-frame representation of
the curl of the same constructed Cartesian potential.  This includes all
positive radii and all angles, without a native-cover restriction. -/
theorem piece_cartesian_velocity (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {z : ProblemStatement.SpaceTime}
    (ht : z.1 < 1) (hr : 0 < z.2 0) (i : Fin 3) :
    (piece U j L).velocity n (PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z)) i =
      ChartScales.Q n ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
        (cartesianVelocity j L (z.1,CylindricalResidual.chart z.2)) i := by
  have hA : DifferentiableAt ℝ (cartesianPotential j L) (z.1,CylindricalResidual.chart z.2) :=
    ((cartesianPotential_smooth j L).contDiffAt (x := (z.1,CylindricalResidual.chart z.2))
      ((isOpen_lt continuous_fst continuous_const).mem_nhds ht)).differentiableAt (by simp)
  have he := globalPotential_forward_germ (physicalAxisRadius_pos L) (physicalPotential j L)
    (physicalPotential_periodic j L) (physicalPotential_zero_axis j L) hr
  have hc := PhysicalCurlCovariance.reference_correctedWave (ChartScales.Q_pos n) h
      (CommonWindow.index h n)
    liftedDomain_open (fun _ hx => hx.1.ne') one_ne_zero (chartCoefficients_frequency_pos j L n).ne'
    (liftedPhase_smooth j L n) (liftedAmplitude_smooth j L n)
    (fun _ hx => liftedNormal_ne j L n hx) (fun _ hx => lifted_tangent j L n hx)
    (physicalPhase j L) (physicalAmplitude j L)
    (fun z hz => by simpa only [one_mul] using physicalPhase_eq j L n hz.1)
    (fun z hz => physicalAmplitude_eq j L n hz.1) (physical_source n ht hr) hA he i
  change ((piece U j L).exactCoefficients.amplitude n _ i *
    carrier ((chartCoefficients j L).frequency n) ((chartCoefficients j L).phase n) _).re = _
  rw [lifted_realized U j L n]
  exact hc

/-- Physical pressure, defined pointwise by `absolutePressureMode j L (physicalLift z)`. -/
noncomputable def physicalPressure (j : Fin 2) (L : Label B N0) : ProblemStatement.SpaceTime → ℝ :=
  fun z => absolutePressureMode j L (physicalLift z)

theorem piece_physical_pressure (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {z : ProblemStatement.SpaceTime} (hr : 0 < z.2 0) :
    (piece U j L).pressure n (PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z)) =
      ChartScales.Q n ^ (2*CoordinateAlgebra.A h) * physicalPressure j L z := by
  rw [piece_pressure_representation]
  change ChartScales.Q n ^ (2*CoordinateAlgebra.A h) *
    absolutePressureMode j L (absoluteChart n _) = _
  rw [absoluteChart_physical n hr]
  rfl

theorem cartesianVelocity_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (cartesianVelocity j L) {z : ProblemStatement.SpaceTime | z.1 < 1} := by
  have ha : ContDiffOn ℝ ∞ (cartesianPotential j L) ((Iio 1) ×ˢ (univ : Set
      ProblemStatement.Space)) :=
    (cartesianPotential_smooth j L).mono (fun _ hx => hx.1)
  exact (SpatialCurl.contDiffOn_spatialCurl ha (by simp)).mono (fun _ hx => ⟨hx,trivial⟩)

theorem cartesianVelocity_divergence (j : Fin 2) (L : Label B N0) {t : ℝ}
    (ht : t < 1) (x : ProblemStatement.Space) :
    ProblemStatement.spatialDivergence (cartesianVelocity j L) t x = 0 := by
  have ha : ContDiffOn ℝ 2 (cartesianPotential j L) ((Iio 1) ×ˢ (univ : Set
      ProblemStatement.Space)) :=
    ((cartesianPotential_smooth j L).mono (fun _ hx => hx.1)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact SpatialCurl.spatialDivergence_spatialCurl_on ha ht x

end NavierStokes.ActualPrimaryCoherence
