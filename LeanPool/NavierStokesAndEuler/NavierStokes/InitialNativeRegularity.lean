/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence

@[expose] public section

/-!
# Full-chart regularity of the initial native copy coefficients

The copied fields use the actual flat radial attachment.  Their regularity
holds across its boundary, rather than only inside the native estimate
domain.  The stripped coefficients are independent of the angular variable.
-/

noncomputable section

namespace NavierStokes.InitialNativeRegularity

open Set Function Filter
open CorrectionInitialization ActualPrimaryBounds
open scoped ContDiff Topology BigOperators

abbrev Point := ActualPrimary.FullPoint
abbrev Frequency := TorusInverse.Frequency

variable {B N0 : ℕ}

/-- The same copied amplitude used by `InitialPhysicalData`. -/
noncomputable def copyAmplitude (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : HarmonicCalculus.ComplexVector :=
  copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n k (nativeOfFull x)

/-- The pressure scaling exponent is twice the velocity exponent. -/
noncomputable def copyPressureCoefficient (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : ℂ :=
  copied (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n k (nativeOfFull x)

/-- The actual inverse-carrier potential formed from the copied amplitude. -/
noncomputable def copyPotentialCoefficient (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : Point) : HarmonicCalculus.ComplexVector :=
  CurlClassBounds.inverseCarrier ((cutCoefficients l).frequency n) •
    CurlClassBounds.normalCoefficient
      ((cutCoefficients l).normal fullStrip (directions B) n x)
      (copyAmplitude l k n x)

theorem gaussian_smooth (l : SignedLabel B N0) :
    ContDiff ℝ ∞ (ActualPrimary.gaussian l.2) :=
  GaussianTailFlat.profile_contDiff.comp (contDiff_snd.snd.div_const _)

/-- The radial-edge attachment is used before taking the copy. -/
theorem cutNativeVelocity_smooth (l : SignedLabel B N0) :
    ContDiffOn ℝ ∞ (cutNativeVelocity l) WaveEdgeExtension.nativeSlowDomain :=
  (gaussian_smooth l).contDiffOn.smul
    ((ActualPrimary.attachedRawVelocity_smooth B N0 l.1 l.2).continuousLinearMap_comp
      CurlClassBounds.complexify)

theorem cutNativePressure_smooth (l : SignedLabel B N0) :
    ContDiffOn ℝ ∞ (cutNativePressure l) WaveEdgeExtension.nativeSlowDomain :=
  (gaussian_smooth l).contDiffOn.smul (ActualPrimary.attachedRawPressure_smooth B N0 l.1 l.2)

theorem copyPoint_mapsTo (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    MapsTo (fun x : Point => copyPoint l n k (nativeOfFull x))
      ActualPrimaryCoherence.positiveChart WaveEdgeExtension.nativeSlowDomain := by
  intro x hx
  change 0 < (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
    (ChartScales.Q (spatialLabel l).1) (nativeOfFull x).1).2.2
  exact ActualSignedGeometry.slowChange_time (ChartScales.Q_pos n) (ChartScales.Q_pos _) hx

/-- The band cutoff is discrete.  In active bands the copy map preserves
positive native time, and in all other bands the field is identically zero. -/
theorem copied_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → Native → E)
    (hf : ∀ l, ContDiffOn ℝ ∞ (f l) WaveEdgeExtension.nativeSlowDomain)
    (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x : Point => copied a f l n k (nativeOfFull x))
      ActualPrimaryCoherence.positiveChart := by
  classical
  by_cases hn : near l n
  · simp only [copied, ite_eq_left hn]
    exact ((hf l).comp ((copyPoint_smooth l n k).comp nativeOfFull.contDiff).contDiffOn
      (copyPoint_mapsTo l k n)).const_smul _
  · simp only [copied, ite_eq_right hn]
    exact contDiffOn_const

theorem copyAmplitude_smooth (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    ContDiffOn ℝ ∞ (copyAmplitude l k n) ActualPrimaryCoherence.positiveChart :=
  copied_smooth _ cutNativeVelocity cutNativeVelocity_smooth l k n

/-- This holds on the larger positive-time chart, including zero radius. -/
theorem copyPressureCoefficient_smooth (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    ContDiffOn ℝ ∞ (copyPressureCoefficient l k n) ActualPrimaryCoherence.positiveChart :=
  copied_smooth _ cutNativePressure cutNativePressure_smooth l k n

theorem cutNormal_eq (l : SignedLabel B N0) (n : ℕ) :
    (cutCoefficients l).normal fullStrip (directions B) n =
      (ActualPrimary.chartCoefficients l.1 l.2).normal fullStrip (directions B) n := by
  simp only [cutCoefficients, LinearWaveBounds.WaveCoefficients.withCutoff,
    LinearWaveBounds.WaveCoefficients.normal]

theorem normal_eq_absolute (l : SignedLabel B N0) (n : ℕ) :
    (cutCoefficients l).normal fullStrip (directions B) n = fun x =>
      ((1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) * Real.sqrt (ChartScales.Q n)) •
        ActualPrimaryCoherence.absoluteNormal l.1 l.2 (ActualPrimaryCoherence.absoluteChart n x) :=
          by
  rw [cutNormal_eq]
  funext x
  simpa only [ActualPrimary.piece, fullStrip, strip, directions] using
    (ActualPrimaryCoherence.chart_normal_absolute (B := B) (N0 := N0) region l.1 l.2 n x)

theorem normal_smooth (l : SignedLabel B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((cutCoefficients l).normal fullStrip (directions B) n)
      ActualPrimaryCoherence.positiveRadialChart := by
  rw [normal_eq_absolute]
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n)
      ActualPrimaryCoherence.positiveRadialChart ActualPrimaryCoherence.positiveRadialAbsolute := by
    intro x hx
    exact ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1,
      mul_pos (ChartScales.Q_pos n) hx.2⟩
  exact ((ActualPrimaryCoherence.absoluteNormal_smooth l.1 l.2).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul _

theorem normal_ne (l : SignedLabel B N0) (n : ℕ) {x : Point}
    (hx : x ∈ ActualPrimaryCoherence.positiveRadialChart) :
    (cutCoefficients l).normal fullStrip (directions B) n x ≠ 0 := by
  rw [cutNormal_eq]
  simpa only [ActualPrimary.piece, fullStrip, strip, directions] using
    (ActualPrimaryCoherence.piece_normal_ne (B := B) (N0 := N0) region l.1 l.2 n hx)

/-- Joint smoothness includes every radial support boundary at positive
radius and time.  There is no interior-support restriction. -/
theorem copyPotentialCoefficient_smooth (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    ContDiffOn ℝ ∞ (copyPotentialCoefficient l k n)
      ActualPrimaryCoherence.positiveRadialChart :=
  (CurlClassBounds.normalCoefficient_contDiffOn (normal_smooth l n)
    ((copyAmplitude_smooth l k n).mono (fun _ hx => hx.2))
    (fun _ hx => normal_ne l n hx)).const_smul _

theorem copyPressureCoefficient_smooth_radial (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    ContDiffOn ℝ ∞ (copyPressureCoefficient l k n)
      ActualPrimaryCoherence.positiveRadialChart :=
  (copyPressureCoefficient_smooth l k n).mono (fun _ hx => hx.2)

/-- The true phase is affine in angle, so its actual phase normal is
angle-independent even where derivatives are defined by totalization. -/
theorem normal_invariant (l : SignedLabel B N0) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : LocalSignedRequest.Point), 1)
      ((cutCoefficients l).normal fullStrip (directions B) n) := by
  let h := ActualPrimary.chartCoefficients_angular l.1 l.2
  obtain ⟨m, hm⟩ := h.phase n
  exact CopyAngularInvariance.phaseNormal_invariant (h.radius n)
    (PrimaryResidualClass.directions_radial_invariant (ActualPrimary.commonContext B) n)
    (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _) hm

theorem copyAmplitude_invariant (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : LocalSignedRequest.Point), 1) (copyAmplitude l k n) :=
  PrimaryResidualClass.invariant_fst (fun y => copied (CoordinateAlgebra.A ActualPrimary.h)
    cutNativeVelocity l n k (ActualSignedGeometry.meanEquiv.symm y))

theorem copyPressureCoefficient_invariant (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : LocalSignedRequest.Point), 1)
      (copyPressureCoefficient l k n) :=
  PrimaryResidualClass.invariant_fst (fun y => copied (2 * CoordinateAlgebra.A ActualPrimary.h)
    cutNativePressure l n k (ActualSignedGeometry.meanEquiv.symm y))

theorem copyPotentialCoefficient_invariant (l : SignedLabel B N0) (k : Frequency) (n : ℕ) :
    CopyAngularInvariance.Invariant ((0 : LocalSignedRequest.Point), 1)
      (copyPotentialCoefficient l k n) :=
  ((normal_invariant l n).map₂ (copyAmplitude_invariant l k n)
    CurlClassBounds.normalCoefficient).map
      (fun z => CurlClassBounds.inverseCarrier ((cutCoefficients l).frequency n) • z)

theorem copyAmplitude_angle (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : LocalSignedRequest.Point) (θ : ℝ) :
    copyAmplitude l k n (x, θ) = copyAmplitude l k n (x, 0) :=
  CopyAngularInvariance.invariant_eq_zeroSlice (copyAmplitude_invariant l k n) x θ

theorem copyPressureCoefficient_angle (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : LocalSignedRequest.Point) (θ : ℝ) :
    copyPressureCoefficient l k n (x, θ) = copyPressureCoefficient l k n (x, 0) :=
  CopyAngularInvariance.invariant_eq_zeroSlice (copyPressureCoefficient_invariant l k n) x θ

theorem copyPotentialCoefficient_angle (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : LocalSignedRequest.Point) (θ : ℝ) :
    copyPotentialCoefficient l k n (x, θ) = copyPotentialCoefficient l k n (x, 0) :=
  CopyAngularInvariance.invariant_eq_zeroSlice (copyPotentialCoefficient_invariant l k n) x θ

end NavierStokes.InitialNativeRegularity
