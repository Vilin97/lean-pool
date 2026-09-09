/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalSignedRequest
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualNaturality
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicPhaseAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling

/-!
# Signed quotient waves from one physical primary reference

The signed numerator is the actual current-state stress request.  All
band views use the same absolute-lift primary pulse and covariance
matrix.  Compatibility is proved before restriction to a physical graph.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalSignedWave

open Set Function Filter Matrix HarmonicCalculus WeightedClasses
open ProblemStatement CommonCoverSolve TorusInverse
open scoped ContDiff Topology InnerProductSpace BigOperators

/-- Mat2: an abbreviation for `SmoothCovariance.Mat2`. -/
abbrev Mat2 := SmoothCovariance.Mat2
/-- Vec2: an abbreviation for `SmoothCovariance.Vec2`. -/
abbrev Vec2 := SmoothCovariance.Vec2
/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Cylinder: an abbreviation for `PhysicalResidualBridge.Cylinder`. -/
abbrev Cylinder := PhysicalResidualBridge.Cylinder

/-- Fast translate, given by `((x.1.1, (x.1.2.1, x.1.2.2 + TorusAverages.latticePoint k)),
x.2)`. -/
noncomputable def fastTranslate (x : Cylinder) (k : TorusInverse.Frequency) : Cylinder :=
  ((x.1.1, (x.1.2.1, x.1.2.2 + TorusAverages.latticePoint k)), x.2)

section QuotientAlgebra

theorem weights_smul_target (H : Mat2) (T : Vec2) (a : ℝ) :
    SmoothCovariance.weights H (a • T) = a • SmoothCovariance.weights H T := by
  ext j
  fin_cases j <;> simp [SmoothCovariance.weights, SmoothCovariance.cramerNumerator,
    Pi.smul_apply, smul_eq_mul] <;> ring

theorem inverse_smul_target (H : Mat2) (T : Vec2) (a : ℝ) :
    H⁻¹.mulVec (a • T) = a • H⁻¹.mulVec T := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

theorem amplitudes_square_scale (H : Mat2) (T : Vec2) {a : ℝ} (ha : 0 ≤ a) :
    SmoothCovariance.amplitudes H (a ^ 2 • T) = a • SmoothCovariance.amplitudes H T := by
  ext j
  simp only [SmoothCovariance.amplitudes, weights_smul_target, Pi.smul_apply, smul_eq_mul]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Both the signed numerator and the original primary target acquire the
same squared scale.  The quotient is therefore multiplied by the positive
scale, including points where its totalized denominator is zero. -/
theorem increment_square_scale (H : Mat2) (T R : Vec2) {a : ℝ} (ha : 0 < a) (j : Fin 2) :
    SignedCovariance.increment H (a ^ 2 • T) (a ^ 2 • R) j =
      a * SignedCovariance.increment H T R j := by
  simp only [SignedCovariance.increment, inverse_smul_target,
    amplitudes_square_scale H T ha.le, Pi.smul_apply, smul_eq_mul]
  by_cases hb : SmoothCovariance.amplitudes H T j = 0
  · simp only [hb, mul_zero, div_zero]
  · field_simp

/-- Coefficient scale, given by `velocityScale * Real.sqrt referenceEpsilon / Real.sqrt
epsilon`. -/
noncomputable def coefficientScale (epsilon referenceEpsilon velocityScale : ℝ) : ℝ :=
  velocityScale * Real.sqrt referenceEpsilon / Real.sqrt epsilon

theorem coefficientScale_pos {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) :
    0 < coefficientScale epsilon referenceEpsilon velocityScale :=
  div_pos (mul_pos hv (Real.sqrt_pos.mpr hr)) (Real.sqrt_pos.mpr he)

theorem coefficientScale_square {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 ≤ referenceEpsilon) :
    coefficientScale epsilon referenceEpsilon velocityScale ^ 2 =
      velocityScale ^ 2 * referenceEpsilon / epsilon := by
  unfold coefficientScale
  rw [div_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt he.le]

theorem sqrt_mul_coefficientScale {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) :
    Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale =
      velocityScale * Real.sqrt referenceEpsilon := by
  unfold coefficientScale
  field_simp

/-- The primary square root and the signed inverse quotient have exactly
the same velocity scaling.  The matrix and column are unchanged. -/
theorem primary_scalar_scale (H : Mat2) (T : Vec2) (mask : ℝ)
    {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) (j : Fin 2) :
    PartitionedCovariance.amplitude epsilon mask H
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • T) j =
      velocityScale * PartitionedCovariance.amplitude referenceEpsilon mask H T j := by
  unfold PartitionedCovariance.amplitude
  rw [amplitudes_square_scale H T (coefficientScale_pos he hr hv).le]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := sqrt_mul_coefficientScale (referenceEpsilon := referenceEpsilon)
    (velocityScale := velocityScale) he
  calc
    _ = (Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale) *
        SmoothCovariance.amplitudes H T j * mask := by ring
    _ = _ := by rw [h]; ring

theorem signed_scalar_scale (H : Mat2) (T R : Vec2) (mask : ℝ)
    {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) (j : Fin 2) :
    Real.sqrt epsilon * SignedCovariance.increment H
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • T)
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • R) j * mask =
      velocityScale * (Real.sqrt referenceEpsilon * SignedCovariance.increment H T R j * mask) := by
  rw [increment_square_scale H T R (coefficientScale_pos he hr hv)]
  have h := sqrt_mul_coefficientScale (referenceEpsilon := referenceEpsilon)
    (velocityScale := velocityScale) he
  calc
    _ = (Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale) *
        SignedCovariance.increment H T R j * mask := by ring
    _ = _ := by rw [h]; ring

/-- With request twice the target, the literal signed quotient is exactly
the primary square root. This also holds at totalized zero denominators. -/
theorem increment_twice_target (H : Mat2) (T : Vec2) (j : Fin 2) :
    SignedCovariance.increment H T ((2 : ℝ) • T) j = SmoothCovariance.amplitudes H T j := by
  by_cases hd : H.det = 0
  · have hi : H⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit H (by simp [hd])
    simp [SignedCovariance.increment, hi, SmoothCovariance.amplitudes,
      SmoothCovariance.weights, hd]
  · rw [SignedCovariance.increment, inverse_smul_target,
      SmoothCovariance.inverse_formula H T hd]
    simp only [Pi.smul_apply, smul_eq_mul, SmoothCovariance.amplitudes]
    by_cases hw : 0 ≤ SmoothCovariance.weights H T j
    · by_cases hz : SmoothCovariance.weights H T j = 0
      · simp [hz]
      · have hp : 0 < SmoothCovariance.weights H T j := lt_of_le_of_ne hw (Ne.symm hz)
        apply (div_eq_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hp).ne')).2
        nlinarith [Real.sq_sqrt hw]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hw)]
      simp

end QuotientAlgebra

/-! ## A concrete periodic reference phase with native clock germs -/

/-- Reference phase data, collecting `geometry`, `window`, `epsilon`, `axialFrequency`,
`radialFrequency`, `angularMode` and their compatibility conditions. -/
structure ReferencePhase where
  /-- Geometry of `ReferencePhase`, of type `CommonCoverSolve.Geometry`. -/
  geometry : CommonCoverSolve.Geometry
  /-- Window of `ReferencePhase`, of type `PeriodicPhaseAssembly.ClockWindow`. -/
  window : PeriodicPhaseAssembly.ClockWindow
  /-- Epsilon of `ReferencePhase`, of type `ℝ`. -/
  epsilon : ℝ
  /-- Axial frequency of `ReferencePhase`, of type `ℝ`. -/
  axialFrequency : ℝ
  /-- Radial frequency of `ReferencePhase`, of type `ℝ`. -/
  radialFrequency : ℝ
  /-- Angular mode of `ReferencePhase`, of type `ℤ`. -/
  angularMode : ℤ
  /-- F of `ReferencePhase`, of type `PeriodicPhaseAssembly.Parameter → ℝ`. -/
  F : PeriodicPhaseAssembly.Parameter → ℝ
  /-- Geometric data of `ReferencePhase`, of type `PeriodicPhaseAssembly.Parameter → ℝ`. -/
  G : PeriodicPhaseAssembly.Parameter → ℝ

namespace ReferencePhase

variable (C : ReferencePhase)

/-- Phase, constructed using `PeriodicPhaseAssembly.angularLift`. -/
noncomputable def phase (K : ℝ) (x : Cylinder) : ℝ :=
  PeriodicPhaseAssembly.angularLift
    (PeriodicPhaseAssembly.profilePhase C.geometry C.window.cutoff C.epsilon
      (C.angularMode / K) C.axialFrequency C.radialFrequency C.F C.G)
    (C.angularMode / K) (PhysicalParticularWave.waveEquiv x)

/-- Native phase, constructed using `PhaseCalculus.phase`. -/
noncomputable def nativePhase (K : ℝ) (copy : TorusInverse.Frequency) (x : Cylinder) : ℝ :=
  PhaseCalculus.phase C.epsilon (C.angularMode / K) C.axialFrequency C.radialFrequency
    (fun p => C.F (p.1, (p.2.2, p.2.1))) (fun p => C.G (p.1, (p.2.2, p.2.1)))
    ((x.1.1, x.1.2.1), (x.2, (C.geometry.coordinates copy x.1.2.2).2))

theorem phase_affine (K : ℝ) :
    CopyAngularInvariance.AffinePhase (0, 1) (C.angularMode / K) (C.phase K) := by
  intro x t
  simp only [phase, PeriodicPhaseAssembly.angularLift, PhysicalParticularWave.waveEquiv_apply,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero,
    smul_eq_mul, mul_one]
  ring

theorem phase_periodic (K : ℝ) (x : Cylinder) (k : TorusInverse.Frequency) :
    C.phase K (fastTranslate x k) = C.phase K x := by
  exact PeriodicPhaseAssembly.fullPhase_periodic C.geometry C.window.cutoff
    (PeriodicPhaseAssembly.profileIntercept C.epsilon C.axialFrequency C.radialFrequency)
    (PeriodicPhaseAssembly.profileRate (C.angularMode / K) C.axialFrequency C.F C.G)
    (C.angularMode / K) (x.1.1, (x.1.2.1.2, x.1.2.1.1)) x.2 x.1.2.2 k

theorem phase_native_germ (K : ℝ)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => C.geometry.center + C.geometry.basis z) '' C.window.outer))
    (copy : TorusInverse.Frequency) {x : Cylinder}
    (hx : C.geometry.coordinates copy x.1.2.2 ∈ C.window.core) :
    C.phase K =ᶠ[𝓝 x] C.nativePhase K copy := by
  have he := PeriodicPhaseAssembly.profilePhase_germ C.geometry C.window hinj C.epsilon
    (C.angularMode / K) C.axialFrequency C.radialFrequency C.F C.G copy
    (x := PhysicalParticularWave.waveEquiv x) hx
  exact he.comp_tendsto PhysicalParticularWave.waveEquiv.continuous.continuousAt

theorem phase_native_jets (K : ℝ)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => C.geometry.center + C.geometry.basis z) '' C.window.outer))
    (copy : TorusInverse.Frequency) {x : Cylinder}
    (hx : C.geometry.coordinates copy x.1.2.2 ∈ C.window.core) (m : ℕ) :
    iteratedFDeriv ℝ m (C.phase K) x = iteratedFDeriv ℝ m (C.nativePhase K copy) x :=
  PeriodizedWaveBounds.jets_eq_of_germ (C.phase_native_germ K hinj copy hx) m

theorem phase_smooth (K : ℝ) (hF : ContDiff ℝ ∞ C.F) (hG : ContDiff ℝ ∞ C.G) :
    ContDiff ℝ ∞ (C.phase K) := by
  apply (PeriodicPhaseAssembly.angularLift_contDiff ?_ _).comp
    PhysicalParticularWave.waveEquiv.contDiff
  exact PeriodicPhaseAssembly.phase_contDiff C.geometry C.window
    ((contDiff_const.mul contDiff_snd.snd).add (contDiff_const.mul contDiff_fst))
    ((contDiff_const.mul hF).add (contDiff_const.mul hG))

/-- Base, given by `{ a with phase := fun n => C.phase (a.frequency n) }`. -/
noncomputable def base (a : LinearWaveBounds.WaveCoefficients Cylinder) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  { a with phase := fun n => C.phase (a.frequency n) }

end ReferencePhase

section ActualRequest

/-- The primitive is taken from the actual current-state residual on
every radius and fast coordinate of the stated slow fiber.  Graph-only
agreement is not used in this theorem. -/
theorem fullRequest_chart (s sr : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord coordr : ℝ) (c cr : CorrectionState.Context Point)
    (u ur : CorrectionState.State Point) (n nr : ℕ)
    {l : ℝ} (hl : 0 < l) (C : LocalSignedRequest.Plane →L[ℝ] LocalSignedRequest.Plane)
    (gap : ℕ) (sourceScale : ℝ) (t : LocalSignedRequest.Plane)
    (hq : 0 < SimilarityCoordinates.coordinateQ coord t)
    {V : Set LocalSignedRequest.Plane} (hV : IsOpen V) (ht : C t ∈ V)
    (hθ : ContDiffOn ℝ ∞ (ur.thetaResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hz : ContDiffOn ℝ ∞ (ur.axialResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hpθ : PhysicalMeanDomain.PeriodicOn V (ur.thetaResidual cr nr))
    (hpz : PhysicalMeanDomain.PeriodicOn V (ur.axialResidual cr nr))
    (hlength : Real.sqrt (SimilarityCoordinates.coordinateQ coordr (C t)) =
      l * Real.sqrt (SimilarityCoordinates.coordinateQ coord t))
    (heθ : ∀ r Y, u.thetaResidual c n (r, (t, Y)) =
      sourceScale * ur.thetaResidual cr nr (l * r, (C t, TemporalMeanUpdate.coverMap gap Y)))
    (hez : ∀ r Y, u.axialResidual c n (r, (t, Y)) =
      sourceScale * ur.axialResidual cr nr (l * r, (C t, TemporalMeanUpdate.coverMap gap Y)))
    (r : ℝ) (Y : LocalSignedRequest.Plane) (angle : ℝ) :
    LocalSignedRequest.fullRequest s P coord c u n ((r, (t, Y)), angle) =
      (sourceScale / l * sr.epsilon nr / s.epsilon n) •
        LocalSignedRequest.fullRequest sr P coordr cr ur nr
          ((l * r, (C t, TemporalMeanUpdate.coverMap gap Y)), angle) := by
  have h1 := LocalSignedRequest.physicalBarSigma_chart P 2 hl hq C gap sourceScale
    hV ht hθ hpθ hlength heθ r
  have h2 := LocalSignedRequest.physicalBarSigma_chart P 1 hl hq C gap sourceScale
    hV ht hz hpz hlength hez r
  have hn := (s.epsilon_pos n).ne'
  have hr := (sr.epsilon_pos nr).ne'
  ext j
  fin_cases j
  · simp [LocalSignedRequest.fullRequest, LocalSignedRequest.normalizedRequest,
      LocalSignedRequest.requestedStress, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, h1];
    field_simp [hl.ne']
  · simp [LocalSignedRequest.fullRequest, LocalSignedRequest.normalizedRequest,
      LocalSignedRequest.requestedStress, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_one, h2];
    field_simp [hl.ne']

theorem source_over_radial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    PhysicalParticularWave.sourceWeight h Q Qr / PhysicalParticularWave.ratioPower Q Qr (1 / 2) =
      PhysicalParticularWave.velocityWeight h Q Qr ^ 2 := by
  unfold PhysicalParticularWave.sourceWeight PhysicalParticularWave.velocityWeight
  rw [PhysicalParticularWave.ratioPower_div hQ hQr, pow_two,
    PhysicalParticularWave.ratioPower_mul hQ hQr]
  congr 1
  ring

theorem physical_request_factor {Q Qr epsilon referenceEpsilon : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (he : 0 < epsilon) (hr : 0 ≤ referenceEpsilon) (h : ℝ) :
    (PhysicalParticularWave.sourceWeight h Q Qr /
      PhysicalParticularWave.ratioPower Q Qr (1 / 2)) * referenceEpsilon / epsilon =
      coefficientScale epsilon referenceEpsilon (PhysicalParticularWave.velocityWeight h Q Qr) ^ 2
          := by
  rw [coefficientScale_square he hr, source_over_radial hQ hQr]

end ActualRequest

/-! ## The actual current-state request on the full free lift -/

/-- Slow change as an element of `LocalSignedRequest.Plane →L[ℝ] LocalSignedRequest.Plane`. -/
noncomputable def slowChange (h Q Qr : ℝ) : LocalSignedRequest.Plane →L[ℝ] LocalSignedRequest.Plane
    :=
  ((PhysicalParticularWave.ratioPower Q Qr 1) • ContinuousLinearMap.id ℝ ℝ).prodMap
    ((PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h)) • ContinuousLinearMap.id ℝ ℝ)

/-- Request chart as an element of `Point ≃L[ℝ] Point`. -/
noncomputable def requestChart (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) : Point ≃L[ℝ] Point :=
  (PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv.trans
    (PhysicalResidualNaturality.chartEquiv h hQ hQr gap)).trans
      PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv

theorem requestChart_apply (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) (x : Point) :
    requestChart h hQ hQr gap x =
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2) * x.1,
        (slowChange h Q Qr x.2.1, TemporalMeanUpdate.coverMap gap x.2.2)) := by
  rw [MeanChartCompatibility.coverMap_eq_coverPower]
  rfl

theorem ratioPower_eq_div_rpow {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (p : ℝ) :
    PhysicalParticularWave.ratioPower Q Qr p = (Q / Qr) ^ p := by
  exact (Real.div_rpow hQ.le hQr.le p).symm

theorem slowChange_coordinateQ {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQr : 0 < Qr) {t : LocalSignedRequest.Plane} (ht : 0 < t.1) :
    SimilarityCoordinates.coordinateQ (2 * h) (slowChange h Q Qr t) =
      (Q / Qr) * SimilarityCoordinates.coordinateQ (2 * h) t := by
  have he := SimilarityHomogeneity.coordinateQ_scale_h hh hh1 (div_pos hQ hQr) ht (z := t.2)
  change SimilarityCoordinates.coordinateQ (2 * h)
      (PhysicalParticularWave.ratioPower Q Qr 1 * t.1,
        PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h) * t.2) = _
  simpa only [ratioPower_eq_div_rpow hQ hQr, Real.rpow_one] using he

theorem slowChange_length {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQr : 0 < Qr) {t : LocalSignedRequest.Plane} (ht : 0 < t.1) :
    Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (slowChange h Q Qr t)) =
      PhysicalParticularWave.ratioPower Q Qr (1 / 2) *
        Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) t) := by
  rw [slowChange_coordinateQ hh hh1 hQ hQr ht, Real.sqrt_mul (div_pos hQ hQr).le,
    Real.sqrt_eq_rpow, ratioPower_eq_div_rpow hQ hQr]

/-- The strip and input coordinates are moved together. Its epsilon is
definitionally the epsilon of the same full-angle wave strip. -/
noncomputable def stateStrip (s : StripData Cylinder) : StripData Point :=
  SignedWaveUpdate.sectionStrip (ParticularWaveBounds.reindexStrip PhysicalResidualTZ.swapCylinder
      s)

/-- State request, defined pointwise by `LocalSignedRequest.fullRequest (stateStrip s) P (2 * h)
c u n (PhysicalResidualTZ.swapCylinder x)`. -/
noncomputable def stateRequest (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ℕ → Cylinder → Vec2 :=
  fun n x => LocalSignedRequest.fullRequest (stateStrip s) P (2 * h) c u n
    (PhysicalResidualTZ.swapCylinder x)

theorem stateRequest_invariant (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (n : ℕ) :
    CopyAngularInvariance.Invariant (0, 1) (stateRequest s P h c u n) := by
  intro x t
  simp [stateRequest, LocalSignedRequest.fullRequest, PhysicalResidualTZ.swapCylinder_apply]

/-- Naturality of the actual request is a consequence of primitive
current-state and background coherence on an open free-lift neighborhood
containing the whole integration fiber. No residual or quotient
compatibility is a hypothesis. -/
theorem fullRequest_of_state (s sr : StripData Point) (P : SignedStressPrimitive.Patch)
    {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQr : 0 < Qr)
    (c cr : CorrectionState.Context Point) (u ur : CorrectionState.State Point)
    (n nr gap : ℕ) {W : Set Point} (hW : IsOpen W)
    (H : PhysicalResidualNaturality.StateOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) u ur n nr)
    (G : PhysicalResidualNaturality.ContextOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) c cr n nr)
    (t : LocalSignedRequest.Plane) (ht : 0 < t.1)
    (hfiber : ∀ r Y, (r, (t, Y)) ∈ W)
    {V : Set LocalSignedRequest.Plane} (hV : IsOpen V) (htV : slowChange h Q Qr t ∈ V)
    (hθ : ContDiffOn ℝ ∞ (ur.thetaResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hz : ContDiffOn ℝ ∞ (ur.axialResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hpθ : PhysicalMeanDomain.PeriodicOn V (ur.thetaResidual cr nr))
    (hpz : PhysicalMeanDomain.PeriodicOn V (ur.axialResidual cr nr))
    (r : ℝ) (Y : LocalSignedRequest.Plane) (angle : ℝ) :
    LocalSignedRequest.fullRequest s P (2 * h) c u n ((r, (t, Y)), angle) =
      coefficientScale (s.epsilon n) (sr.epsilon nr)
        (PhysicalParticularWave.velocityWeight h Q Qr) ^ 2 •
      LocalSignedRequest.fullRequest sr P (2 * h) cr ur nr
        (requestChart h hQ hQr gap (r, (t, Y)), angle) := by
  have hl := PhysicalParticularWave.ratioPower_pos hQ hQr (1 / 2)
  have hθeq (r : ℝ) (Y : LocalSignedRequest.Plane) := H.thetaResidual G hW hl.ne' (r, (t, Y))
      (hfiber r Y)
  have hzeq (r : ℝ) (Y : LocalSignedRequest.Plane) := H.axialResidual G hW hl.ne' (r, (t, Y))
      (hfiber r Y)
  simp only [requestChart_apply, PhysicalResidualNaturality.weight_source hQ hQr] at hθeq hzeq
  have he := fullRequest_chart s sr P (2 * h) (2 * h) c cr u ur n nr hl
    (slowChange h Q Qr) gap (PhysicalParticularWave.sourceWeight h Q Qr) t
    (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) ht).1 hV htV hθ hz hpθ hpz
    (slowChange_length hh hh1 hQ hQr ht) hθeq hzeq r Y angle
  rw [physical_request_factor hQ hQr (s.epsilon_pos n) (sr.epsilon_pos nr).le] at he
  simpa only [requestChart_apply] using he

theorem stateRequest_of_state (s sr : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQr : 0 < Qr)
    (c cr : CorrectionState.Context Point) (u ur : CorrectionState.State Point)
    (n nr gap : ℕ) {W : Set Point} (hW : IsOpen W)
    (H : PhysicalResidualNaturality.StateOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) u ur n nr)
    (G : PhysicalResidualNaturality.ContextOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) c cr n nr)
    (x : Cylinder) (ht : 0 < x.1.2.1.2)
    (hfiber : ∀ r Y, (r, ((x.1.2.1.2, x.1.2.1.1), Y)) ∈ W)
    {V : Set LocalSignedRequest.Plane} (hV : IsOpen V)
    (htV : slowChange h Q Qr (x.1.2.1.2, x.1.2.1.1) ∈ V)
    (hθ : ContDiffOn ℝ ∞ (ur.thetaResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hz : ContDiffOn ℝ ∞ (ur.axialResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hpθ : PhysicalMeanDomain.PeriodicOn V (ur.thetaResidual cr nr))
    (hpz : PhysicalMeanDomain.PeriodicOn V (ur.axialResidual cr nr)) :
    stateRequest s P h c u n x =
      coefficientScale (s.epsilon n) (sr.epsilon nr)
        (PhysicalParticularWave.velocityWeight h Q Qr) ^ 2 •
      stateRequest sr P h cr ur nr (PhysicalParticularWave.cylinderChange h Q Qr gap x) := by
  have he := fullRequest_of_state (stateStrip s) (stateStrip sr) P hh hh1 hQ hQr c cr u ur n nr gap
    hW H G (x.1.2.1.2, x.1.2.1.1) ht hfiber hV htV hθ hz hpθ hpz x.1.1 x.1.2.2 x.2
  exact he

section CoefficientTransport

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact pointwise transport of the literal signed quotient coefficient
from primitive matrix, targets, mask and primary fundamental identities. -/
theorem signedVector_transport (s : StripData D) (sr : StripData E)
    (H : ℕ → D → Mat2) (Hr : ℕ → E → Mat2)
    (T R : ℕ → D → Vec2) (Tr Rr : ℕ → E → Vec2)
    (mask : ℕ → D → ℝ) (maskr : ℕ → E → ℝ)
    (v : ℕ → D → Space) (vr : ℕ → E → Space)
    (n nr : ℕ) (x : D) (xr : E) {c : ℝ} (hc : 0 < c)
    (hH : H n x = Hr nr xr)
    (hT : T n x = coefficientScale (s.epsilon n) (sr.epsilon nr) c ^ 2 • Tr nr xr)
    (hR : R n x = coefficientScale (s.epsilon n) (sr.epsilon nr) c ^ 2 • Rr nr xr)
    (hm : mask n x = maskr nr xr) (hv : v n x = vr nr xr) (j : Fin 2) :
    SignedWaveUpdate.signedVector s H T R mask v j n x =
      c • SignedWaveUpdate.signedVector sr Hr Tr Rr maskr vr j nr xr := by
  simp only [SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    hH, hT, hR, hm, hv]
  rw [signed_scalar_scale (Hr nr xr) (Tr nr xr) (Rr nr xr) (maskr nr xr)
    (s.epsilon_pos n) (sr.epsilon_pos nr) hc j]
  rw [smul_smul]

theorem homogeneousPressure_scale (K Kr rate c normalScale : ℝ)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (hs : normalScale ≠ 0)
    (N Ndot v Av : Space) :
    Complex.I * (TangentProjection.pressureCoefficient (normalScale • N)
      ((normalScale * rate) • Ndot) (c • v) ((rate * c) • Av) 0 : ℂ) / (K : ℂ) =
        ((rate * c / normalScale) * (Kr / K)) •
          (Complex.I * (TangentProjection.pressureCoefficient N Ndot v Av 0 : ℂ) / (Kr : ℂ)) := by
  have hk : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hkr : (Kr : ℂ) ≠ 0 := by exact_mod_cast hKr
  have hns : (normalScale : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [show (0 : Space) = (rate * c) • (0 : Space) by simp,
    NormalScaling.pressureCoefficient_rescale N Ndot v Av 0 rate c hs]
  simp only [smul_zero, Complex.ofReal_mul, Complex.ofReal_div, Complex.real_smul]
  field_simp

end CoefficientTransport

/-! ## One actual primary pulse family, reused in every view -/

/-- Only primary construction data and background fields are stored.
The pulse, covariance matrix, square roots and signed quotients are all
computed by the existing constructors. -/
structure PrimaryData (U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow) where
  /-- Strip of `PrimaryData`, of type `StripData Cylinder`. -/
  strip : StripData Cylinder
  /-- Base of `PrimaryData`, of type `LinearWaveBounds.WaveCoefficients Cylinder`. -/
  base : LinearWaveBounds.WaveCoefficients Cylinder
  /-- Directions of `PrimaryData`, of type `LinearWaveBounds.GraphDirections Cylinder`. -/
  directions : LinearWaveBounds.GraphDirections Cylinder
  /-- Pulse of `PrimaryData`, of type `Fin 2 → PrimaryPulseBounds.PhaseConstruction U`. -/
  pulse : Fin 2 → PrimaryPulseBounds.PhaseConstruction U
  /-- Prefactor of `PrimaryData`, of type `Fin 2 → ℕ → ℝ`. -/
  prefactor : Fin 2 → ℕ → ℝ
  /-- Coordinate of `PrimaryData`, of type `ℕ → Cylinder → PhaseCalculus.Slow × ℝ`. -/
  coordinate : ℕ → Cylinder → PhaseCalculus.Slow × ℝ
  /-- Target of `PrimaryData`, of type `ℕ → Cylinder → Vec2`. -/
  target : ℕ → Cylinder → Vec2
  /-- Mask of `PrimaryData`, of type `ℕ → Cylinder → ℝ`. -/
  mask : ℕ → Cylinder → ℝ
  /-- Normal motion of `PrimaryData`, of type `ℕ → Cylinder → Space`. -/
  normalMotion : ℕ → Cylinder → Space
  /-- Action of `PrimaryData`, of type `ℕ → Cylinder → Space →L[ℝ] Space`. -/
  action : ℕ → Cylinder → Space →L[ℝ] Space

namespace PrimaryData

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (B : PrimaryData U)

/-- With reference phase, given by `{ B with base := C.base B.base }`. -/
noncomputable def withReferencePhase (C : ReferencePhase) : PrimaryData U :=
  { B with base := C.base B.base }

/-- Matrix, given by `SignedWaveUpdate.phaseMatrix B.pulse B.prefactor B.coordinate`. -/
noncomputable def matrix : ℕ → Cylinder → Mat2 :=
  SignedWaveUpdate.phaseMatrix B.pulse B.prefactor B.coordinate

/-- Fundamental, given by `SignedWaveUpdate.phaseFundamental B.pulse B.coordinate j`. -/
noncomputable def fundamental (j : Fin 2) : ℕ → Cylinder → Space :=
  SignedWaveUpdate.phaseFundamental B.pulse B.coordinate j

/-- The single Gaussian slot cutoff of this primary pulse. -/
noncomputable def cutoff (n : ℕ) (x : Cylinder) : ℝ :=
  GaussianTailFlat.profile (B.coordinate n x).2

/-- Coefficients, constructed using `SignedWaveUpdate.coefficients`. -/
noncomputable def coefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients B.base B.strip B.directions B.matrix B.target request B.mask
    (B.fundamental j) B.normalMotion B.action j

/-- Primary vector, given by `PartitionedCovariance.amplitude (B.strip.epsilon n) (B.mask n x)
(B.matrix n x) (B.target n x) j • B.fundamental j n x`. -/
noncomputable def primaryVector (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  PartitionedCovariance.amplitude (B.strip.epsilon n) (B.mask n x) (B.matrix n x)
    (B.target n x) j • B.fundamental j n x

/-- Primary coefficients, given by `SignedWaveUpdate.homogeneousCoefficients B.base B.strip
B.directions (B.primaryVector j) B.normalMotion B.action`. -/
noncomputable def primaryCoefficients (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.homogeneousCoefficients B.base B.strip B.directions
    (B.primaryVector j) B.normalMotion B.action

/-- Primary request, defined pointwise by `(2 : ℝ) • B.target n x`. -/
noncomputable def primaryRequest : ℕ → Cylinder → Vec2 := fun n x => (2 : ℝ) • B.target n x

theorem primaryVector_eq_signed (j : Fin 2) :
    B.primaryVector j = SignedWaveUpdate.signedVector B.strip B.matrix B.target B.primaryRequest
      B.mask (B.fundamental j) j := by
  funext n x
  simp only [primaryVector, SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    primaryRequest, increment_twice_target, PartitionedCovariance.amplitude]

theorem primaryCoefficients_eq_signed (j : Fin 2) :
    B.primaryCoefficients j = B.coefficients B.primaryRequest j := by
  unfold primaryCoefficients coefficients SignedWaveUpdate.coefficients
  rw [B.primaryVector_eq_signed j]

/-- The primary uses the actual normalized Volterra pulse. Its Gaussian
factor is inserted exactly once, after the primary square root. -/
theorem primary_cutoff_amplitude (j : Fin 2) (n : ℕ) (x : Cylinder) :
    ((B.primaryCoefficients j).withCutoff B.cutoff).amplitude n x =
      PartitionedCovariance.amplitude (B.strip.epsilon n) (B.mask n x)
        (B.matrix n x) (B.target n x) j •
      CurlClassBounds.complexify (PrimaryPulseBounds.cutoffPulse ((B.pulse j).frame n)
        ((B.pulse j).lam n) ((B.pulse j).u n) ((B.pulse j).L n) (B.coordinate n x)) := by
  simp only [primaryCoefficients, SignedWaveUpdate.homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, primaryVector, cutoff,
    PrimaryPulseBounds.cutoffPulse, fundamental, SignedWaveUpdate.phaseFundamental, map_smul]
  exact smul_comm _ _ _

/-- The same reference carrier is pulled back before multiplication by
the target band's frequency. All other background fields remain inputs. -/
noncomputable def viewBase (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder) (reference : ℕ) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  { background with
    frequency := frequency
    phase := fun n x => (B.base.frequency reference / frequency n) *
      B.base.phase reference (view n x) }

/-- View target, defined pointwise by `coefficientScale (s.epsilon n) (B.strip.epsilon
reference) (velocity n) ^ 2 • B.target reference (view n x)`. -/
noncomputable def viewTarget (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference : ℕ) : ℕ → Cylinder → Vec2 :=
  fun n x => coefficientScale (s.epsilon n) (B.strip.epsilon reference) (velocity n) ^ 2 •
    B.target reference (view n x)

/-- View cutoff, defined pointwise by `B.cutoff reference (view n x)`. -/
noncomputable def viewCutoff (view : ℕ → Cylinder → Cylinder) (reference : ℕ) :
    ℕ → Cylinder → ℝ := fun n x => B.cutoff reference (view n x)

/-- Each view calls the actual signed quotient constructor, with the same
reference pulse and matrix. Its request may be the literal current-state
request and is not replaced by an independently chosen signed wave. -/
noncomputable def viewCoefficients (s : StripData Cylinder)
    (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference : ℕ) (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients (B.viewBase background frequency view reference) s d
    (fun n x => B.matrix reference (view n x)) (B.viewTarget s velocity view reference) request
    (fun n x => B.mask reference (view n x))
    (fun n x => B.fundamental j reference (view n x))
    (fun n x => (normal n * clock n) • B.normalMotion reference (view n x))
    (fun n x => clock n • B.action reference (view n x)) j

theorem view_carrier (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder) (reference n : ℕ)
    (hf : frequency n ≠ 0) (x : Cylinder) :
    (B.viewBase background frequency view reference).frequency n *
      (B.viewBase background frequency view reference).phase n x =
        B.base.frequency reference * B.base.phase reference (view n x) := by
  simp only [viewBase]
  field_simp

theorem view_signedVector (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference n : ℕ)
    (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) (x : Cylinder)
    (hc : 0 < velocity n)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x)) :
    SignedWaveUpdate.signedVector s (fun n x => B.matrix reference (view n x))
      (B.viewTarget s velocity view reference) request (fun n x => B.mask reference (view n x))
      (fun n x => B.fundamental j reference (view n x)) j n x =
        velocity n • SignedWaveUpdate.signedVector B.strip B.matrix B.target referenceRequest
          B.mask (B.fundamental j) j reference (view n x) :=
  signedVector_transport s B.strip _ _ _ _ _ _ _ _ _ _ n reference x (view n x) hc
    rfl rfl hrequest rfl rfl j

theorem view_amplitude (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x)) :
    (B.viewCoefficients s d background frequency velocity clock normal view reference request
        j).amplitude n x =
      velocity n • (B.coefficients referenceRequest j).amplitude reference (view n x) := by
  change CurlClassBounds.complexify _ = velocity n • CurlClassBounds.complexify _
  rw [B.view_signedVector s velocity view reference n request referenceRequest j x hc hrequest,
    map_smul]

theorem view_cutoff_amplitude (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections
    Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x)) :
    ((B.viewCoefficients s d background frequency velocity clock normal view reference request
        j).withCutoff
      (B.viewCutoff view reference)).amplitude n x =
        velocity n • ((B.coefficients referenceRequest j).withCutoff B.cutoff).amplitude
          reference (view n x) := by
  simp only [LinearWaveBounds.WaveCoefficients.withCutoff, viewCutoff]
  rw [B.view_amplitude s d background frequency velocity clock normal view reference n
    request referenceRequest j x hc hrequest]
  exact smul_comm _ _ _

theorem view_pressure (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n) (hK : frequency n ≠ 0)
    (hKr : B.base.frequency reference ≠ 0) (hs : normal n ≠ 0)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x))
    (hN : (B.viewBase background frequency view reference).normal s d n x =
      normal n • B.base.normal B.strip B.directions reference (view n x)) :
    (B.viewCoefficients s d background frequency velocity clock normal view reference request
        j).pressure n x =
      ((clock n * velocity n / normal n) * (B.base.frequency reference / frequency n)) •
        (B.coefficients referenceRequest j).pressure reference (view n x) := by
  have hv := B.view_signedVector s velocity view reference n request referenceRequest j x hc
      hrequest
  change Complex.I * (TangentProjection.pressureCoefficient
      ((B.viewBase background frequency view reference).normal s d n x)
      ((normal n * clock n) • B.normalMotion reference (view n x))
      _ ((clock n • B.action reference (view n x)) _) 0 : ℂ) / (frequency n : ℂ) = _
  rw [hN, hv]
  simp only [_root_.smul_apply, map_smul, smul_smul]
  rw [mul_comm (velocity n) (clock n)]
  exact homogeneousPressure_scale (frequency n) (B.base.frequency reference) (clock n)
    (velocity n) (normal n) hK hKr hs _ _ _ _

theorem view_cutoff_pressure (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections
    Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n) (hK : frequency n ≠ 0)
    (hKr : B.base.frequency reference ≠ 0) (hs : normal n ≠ 0)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x))
    (hN : (B.viewBase background frequency view reference).normal s d n x =
      normal n • B.base.normal B.strip B.directions reference (view n x)) :
    ((B.viewCoefficients s d background frequency velocity clock normal view reference request
        j).withCutoff
      (B.viewCutoff view reference)).pressure n x =
      ((clock n * velocity n / normal n) * (B.base.frequency reference / frequency n)) •
        ((B.coefficients referenceRequest j).withCutoff B.cutoff).pressure reference (view n x) :=
            by
  simp only [LinearWaveBounds.WaveCoefficients.withCutoff, viewCutoff]
  rw [B.view_pressure s d background frequency velocity clock normal view reference n
    request referenceRequest j x hc hK hKr hs hrequest hN]
  simp only [Complex.real_smul]
  ring

/-- View primary vector, constructed using `PartitionedCovariance.amplitude`. -/
noncomputable def viewPrimaryVector (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference : ℕ) (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  PartitionedCovariance.amplitude (s.epsilon n) (B.mask reference (view n x))
    (B.matrix reference (view n x)) (B.viewTarget s velocity view reference n x) j •
      B.fundamental j reference (view n x)

theorem view_primaryVector (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference : ℕ) (j : Fin 2) (n : ℕ) (x : Cylinder)
    (hc : 0 < velocity n) :
    B.viewPrimaryVector s velocity view reference j n x =
      velocity n • B.primaryVector j reference (view n x) := by
  unfold viewPrimaryVector viewTarget primaryVector
  rw [primary_scalar_scale _ _ _ (s.epsilon_pos n) (B.strip.epsilon_pos reference) hc j,
    smul_smul]

/-- View primary coefficients, constructed using `SignedWaveUpdate.homogeneousCoefficients`. -/
noncomputable def viewPrimaryCoefficients (s : StripData Cylinder)
    (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference : ℕ) (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.homogeneousCoefficients (B.viewBase background frequency view reference) s d
    (B.viewPrimaryVector s velocity view reference j)
    (fun n x => (normal n * clock n) • B.normalMotion reference (view n x))
    (fun n x => clock n • B.action reference (view n x))

theorem view_primary_amplitude (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections
    Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (j : Fin 2) (x : Cylinder) (hc : 0 < velocity n) :
    ((B.viewPrimaryCoefficients s d background frequency velocity clock normal view reference
        j).withCutoff
      (B.viewCutoff view reference)).amplitude n x =
      velocity n • ((B.primaryCoefficients j).withCutoff B.cutoff).amplitude reference (view n x)
          := by
  simp only [viewPrimaryCoefficients, primaryCoefficients, SignedWaveUpdate.homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, viewCutoff]
  rw [B.view_primaryVector s velocity view reference j n x hc, map_smul]
  exact smul_comm _ _ _

/-- Regularity on one reference native cell. Every entry concerns the
original coordinate, target, current request, mask or phase/frame input;
there is no regularity assumption on a solved wave. -/
structure Regular (request : ℕ → Cylinder → Vec2) (reference : ℕ) (column : Fin 2) : Prop where
  coordinate : ContDiffOn ℝ ∞ (B.coordinate reference) B.strip.domain
  coordinate_mem : ∀ x ∈ B.strip.domain,
    B.coordinate reference x ∈ U.carrier reference ×ˢ Ioo (0 : ℝ) 1
  prefactor : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => B.prefactor j n)
  target : ∀ j, ContDiffOn ℝ ∞ (fun x => B.target reference x j) B.strip.domain
  request : ∀ j, ContDiffOn ℝ ∞ (fun x => request reference x j) B.strip.domain
  mask : ContDiffOn ℝ ∞ (B.mask reference) B.strip.domain
  cone : ∀ x ∈ B.strip.domain,
    SmoothCovariance.StrictCone (B.matrix reference x) (B.target reference x)
  phase : ContDiffOn ℝ ∞ (B.base.phase reference) B.strip.domain
  normal_ne : ∀ x ∈ B.strip.domain, B.base.normal B.strip B.directions reference x ≠ 0
  normal_frame : ∀ x, x ∈ B.strip.domain →
    B.base.normal B.strip B.directions reference x =
      ((B.pulse column).frame reference).normal ((B.coordinate reference x).1,
        (B.pulse column).L reference * (B.coordinate reference x).2)

namespace Regular

variable {B} {request : ℕ → Cylinder → Vec2} {reference : ℕ} {column : Fin 2}
  (H : B.Regular request reference column)

include H

theorem forPrimary : B.Regular B.primaryRequest reference column :=
  { H with request := fun j => (H.target j).const_smul (2 : ℝ) }

theorem matrix_smooth (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => B.matrix reference x i j) B.strip.domain := by
  have hm := PrimaryPulseBounds.primaryCovariance_entry_polynomial U B.prefactor
    (fun j => (B.pulse j).frame) (fun j => (B.pulse j).lam) (fun j => (B.pulse j).u)
    (fun j => (B.pulse j).L) H.prefactor (fun j => (B.pulse j).pulse_jets)
    (fun j => (B.pulse j).lam_pos) (fun j => (B.pulse j).u_pos) (fun j => (B.pulse j).L_pos) i j
  exact (hm.smooth reference).comp H.coordinate.fst (fun x hx => (H.coordinate_mem x hx).1)

theorem fundamental_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (B.fundamental j reference) B.strip.domain :=
  ((B.pulse j).pulse_jets.smooth reference).comp H.coordinate H.coordinate_mem

theorem cutoff_smooth : ContDiffOn ℝ ∞ (B.cutoff reference) B.strip.domain :=
  GaussianTailFlat.profile_contDiff.comp_contDiffOn H.coordinate.snd

theorem signedScalar_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (SignedWaveUpdate.signedScalar B.strip B.matrix B.target request B.mask j
        reference)
      B.strip.domain := by
  have hi := SmoothCovariance.contDiffOn_inverse_solution H.matrix_smooth H.request
    (fun x hx => (H.cone x hx).det_ne_zero) j
  have ha := SmoothCovariance.contDiffOn_amplitudes H.matrix_smooth H.target H.cone j
  have hd : ∀ x ∈ B.strip.domain, 2 * SmoothCovariance.amplitudes
      (B.matrix reference x) (B.target reference x) j ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by norm_num) ((H.cone x hx).amplitudes_pos j).ne'
  exact (contDiffOn_const.mul (hi.div (contDiffOn_const.mul ha) hd)).mul H.mask

theorem amplitude_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ ((B.coefficients request j).amplitude reference) B.strip.domain :=
  CurlClassBounds.complexify.contDiff.comp_contDiffOn
    ((H.signedScalar_smooth j).smul (H.fundamental_smooth j))

theorem cutoff_amplitude_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (((B.coefficients request j).withCutoff B.cutoff).amplitude reference)
        B.strip.domain :=
  H.cutoff_smooth.smul (H.amplitude_smooth j)

theorem fundamental_tangent {x : Cylinder} (hx : x ∈ B.strip.domain) :
    ⟪B.base.normal B.strip B.directions reference x, B.fundamental column reference x⟫_ℝ = 0 := by
  rw [H.normal_frame x hx]
  exact ((B.pulse column).frame reference).ambient_tangent _ _

theorem amplitude_tangent {x : Cylinder} (hx : x ∈ B.strip.domain) :
    normalDot (B.base.normal B.strip B.directions reference x)
      ((B.coefficients request column).amplitude reference x) = 0 := by
  change normalDot _ (CurlClassBounds.complexify (_ • B.fundamental column reference x)) = 0
  rw [SignedWaveUpdate.normalDot_complexify, inner_smul_right, H.fundamental_tangent hx, mul_zero]
  rfl

theorem cutoff_amplitude_tangent {x : Cylinder} (hx : x ∈ B.strip.domain) :
    normalDot (B.base.normal B.strip B.directions reference x)
      (((B.coefficients request column).withCutoff B.cutoff).amplitude reference x) = 0 := by
  change normalDot _ (B.cutoff reference x • (B.coefficients request column).amplitude reference x)
      = 0
  have he : normalDot (B.base.normal B.strip B.directions reference x)
      (B.cutoff reference x • (B.coefficients request column).amplitude reference x) =
      (B.cutoff reference x : ℂ) * normalDot (B.base.normal B.strip B.directions reference x)
        ((B.coefficients request column).amplitude reference x) := by
    simp only [normalDot, Pi.smul_apply, Complex.real_smul]
    ring
  rw [he, H.amplitude_tangent hx, mul_zero]

end Regular

/-- Angular conditions concern the original phase, coordinate and scalar
inputs. In particular the signed coefficient's invariance is a theorem. -/
structure Angular (request : ℕ → Cylinder → Vec2) (reference : ℕ) where
  /-- Mode of `Angular`, of type `ℤ`. -/
  mode : ℤ
  phase : CopyAngularInvariance.AffinePhase (0, 1) (mode / B.base.frequency reference)
    (B.base.phase reference)
  coordinate : CopyAngularInvariance.Invariant (0, 1) (B.coordinate reference)
  target : CopyAngularInvariance.Invariant (0, 1) (B.target reference)
  request : CopyAngularInvariance.Invariant (0, 1) (request reference)
  mask : CopyAngularInvariance.Invariant (0, 1) (B.mask reference)
  normalMotion : CopyAngularInvariance.Invariant (0, 1) (B.normalMotion reference)
  action : CopyAngularInvariance.Invariant (0, 1) (B.action reference)

/-- For primary, given by `{ H with request := H.target.map (fun t => (2 : ℝ) • t) }`. -/
noncomputable def Angular.forPrimary {request : ℕ → Cylinder → Vec2} {reference : ℕ}
    (H : B.Angular request reference) : B.Angular B.primaryRequest reference :=
  { H with request := H.target.map (fun t => (2 : ℝ) • t) }

/-- The angular phase and full auxiliary periodicity can be supplied by
the explicit compact-clock construction, before any signed solve. -/
noncomputable def periodicAngular (C : ReferencePhase) (request : ℕ → Cylinder → Vec2) (reference :
    ℕ)
    (hc : CopyAngularInvariance.Invariant (0, 1) (B.coordinate reference))
    (hT : CopyAngularInvariance.Invariant (0, 1) (B.target reference))
    (hR : CopyAngularInvariance.Invariant (0, 1) (request reference))
    (hm : CopyAngularInvariance.Invariant (0, 1) (B.mask reference))
    (hn : CopyAngularInvariance.Invariant (0, 1) (B.normalMotion reference))
    (ha : CopyAngularInvariance.Invariant (0, 1) (B.action reference)) :
    (B.withReferencePhase C).Angular request reference where
  mode := C.angularMode
  phase := C.phase_affine _
  coordinate := hc
  target := hT
  request := hR
  mask := hm
  normalMotion := hn
  action := ha

/-- Periodic state angular, given by `B.periodicAngular C _ reference hc hT
(stateRequest_invariant B.strip P h context current reference) hm hn ha`. -/
noncomputable def periodicStateAngular (C : ReferencePhase) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (context : CorrectionState.Context Point) (current : CorrectionState.State Point)
    (reference : ℕ)
    (hc : CopyAngularInvariance.Invariant (0, 1) (B.coordinate reference))
    (hT : CopyAngularInvariance.Invariant (0, 1) (B.target reference))
    (hm : CopyAngularInvariance.Invariant (0, 1) (B.mask reference))
    (hn : CopyAngularInvariance.Invariant (0, 1) (B.normalMotion reference))
    (ha : CopyAngularInvariance.Invariant (0, 1) (B.action reference)) :
    (B.withReferencePhase C).Angular (stateRequest B.strip P h context current) reference :=
  B.periodicAngular C _ reference hc hT (stateRequest_invariant B.strip P h context current
      reference) hm hn ha

/-- Raw, given by `((B.coefficients request j).withCutoff B.cutoff).amplitude reference`. -/
noncomputable def raw (request : ℕ → Cylinder → Vec2) (j : Fin 2) (reference : ℕ) :
    Cylinder → ComplexVector := ((B.coefficients request j).withCutoff B.cutoff).amplitude reference

/-- Raw pressure, given by `((B.coefficients request j).withCutoff B.cutoff).pressure
reference`. -/
noncomputable def rawPressure (request : ℕ → Cylinder → Vec2) (j : Fin 2) (reference : ℕ) :
    Cylinder → ℂ := ((B.coefficients request j).withCutoff B.cutoff).pressure reference

theorem raw_invariant {request : ℕ → Cylinder → Vec2} {reference : ℕ}
    (H : B.Angular request reference) (j : Fin 2) :
    CopyAngularInvariance.Invariant (0, 1) (B.raw request j reference) := by
  intro x t
  simp only [raw, coefficients, SignedWaveUpdate.coefficients,
      SignedWaveUpdate.homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, cutoff, SignedWaveUpdate.signedVector,
    SignedWaveUpdate.signedScalar, matrix, SignedWaveUpdate.phaseMatrix,
        PrimaryPulseBounds.chartCovariance,
    fundamental, SignedWaveUpdate.phaseFundamental,
    H.coordinate x t, H.target x t, H.request x t, H.mask x t]

end PrimaryData

/-- Literal background chart operators, before any wave is formed. -/
structure ChartGeometry (a : LinearWaveBounds.WaveCoefficients Cylinder)
    (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (n : ℕ) (h Q : ℝ) (cover : ℕ) : Prop where
  radius : a.radius n = PhysicalResidualBridge.ScaledGraph.radius
  radial : d.radialField n = (PhysicalResidualBridge.commonGraph Q h cover).radial
  angular : (fun _ => d.angular) = PhysicalResidualBridge.ScaledGraph.angular
  axial : d.axialField s n = (PhysicalResidualBridge.commonGraph Q h cover).axial

theorem ChartGeometry.normal {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q : ℝ} (G : ChartGeometry a s d n h Q cover) :
    a.normal s d n = phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h cover).radial
          PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h cover).axial (a.phase n) := by
  unfold LinearWaveBounds.WaveCoefficients.normal
  rw [G.radius, G.radial, G.angular, G.axial]

theorem ChartGeometry.corrected_wave {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q : ℝ} (G : ChartGeometry a s d n h Q cover)
    (cutoff : ℕ → Cylinder → ℝ) :
    vectorMode (a.frequency n) (a.phase n) ((a.corrected s d cutoff).amplitude n) =
      vectorMode (a.frequency n) (a.phase n)
        (CurlClassBounds.realizedCoefficient (a.frequency n)
            PhysicalResidualBridge.ScaledGraph.radius
          (PhysicalResidualBridge.commonGraph Q h cover).radial
              PhysicalResidualBridge.ScaledGraph.angular
          (PhysicalResidualBridge.commonGraph Q h cover).axial (a.phase n)
          ((a.withCutoff cutoff).amplitude n)) := by
  change vectorMode (a.frequency n) (a.phase n)
      (CurlClassBounds.realizedCoefficient (a.frequency n) (a.radius n) (d.radialField n)
        (fun _ => d.angular) (d.axialField s n) (a.phase n) ((a.withCutoff cutoff).amplitude n)) = _
  rw [G.radius, G.radial, G.angular, G.axial]

theorem ChartGeometry.normal_invariant {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q slope : ℝ} (G : ChartGeometry a s d n h Q cover)
    (hphi : CopyAngularInvariance.AffinePhase (0, 1) slope (a.phase n)) :
    CopyAngularInvariance.Invariant (0, 1) (a.normal s d n) := by
  rw [G.normal]
  apply CopyAngularInvariance.phaseNormal_invariant (hΦ := hphi)
  · intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radius]
  · intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radial]
  · exact CopyAngularInvariance.Invariant.const _
  · exact CopyAngularInvariance.Invariant.const _

namespace PrimaryData

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (B : PrimaryData U) (reference : ℕ)

theorem rawPressure_invariant {request : ℕ → Cylinder → Vec2}
    (H : B.Angular request reference) {h Q : ℝ} {cover : ℕ}
    (G : ChartGeometry B.base B.strip B.directions reference h Q cover) (j : Fin 2) :
    CopyAngularInvariance.Invariant (0, 1) (B.rawPressure request j reference) := by
  have hn := G.normal_invariant H.phase
  intro x t
  simp only [rawPressure, coefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, LinearWaveBounds.WaveCoefficients.withCutoff,
    cutoff, ParticularWaveBounds.projectedPressure, SignedWaveUpdate.signedVector,
    SignedWaveUpdate.signedScalar, matrix, SignedWaveUpdate.phaseMatrix,
    PrimaryPulseBounds.chartCovariance, fundamental, SignedWaveUpdate.phaseFundamental,
    H.coordinate x t, H.target x t, H.request x t, H.mask x t, H.normalMotion x t,
    H.action x t, hn x t]

/-- One physical reference scale and cover for this primary column. Band
backgrounds are primitive data; frequency, phase, target, pulse, cutoff,
normal motion and action of each view are constructed below. -/
structure Views (B : PrimaryData U) (reference : ℕ) where
  /-- Exponent of `Views`, of type `ℝ`. -/
  exponent : ℝ
  /-- Reference scale of `Views`, of type `ℝ`. -/
  referenceScale : ℝ
  referenceScale_pos : 0 < referenceScale
  /-- Reference cover of `Views`, of type `ℕ`. -/
  referenceCover : ℕ
  /-- Scale of `Views`, of type `ℕ → ℝ`. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  /-- Cover of `Views`, of type `ℕ → ℕ`. -/
  cover : ℕ → ℕ
  cover_le : ∀ n, cover n ≤ referenceCover
  /-- Frequency of `Views`, of type `ℕ → ℝ`. -/
  frequency : ℕ → ℝ
  frequency_ne : ∀ n, frequency n ≠ 0
  /-- Strip of `Views`, of type `StripData Cylinder`. -/
  strip : StripData Cylinder
  /-- Directions of `Views`, of type `LinearWaveBounds.GraphDirections Cylinder`. -/
  directions : LinearWaveBounds.GraphDirections Cylinder
  /-- Background of `Views`, of type `LinearWaveBounds.WaveCoefficients Cylinder`. -/
  background : LinearWaveBounds.WaveCoefficients Cylinder

namespace Views

variable {B reference} (V : B.Views reference)

/-- Map, given by `PhysicalParticularWave.cylinderChange V.exponent (V.scale n) V.referenceScale
(V.referenceCover - V.cover n)`. -/
noncomputable def map (n : ℕ) : Cylinder →L[ℝ] Cylinder :=
  PhysicalParticularWave.cylinderChange V.exponent (V.scale n) V.referenceScale
    (V.referenceCover - V.cover n)

/-- Velocity, given by `PhysicalParticularWave.velocityWeight V.exponent (V.scale n)
V.referenceScale`. -/
noncomputable def velocity (n : ℕ) : ℝ :=
  PhysicalParticularWave.velocityWeight V.exponent (V.scale n) V.referenceScale

/-- Clock, given by `PhysicalParticularWave.clockWeight V.exponent (V.scale n)
V.referenceScale`. -/
noncomputable def clock (n : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight V.exponent (V.scale n) V.referenceScale

/-- Normal, given by `PhysicalParticularWave.normalWeight (V.scale n) V.referenceScale
(V.frequency n) (B.base.frequency reference)`. -/
noncomputable def normal (n : ℕ) : ℝ :=
  PhysicalParticularWave.normalWeight (V.scale n) V.referenceScale (V.frequency n)
      (B.base.frequency reference)

/-- Coefficients, constructed using `B.viewCoefficients`. -/
noncomputable def coefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  B.viewCoefficients V.strip V.directions V.background V.frequency V.velocity V.clock V.normal
    (fun n => V.map n) reference request j

/-- Cutoff, given by `B.viewCutoff (fun n => V.map n) reference`. -/
noncomputable def cutoff : ℕ → Cylinder → ℝ := B.viewCutoff (fun n => V.map n) reference

/-- Exact coefficients, given by `(V.coefficients request j).corrected V.strip V.directions
V.cutoff`. -/
noncomputable def exactCoefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  (V.coefficients request j).corrected V.strip V.directions V.cutoff

theorem map_graph (n : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    V.map n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) =
      (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z := by
  have he := PhysicalParticularWave.cylinderChange_graph (V.scale_pos n) V.referenceScale_pos
    V.exponent (V.cover n) (V.referenceCover - V.cover n) hz
  simp only [Nat.add_sub_of_le (V.cover_le n)] at he
  exact he

theorem map_fastTranslate (n : ℕ) (x : Cylinder) (k : TorusInverse.Frequency) :
    V.map n (fastTranslate x k) =
      fastTranslate (V.map n x) (CommonCoverSolve.coverIndex (V.referenceCover - V.cover n) k) := by
  simp only [map, fastTranslate, PhysicalParticularWave.cylinderChange_apply,
    PhysicalParticularWave.chartChange_apply, map_add, CommonCoverSolve.coverPower_lattice]

theorem phase_periodic (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (hp : ∀ x k, B.base.phase reference (fastTranslate x k) = B.base.phase reference x)
    (n : ℕ) (x : Cylinder) (k : TorusInverse.Frequency) :
    (V.coefficients request j).phase n (fastTranslate x k) = (V.coefficients request j).phase n x
        := by
  change (B.base.frequency reference / V.frequency n) * B.base.phase reference (V.map n
      (fastTranslate x k)) =
    (B.base.frequency reference / V.frequency n) * B.base.phase reference (V.map n x)
  rw [V.map_fastTranslate, hp]

theorem carrier_periodic (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (hp : ∀ x k, B.base.phase reference (fastTranslate x k) = B.base.phase reference x)
    (n : ℕ) (x : Cylinder) (k : TorusInverse.Frequency) :
    carrier (V.frequency n) ((V.coefficients request j).phase n) (fastTranslate x k) =
      carrier (V.frequency n) ((V.coefficients request j).phase n) x := by
  simp only [HarmonicCalculus.carrier, V.phase_periodic request j hp n x k]

theorem normal_transport
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (n : ℕ)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {x : Cylinder} (hx : 0 < x.1.1)
    (hΦ : DifferentiableAt ℝ (B.base.phase reference) (V.map n x)) :
    (B.viewBase V.background V.frequency (fun n => V.map n) reference).normal V.strip V.directions
        n x =
      V.normal n • B.base.normal B.strip B.directions reference (V.map n x) := by
  rw [G.normal, H.normal]
  have he := PhysicalParticularWave.phaseNormal_chartChange (V.scale_pos n) V.referenceScale_pos
    V.exponent (V.cover n) (V.referenceCover - V.cover n) (V.frequency n) (B.base.frequency
        reference) hx hΦ
  simp only [Nat.add_sub_of_le (V.cover_le n)] at he
  exact he

theorem amplitude_transport (request referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (n : ℕ) (x : Cylinder)
    (hrequest : request n x = coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference)
      (V.velocity n) ^ 2 • referenceRequest reference (V.map n x)) :
    ((V.coefficients request j).withCutoff V.cutoff).amplitude n x =
      V.velocity n • ((B.coefficients referenceRequest j).withCutoff B.cutoff).amplitude reference
          (V.map n x) :=
  B.view_cutoff_amplitude V.strip V.directions V.background V.frequency V.velocity V.clock V.normal
    (fun n => V.map n) reference n request referenceRequest j x
    (PhysicalParticularWave.ratioPower_pos (V.scale_pos n) V.referenceScale_pos _) hrequest

theorem pressure_transport (request referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (n : ℕ) {x : Cylinder} (hx : 0 < x.1.1)
    (hKr : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hΦ : DifferentiableAt ℝ (B.base.phase reference) (V.map n x))
    (hrequest : request n x = coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference)
      (V.velocity n) ^ 2 • referenceRequest reference (V.map n x)) :
    ((V.coefficients request j).withCutoff V.cutoff).pressure n x =
      PhysicalParticularWave.pressureWeight V.exponent (V.scale n) V.referenceScale •
        ((B.coefficients referenceRequest j).withCutoff B.cutoff).pressure reference (V.map n x) :=
            by
  have he := B.view_cutoff_pressure V.strip V.directions V.background V.frequency V.velocity
      V.clock V.normal
    (fun n => V.map n) reference n request referenceRequest j x
    (PhysicalParticularWave.ratioPower_pos (V.scale_pos n) V.referenceScale_pos _) (V.frequency_ne
        n) hKr
    (PhysicalParticularWave.normalWeight_ne (V.scale_pos n) V.referenceScale_pos (V.frequency_ne n)
        hKr)
    hrequest (V.normal_transport G n H hx hΦ)
  rw [show V.clock n * V.velocity n / V.normal n * (B.base.frequency reference / V.frequency n) =
      PhysicalParticularWave.pressureWeight V.exponent (V.scale n) V.referenceScale from
    PhysicalParticularWave.pressure_scaling (V.scale_pos n) V.referenceScale_pos (V.frequency_ne n)
        hKr V.exponent] at he
  exact he

/-- Physical phase, defined pointwise by `B.base.phase reference
((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)`. -/
noncomputable def physicalPhase : SpaceTime → ℝ :=
  fun z => B.base.phase reference
    ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

/-- Physical raw as an element of `SpaceTime → ComplexVector`. -/
noncomputable def physicalRaw (referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) :
    SpaceTime → ComplexVector :=
  fun z => V.referenceScale ^ (-CoordinateAlgebra.A V.exponent) • B.raw referenceRequest j reference
    ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

/-- Reference potential, given by `PhysicalCurlCovariance.referencePotential (B.base.frequency
reference) V.physicalPhase (V.physicalRaw referenceRequest j)`. -/
noncomputable def referencePotential (referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) :
    SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential (B.base.frequency reference) V.physicalPhase
    (V.physicalRaw referenceRequest j)

/-- One Cartesian potential is chosen from the reference band and cover,
and each actual band wave will be identified with its curl. -/
noncomputable def physicalPotential (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : VelocityField :=
  PhysicalCurlCovariance.globalCartesianPotential delta (V.referencePotential referenceRequest j)

/-- Physical velocity, given by `SpatialCurl.spatialCurl (V.physicalPotential referenceRequest j
delta)`. -/
noncomputable def physicalVelocity (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : VelocityField :=
  SpatialCurl.spatialCurl (V.physicalPotential referenceRequest j delta)

theorem physicalGraph_add_angle (z : SpaceTime) (t : ℝ) :
    (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map
      (z + t • ((0 : ℝ), coordinateVector 1)) =
    (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z +
      t • ((0 : PhysicalResidualBridge.Lift), (1 : ℝ)) := by
  ext <;> simp [PhysicalResidualBridge.ScaledGraph.map, coordinateVector, smul_eq_mul]

theorem referencePotential_periodic {referenceRequest : ℕ → Cylinder → Vec2}
    (H : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (j : Fin 2) (t r z : ℝ) :
    Function.Periodic (fun angle => V.referencePotential referenceRequest j
      (t, AxisymmetricResidual.pack r angle z)) (2 * Real.pi) := by
  have hphi : CopyAngularInvariance.AffinePhase ((0 : ℝ), coordinateVector 1)
      (H.mode / B.base.frequency reference) V.physicalPhase := by
    intro x a
    unfold physicalPhase
    rw [V.physicalGraph_add_angle]
    exact H.phase _ a
  have ha : CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1)
      (V.physicalRaw referenceRequest j) := by
    intro x a
    unfold physicalRaw
    rw [V.physicalGraph_add_angle, B.raw_invariant H j _ a]
  have hR : CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1)
      LinearWaveResidual.coordinateRadius := by
    intro x a
    simp [LinearWaveResidual.coordinateRadius, coordinateVector]
  have hf : B.base.frequency reference * (H.mode / B.base.frequency reference) = (H.mode : ℝ) := by
    field_simp
  intro angle
  have he := PhysicalCurlCovariance.vectorPotential_fullTurn (Vr :=
      LinearWaveResidual.spaceDirection 0)
    (Vθ := LinearWaveResidual.spaceDirection 1) (Vz := LinearWaveResidual.spaceDirection 2)
    H.mode hR (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _)
    (CopyAngularInvariance.Invariant.const _) hphi ha hf (t, AxisymmetricResidual.pack r angle z)
  simpa only [referencePotential, PhysicalCurlCovariance.referencePotential,
    PhysicalParticularWave.angle_translate_pack] using he

/-- Wave, constructed using `vectorMode`. -/
noncomputable def wave (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    Cylinder → ComplexVector :=
  vectorMode (V.frequency n) ((V.coefficients request j).phase n)
    (CurlClassBounds.realizedCoefficient (V.frequency n) PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
      ((V.coefficients request j).phase n) (((V.coefficients request j).withCutoff
          V.cutoff).amplitude n))

theorem wave_eq_exact (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n)) :
    V.wave request j n = vectorMode ((V.exactCoefficients request j).frequency n)
      ((V.exactCoefficients request j).phase n) ((V.exactCoefficients request j).amplitude n) := by
  have H' : ChartGeometry (V.coefficients request j) V.strip V.directions n V.exponent
      (V.scale n) (V.cover n) := ⟨H.radius, H.radial, H.angular, H.axial⟩
  exact (H'.corrected_wave V.cutoff).symm

/-- The output is one literal Cartesian curl. All phase and amplitude
identities used by the curl theorem are derived from the constructors. -/
theorem wave_physical (request referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (n : ℕ) (R : B.Regular referenceRequest reference j)
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    (hradius : ∀ x ∈ V.strip.domain, 0 < x.1.1)
    (hrequest : ∀ x ∈ V.strip.domain, request n x =
      coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference) (V.velocity n) ^ 2 •
        referenceRequest reference (V.map n x))
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
        V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (V.wave request j n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover
        n)).map z) component).re =
      V.scale n ^ CoordinateAlgebra.A V.exponent * CylindricalResidual.frame (-(z.2 1))
        (V.physicalVelocity referenceRequest j delta (z.1, CylindricalResidual.chart z.2))
            component := by
  have hphi : ContDiffOn ℝ ∞ ((V.coefficients request j).phase n) V.strip.domain :=
    contDiffOn_const.mul (R.phase.comp (V.map n).contDiff.contDiffOn hmap)
  have ha : ContDiffOn ℝ ∞ (((V.coefficients request j).withCutoff V.cutoff).amplitude n)
      V.strip.domain := by
    apply (((R.cutoff_amplitude_smooth j).comp (V.map n).contDiff.contDiffOn hmap).const_smul
      (V.velocity n)).congr
    intro x hx
    exact V.amplitude_transport request referenceRequest j n x (hrequest x hx)
  have hnrel (x : Cylinder) (hx : x ∈ V.strip.domain) :
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        ((V.coefficients request j).phase n) x =
      V.normal n • B.base.normal B.strip B.directions reference (V.map n x) := by
    exact (congrFun H.normal x).symm.trans (V.normal_transport G n H (hradius x hx)
      ((R.phase.contDiffAt (B.strip.isOpen_domain.mem_nhds (hmap hx))).differentiableAt (by simp)))
  have hn (x : Cylinder) (hx : x ∈ V.strip.domain) :
      phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        ((V.coefficients request j).phase n) x ≠ 0 := by
    rw [hnrel x hx]
    exact smul_ne_zero (PhysicalParticularWave.normalWeight_ne (V.scale_pos n) V.referenceScale_pos
      (V.frequency_ne n) hK) (R.normal_ne _ (hmap hx))
  have ht (x : Cylinder) (hx : x ∈ V.strip.domain) :
      normalDot (phaseNormal PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
        ((V.coefficients request j).phase n) x)
        (((V.coefficients request j).withCutoff V.cutoff).amplitude n x) = 0 := by
    rw [hnrel x hx, V.amplitude_transport request referenceRequest j n x (hrequest x hx),
      PhysicalParticularWave.normalDot_scaled, R.cutoff_amplitude_tangent (hmap hx), mul_zero]
  have hp : ∀ y ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain,
      B.base.frequency reference * V.physicalPhase y =
        V.frequency n * (V.coefficients request j).phase n
          ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y) := by
    intro y hy
    change B.base.frequency reference * B.base.phase reference
        ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map y) =
      V.frequency n * ((B.base.frequency reference / V.frequency n) * B.base.phase reference
        (V.map n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y)))
    rw [V.map_graph n hy.1]
    field_simp [V.frequency_ne n]
  have hav : ∀ y ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
      V.strip.domain,
      V.physicalRaw referenceRequest j y = V.scale n ^ (-CoordinateAlgebra.A V.exponent) •
        ((V.coefficients request j).withCutoff V.cutoff).amplitude n
          ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map y) := by
    intro y hy
    rw [V.amplitude_transport request referenceRequest j n _ (hrequest _ hy.2),
      V.map_graph n hy.1, smul_smul]
    change V.referenceScale ^ (-CoordinateAlgebra.A V.exponent) • _ =
      (V.scale n ^ (-CoordinateAlgebra.A V.exponent) * V.velocity n) • _
    congr 1
    rw [mul_comm]
    exact (PhysicalParticularWave.ratioPower_cancel (V.scale_pos n) V.referenceScale_pos _).symm
  exact PhysicalCurlCovariance.reference_correctedWave_constructed (V.scale_pos n) V.exponent
      (V.cover n)
    V.strip.isOpen_domain (fun x hx => (hradius x hx).ne') hK (V.frequency_ne n) hphi ha hn ht
    V.physicalPhase (V.physicalRaw referenceRequest j) hp hav
    (V.referencePotential_periodic A hK j) hz hdelta chart hchart component

theorem referencePotential_smoothAt (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (R : B.Regular referenceRequest reference j)
    (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (hradius : ∀ x ∈ B.strip.domain, 0 < x.1.1)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z ∈
        B.strip.domain) :
    ContDiffAt ℝ ∞ (V.referencePotential referenceRequest j) z := by
  let g := PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover
  have hn : ∀ x ∈ B.strip.domain, phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      g.radial PhysicalResidualBridge.ScaledGraph.angular g.axial (B.base.phase reference) x ≠ 0 :=
          by
    intro x hx
    rw [← G.normal]
    exact R.normal_ne x hx
  have hs := CurlClassBounds.vectorPotential_contDiffOn
    (PhysicalCurlCovariance.ScaledGraph.geometry g B.strip.isOpen_domain (fun x hx => (hradius x
        hx).ne'))
    (B.base.frequency reference) R.phase (R.cutoff_amplitude_smooth j) hn
  have hm : ContDiffAt ℝ ∞ g.map z :=
    g.map_smoothAt (mul_pos (Real.rpow_pos_of_pos V.referenceScale_pos _) hz).ne'
  have ht := ((hs.contDiffAt (B.strip.isOpen_domain.mem_nhds hx)).comp z hm).const_smul
    (V.referenceScale ^ (-V.exponent))
  have he := PhysicalCurlCovariance.referencePotential_eq_on V.referenceScale_pos V.exponent
      V.referenceCover
    B.strip.isOpen_domain hK hK R.phase (B.raw referenceRequest j reference)
    V.physicalPhase (V.physicalRaw referenceRequest j) (fun _ _ => rfl) (fun _ _ => rfl)
  apply ht.congr_of_eventuallyEq
  exact eventually_of_mem ((g.source_open (Real.rpow_pos_of_pos V.referenceScale_pos _)
    B.strip.isOpen_domain).mem_nhds ⟨hz, hx⟩) he

theorem physicalPotential_smoothAt (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (R : B.Regular referenceRequest reference j)
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (hradius : ∀ x ∈ B.strip.domain, 0 < x.1.1)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z ∈
        B.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    ContDiffAt ℝ ∞ (V.physicalPotential referenceRequest j delta) (z.1, CylindricalResidual.chart
        z.2) :=
  PhysicalCurlCovariance.globalCartesianPotential_smoothAt_forward hdelta chart
    (V.referencePotential_periodic A hK j) hchart
    (V.referencePotential_smoothAt referenceRequest j R hK G hradius hz hx)

theorem physicalVelocity_divergence (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (R : B.Regular referenceRequest reference j)
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (hradius : ∀ x ∈ B.strip.domain, 0 < x.1.1)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z ∈
        B.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    spatialDivergence (V.physicalVelocity referenceRequest j delta) z.1 (CylindricalResidual.chart
        z.2) = 0 := by
  have hs := (V.physicalPotential_smoothAt referenceRequest j R A hK G hradius hz hx hdelta chart
      hchart).comp
    (CylindricalResidual.chart z.2) (contDiffAt_const.prodMk contDiffAt_id)
  exact SpatialCurl.spatialDivergence_spatialCurl _ _ _
    (hs.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)

/-! ## Pressure is transported from the same reference coefficient -/

/-- Physical pressure coefficient as an element of `SpaceTime → ℂ`. -/
noncomputable def physicalPressureCoefficient (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) : SpaceTime → ℂ :=
  fun z => V.referenceScale ^ (-(2 * CoordinateAlgebra.A V.exponent)) •
    B.rawPressure referenceRequest j reference
      ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

/-- Complex physical pressure, given by `mode (B.base.frequency reference) V.physicalPhase
(V.physicalPressureCoefficient referenceRequest j)`. -/
noncomputable def complexPhysicalPressure (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) : SpaceTime → ℂ :=
  mode (B.base.frequency reference) V.physicalPhase (V.physicalPressureCoefficient referenceRequest
      j)

/-- Physical pressure as an element of `PressureField`. -/
noncomputable def physicalPressure (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : PressureField :=
  fun z => PhysicalCurlCovariance.globalCartesianPotential delta
    (PhysicalParticularWave.pressureVector (V.complexPhysicalPressure referenceRequest j)) z 2

/-- Pressure mode, given by `mode (V.frequency n) ((V.coefficients request j).phase n)
(((V.coefficients request j).withCutoff V.cutoff).pressure n)`. -/
noncomputable def pressureMode (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    Cylinder → ℂ :=
  mode (V.frequency n) ((V.coefficients request j).phase n)
    (((V.coefficients request j).withCutoff V.cutoff).pressure n)

theorem complexPhysicalPressure_periodic {referenceRequest : ℕ → Cylinder → Vec2}
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (j : Fin 2) (t r z : ℝ) :
    Function.Periodic (fun angle => V.complexPhysicalPressure referenceRequest j
      (t, AxisymmetricResidual.pack r angle z)) (2 * Real.pi) := by
  have hphi : CopyAngularInvariance.AffinePhase ((0 : ℝ), coordinateVector 1)
      (A.mode / B.base.frequency reference) V.physicalPhase := by
    intro x a
    unfold physicalPhase
    rw [V.physicalGraph_add_angle]
    exact A.phase _ a
  have hp : CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1)
      (V.physicalPressureCoefficient referenceRequest j) := by
    intro x a
    unfold physicalPressureCoefficient
    rw [V.physicalGraph_add_angle, B.rawPressure_invariant reference A G j _ a]
  have hf : B.base.frequency reference * (A.mode / B.base.frequency reference) = (A.mode : ℝ) := by
    field_simp
  intro angle
  have he := PhysicalParticularWave.mode_fullTurn A.mode hphi hp hf
    (t, AxisymmetricResidual.pack r angle z)
  simpa only [complexPhysicalPressure, PhysicalParticularWave.angle_translate_pack] using he

theorem physicalPressure_forward {referenceRequest : ℕ → Cylinder → Vec2}
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (j : Fin 2) {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    V.physicalPressure referenceRequest j delta (z.1, CylindricalResidual.chart z.2) =
      (V.complexPhysicalPressure referenceRequest j z).re := by
  have hper (t r z : ℝ) : Function.Periodic
      (fun angle => PhysicalParticularWave.pressureVector (V.complexPhysicalPressure
          referenceRequest j)
        (t, AxisymmetricResidual.pack r angle z)) (2 * Real.pi) := by
    intro angle
    simp only [PhysicalParticularWave.pressureVector,
      V.complexPhysicalPressure_periodic A hK G j t r z angle]
  have he := (PhysicalCurlCovariance.globalCartesianPotential_forward_germ hdelta chart
    (PhysicalParticularWave.pressureVector (V.complexPhysicalPressure referenceRequest j)) hper
        hz).eq_of_nhds
  unfold physicalPressure
  rw [he]
  simp [CylindricalResidual.frame_apply, PhysicalCurlCovariance.realVector,
    PhysicalParticularWave.pressureVector]

theorem pressureMode_physical (request referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (n : ℕ) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hPhi : DifferentiableAt ℝ (B.base.phase reference)
      ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z))
    (hrequest : request n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover
        n)).map z) =
      coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference) (V.velocity n) ^ 2 •
        referenceRequest reference ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent
            V.referenceCover).map z)) :
    V.pressureMode request j n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover
        n)).map z) =
      V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) • V.complexPhysicalPressure referenceRequest
          j z := by
  have hraw := V.pressure_transport request referenceRequest j n
    (x := (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)
    (mul_pos (Real.rpow_pos_of_pos (V.scale_pos n) _) hz) hK G H
    (by simpa only [V.map_graph n hz] using hPhi) (by simpa only [V.map_graph n hz] using hrequest)
  rw [V.map_graph n hz] at hraw
  have hc : carrier (V.frequency n) ((V.coefficients request j).phase n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) =
      carrier (B.base.frequency reference) V.physicalPhase z := by
    apply PhysicalCurlCovariance.carrier_eq_of_products
    have he := B.view_carrier V.background V.frequency (fun n => V.map n) reference n
      (V.frequency_ne n) ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover
          n)).map z)
    simp only [V.map_graph n hz] at he
    exact he
  have hw : PhysicalParticularWave.pressureWeight V.exponent (V.scale n) V.referenceScale =
      V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
        V.referenceScale ^ (-(2 * CoordinateAlgebra.A V.exponent)) := by
    unfold PhysicalParticularWave.pressureWeight PhysicalParticularWave.ratioPower
    rw [Real.rpow_neg V.referenceScale_pos.le, div_eq_mul_inv]
  unfold pressureMode complexPhysicalPressure HarmonicCalculus.mode
  rw [hraw, hc, hw]
  simp only [physicalPressureCoefficient, rawPressure, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem pressure_physical (request referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (n : ℕ) (A : B.Angular referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hPhi : DifferentiableAt ℝ (B.base.phase reference)
      ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z))
    (hrequest : request n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover
        n)).map z) =
      coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference) (V.velocity n) ^ 2 •
        referenceRequest reference ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent
            V.referenceCover).map z))
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (V.pressureMode request j n ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent
        (V.cover n)).map z)).re =
      V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
        V.physicalPressure referenceRequest j delta (z.1, CylindricalResidual.chart z.2) := by
  rw [V.pressureMode_physical request referenceRequest j n hK G H hz hPhi hrequest,
    V.physicalPressure_forward A hK G j hdelta chart hchart]
  simp [Complex.real_smul]

theorem pressureMode_eq_exact (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    V.pressureMode request j n = HarmonicCalculus.mode ((V.exactCoefficients request j).frequency n)
      ((V.exactCoefficients request j).phase n) ((V.exactCoefficients request j).pressure n) := rfl

/-! ## The primary coefficient is an exact specialization -/

/-- Primary request, defined pointwise by `(2 : ℝ) • B.viewTarget V.strip V.velocity (fun n =>
V.map n) reference n x`. -/
noncomputable def primaryRequest : ℕ → Cylinder → Vec2 :=
  fun n x => (2 : ℝ) • B.viewTarget V.strip V.velocity (fun n => V.map n) reference n x

/-- Primary coefficients, given by `B.viewPrimaryCoefficients V.strip V.directions V.background
V.frequency V.velocity V.clock V.normal (fun n => V.map n) reference j`. -/
noncomputable def primaryCoefficients (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  B.viewPrimaryCoefficients V.strip V.directions V.background V.frequency V.velocity V.clock
      V.normal
    (fun n => V.map n) reference j

/-- Primary exact coefficients, given by `(V.primaryCoefficients j).corrected V.strip
V.directions V.cutoff`. -/
noncomputable def primaryExactCoefficients (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder
    :=
  (V.primaryCoefficients j).corrected V.strip V.directions V.cutoff

theorem primaryCoefficients_eq_signed (j : Fin 2) :
    V.primaryCoefficients j = V.coefficients V.primaryRequest j := by
  have he : B.viewPrimaryVector V.strip V.velocity (fun n => V.map n) reference j =
      SignedWaveUpdate.signedVector V.strip
        (fun n x => B.matrix reference (V.map n x))
        (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) V.primaryRequest
        (fun n x => B.mask reference (V.map n x))
        (fun n x => B.fundamental j reference (V.map n x)) j := by
    funext n x
    simp only [viewPrimaryVector, SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
      primaryRequest, increment_twice_target, PartitionedCovariance.amplitude]
  unfold primaryCoefficients viewPrimaryCoefficients coefficients viewCoefficients
    SignedWaveUpdate.coefficients
  rw [he]

theorem primaryRequest_transport (n : ℕ) (x : Cylinder) :
    V.primaryRequest n x = coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference)
      (V.velocity n) ^ 2 • B.primaryRequest reference (V.map n x) := by
  simp only [primaryRequest, PrimaryData.primaryRequest, viewTarget]
  exact smul_comm _ _ _

/-- Primary physical potential, given by `V.physicalPotential B.primaryRequest j delta`. -/
noncomputable def primaryPhysicalPotential (delta : ℝ) (j : Fin 2) : VelocityField :=
  V.physicalPotential B.primaryRequest j delta

/-- Primary physical velocity, given by `SpatialCurl.spatialCurl (V.primaryPhysicalPotential
delta j)`. -/
noncomputable def primaryPhysicalVelocity (delta : ℝ) (j : Fin 2) : VelocityField :=
  SpatialCurl.spatialCurl (V.primaryPhysicalPotential delta j)

/-- Primary physical pressure, given by `V.physicalPressure B.primaryRequest j delta`. -/
noncomputable def primaryPhysicalPressure (delta : ℝ) (j : Fin 2) : PressureField :=
  V.physicalPressure B.primaryRequest j delta

/-- The primary statement uses its actual square-root coefficient and
the same once-cutoff curl correction as the signed update. -/
theorem primary_wave_physical {request : ℕ → Cylinder → Vec2}
    (j : Fin 2) (n : ℕ) (R : B.Regular request reference j)
    (A : B.Angular request reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    (hradius : ∀ x ∈ V.strip.domain, 0 < x.1.1)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
        V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (vectorMode ((V.primaryExactCoefficients j).frequency n) ((V.primaryExactCoefficients j).phase
        n)
      ((V.primaryExactCoefficients j).amplitude n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) component).re
          =
        V.scale n ^ CoordinateAlgebra.A V.exponent * CylindricalResidual.frame (-(z.2 1))
          (V.primaryPhysicalVelocity delta j (z.1, CylindricalResidual.chart z.2)) component := by
  have he := V.wave_physical V.primaryRequest B.primaryRequest j n R.forPrimary (A.forPrimary B)
    hK G H hmap hradius (fun x _ => V.primaryRequest_transport n x) hz hdelta chart hchart component
  rw [V.wave_eq_exact V.primaryRequest j n H] at he
  simp only [primaryExactCoefficients, V.primaryCoefficients_eq_signed j] at he ⊢
  exact he

theorem primary_pressure_physical {request : ℕ → Cylinder → Vec2}
    (j : Fin 2) (n : ℕ) (R : B.Regular request reference j)
    (A : B.Angular request reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z ∈
        B.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (HarmonicCalculus.mode ((V.primaryExactCoefficients j).frequency n)
        ((V.primaryExactCoefficients j).phase n)
      ((V.primaryExactCoefficients j).pressure n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)).re =
        V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
          V.primaryPhysicalPressure delta j (z.1, CylindricalResidual.chart z.2) := by
  have he := V.pressure_physical V.primaryRequest B.primaryRequest j n (A.forPrimary B) hK G H hz
    ((R.phase.contDiffAt (B.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (by simpa only [V.map_graph n hz] using (V.primaryRequest_transport n
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)))
    hdelta chart hchart
  rw [V.pressureMode_eq_exact V.primaryRequest j n] at he
  simp only [primaryExactCoefficients, V.primaryCoefficients_eq_signed j] at he ⊢
  exact he

/-! ## Bind the constructor to the literal current-state request -/

/-- All coherence fields concern the current state, background and
integration domain before the signed wave is constructed. -/
structure StateData (V : B.Views reference) where
  /-- Patch of `StateData`, of type `SignedStressPrimitive.Patch`. -/
  patch : SignedStressPrimitive.Patch
  /-- Context of `StateData`, of type `CorrectionState.Context Point`. -/
  context : CorrectionState.Context Point
  /-- Reference context of `StateData`, of type `CorrectionState.Context Point`. -/
  referenceContext : CorrectionState.Context Point
  /-- Current of `StateData`, of type `CorrectionState.State Point`. -/
  current : CorrectionState.State Point
  /-- Reference state of `StateData`, of type `CorrectionState.State Point`. -/
  referenceState : CorrectionState.State Point
  exponent_pos : 0 < V.exponent
  exponent_lt_half : V.exponent < 1 / 2
  /-- Domain of `StateData`, of type `ℕ → Set Point`. -/
  domain : ℕ → Set Point
  domain_open : ∀ n, IsOpen (domain n)
  state_coherent : ∀ n, PhysicalResidualNaturality.StateOn (domain n)
    (requestChart V.exponent (V.scale_pos n) V.referenceScale_pos (V.referenceCover - V.cover n))
    (V.velocity n) (PhysicalParticularWave.ratioPower (V.scale n) V.referenceScale (1 / 2))
    current referenceState n reference
  context_coherent : ∀ n, PhysicalResidualNaturality.ContextOn (domain n)
    (requestChart V.exponent (V.scale_pos n) V.referenceScale_pos (V.referenceCover - V.cover n))
    (V.velocity n) (PhysicalParticularWave.ratioPower (V.scale n) V.referenceScale (1 / 2))
    context referenceContext n reference
  time_pos : ∀ x ∈ V.strip.domain, 0 < x.1.2.1.2
  fibers : ∀ n x, x ∈ V.strip.domain → ∀ r Y,
    (r, ((x.1.2.1.2, x.1.2.1.1), Y)) ∈ domain n
  /-- Reference slow of `StateData`, of type `ℕ → Set LocalSignedRequest.Plane`. -/
  referenceSlow : ℕ → Set LocalSignedRequest.Plane
  referenceSlow_open : ∀ n, IsOpen (referenceSlow n)
  referenceSlow_mem : ∀ n x, x ∈ V.strip.domain →
    slowChange V.exponent (V.scale n) V.referenceScale (x.1.2.1.2, x.1.2.1.1) ∈ referenceSlow n
  reference_theta_smooth : ∀ n, ContDiffOn ℝ ∞ (referenceState.thetaResidual referenceContext
      reference)
    (PhysicalMeanDomain.slowDomain (referenceSlow n))
  reference_axial_smooth : ∀ n, ContDiffOn ℝ ∞ (referenceState.axialResidual referenceContext
      reference)
    (PhysicalMeanDomain.slowDomain (referenceSlow n))
  reference_theta_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn (referenceSlow n)
    (referenceState.thetaResidual referenceContext reference)
  reference_axial_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn (referenceSlow n)
    (referenceState.axialResidual referenceContext reference)

namespace StateData

variable {V} (D : V.StateData)

/-- Request, given by `stateRequest V.strip D.patch V.exponent D.context D.current`. -/
noncomputable def request : ℕ → Cylinder → Vec2 :=
  stateRequest V.strip D.patch V.exponent D.context D.current

/-- Reference request, given by `stateRequest B.strip D.patch V.exponent D.referenceContext
D.referenceState`. -/
noncomputable def referenceRequest : ℕ → Cylinder → Vec2 :=
  stateRequest B.strip D.patch V.exponent D.referenceContext D.referenceState

theorem request_transport (n : ℕ) (x : Cylinder) (hx : x ∈ V.strip.domain) :
    D.request n x = coefficientScale (V.strip.epsilon n) (B.strip.epsilon reference)
      (V.velocity n) ^ 2 • D.referenceRequest reference (V.map n x) :=
  stateRequest_of_state V.strip B.strip D.patch D.exponent_pos D.exponent_lt_half
    (V.scale_pos n) V.referenceScale_pos D.context D.referenceContext D.current D.referenceState
    n reference (V.referenceCover - V.cover n) (D.domain_open n) (D.state_coherent n)
        (D.context_coherent n)
    x (D.time_pos x hx) (D.fibers n x hx) (D.referenceSlow_open n) (D.referenceSlow_mem n x hx)
    (D.reference_theta_smooth n) (D.reference_axial_smooth n)
    (D.reference_theta_periodic n) (D.reference_axial_periodic n)

theorem actual_wave_physical (j : Fin 2) (n : ℕ)
    (R : B.Regular D.referenceRequest reference j) (A : B.Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    (hradius : ∀ x ∈ V.strip.domain, 0 < x.1.1)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
        V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (component : Fin 3) :
    (vectorMode ((V.exactCoefficients D.request j).frequency n) ((V.exactCoefficients D.request
        j).phase n)
      ((V.exactCoefficients D.request j).amplitude n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) component).re
          =
        V.scale n ^ CoordinateAlgebra.A V.exponent * CylindricalResidual.frame (-(z.2 1))
          (V.physicalVelocity D.referenceRequest j delta (z.1, CylindricalResidual.chart z.2))
              component := by
  have he := V.wave_physical D.request D.referenceRequest j n R A hK G H hmap hradius
    (D.request_transport n) hz hdelta chart hchart component
  rwa [V.wave_eq_exact D.request j n H] at he

theorem actual_pressure_physical (j : Fin 2) (n : ℕ)
    (R : B.Regular D.referenceRequest reference j) (A : B.Angular D.referenceRequest reference)
    (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale
        V.referenceCover)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    (hmap : MapsTo (V.map n) V.strip.domain B.strip.domain)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).source
        V.strip.domain)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (HarmonicCalculus.mode ((V.exactCoefficients D.request j).frequency n) ((V.exactCoefficients
        D.request j).phase n)
      ((V.exactCoefficients D.request j).pressure n)
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z)).re =
        V.scale n ^ (2 * CoordinateAlgebra.A V.exponent) *
          V.physicalPressure D.referenceRequest j delta (z.1, CylindricalResidual.chart z.2) := by
  have hx : (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z
      ∈ B.strip.domain := by
    rw [← V.map_graph n hz.1]
    exact hmap hz.2
  have he := V.pressure_physical D.request D.referenceRequest j n A hK G H hz.1
    ((R.phase.contDiffAt (B.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (by simpa only [V.map_graph n hz.1] using (D.request_transport n
      ((PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).map z) hz.2))
    hdelta chart hchart
  rwa [V.pressureMode_eq_exact D.request j n] at he

end StateData

end Views

end PrimaryData

end NavierStokes.PhysicalSignedWave
