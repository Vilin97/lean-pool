/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedStressPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ErrorHarmonics
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanMomentBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopyAngularInvariance

@[expose] public section

/-!
# Constructed signed wave increments

The signed coefficient is the inverse of the same integrated primary matrix,
divided by twice the same positive primary amplitude.  Its sign is unrestricted.
The homogeneous pressure, exact curl, signed square, and slot-cutoff error are
retained as actual fields.
-/

noncomputable section

namespace NavierStokes.SignedWaveUpdate

open Set Function Filter MeasureTheory Matrix
open WeightedClasses HarmonicCalculus
open scoped ContDiff Topology BigOperators ComplexConjugate InnerProductSpace


abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Space := ProblemStatement.Space

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The requested stress is the negative primitive of the actual state -/

noncomputable def requestedStress (p : SignedStressPrimitive.Patch)
    (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) : ℕ → ℝ × E → Vec2 :=
  fun n z => ![SignedStressPrimitive.barSigma p 2 (u.thetaResidual c n) z,
    SignedStressPrimitive.barSigma p 1 (u.axialResidual c n) z]

theorem requestedStress_contDiff (p : SignedStressPrimitive.Patch)
    (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) (n : ℕ)
    (ht : ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ContDiff ℝ ∞ (u.axialResidual c n))
    (hst : RadialAlias.RadiallySupported p.a p.b (u.thetaResidual c n))
    (hsz : RadialAlias.RadiallySupported p.a p.b (u.axialResidual c n)) :
    ContDiff ℝ ∞ (requestedStress p c u n) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact SignedStressPrimitive.barSigma_contDiff p 2 ht hst
  · exact SignedStressPrimitive.barSigma_contDiff p 1 hz hsz

theorem requestedStress_negative_primitive (p : SignedStressPrimitive.Patch)
    (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) (n : ℕ)
    (ht : ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ContDiff ℝ ∞ (u.axialResidual c n))
    (hst : RadialAlias.RadiallySupported p.a p.b (u.thetaResidual c n))
    (hsz : RadialAlias.RadiallySupported p.a p.b (u.axialResidual c n)) (z : ℝ × E) :
    requestedStress p c u n z =
      ![-(∫ r in (0 : ℝ)..z.1, r ^ 2 * SignedStressPrimitive.adjusted p 2
          (PressureStream.torusAverage (u.thetaResidual c n)) (r, z.2)) / z.1 ^ 2,
        -(∫ r in (0 : ℝ)..z.1, r ^ 1 * SignedStressPrimitive.adjusted p 1
          (PressureStream.torusAverage (u.axialResidual c n)) (r, z.2)) / z.1 ^ 1] := by
  ext i
  fin_cases i
  · exact SignedStressPrimitive.barSigma_eq_primitive p 2 ht hst z
  · exact SignedStressPrimitive.barSigma_eq_primitive p 1 hz hsz z

theorem requestedStress_divergence (p : SignedStressPrimitive.Patch)
    (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) (n : ℕ)
    (ht : ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ContDiff ℝ ∞ (u.axialResidual c n))
    (hst : RadialAlias.RadiallySupported p.a p.b (u.thetaResidual c n))
    (hsz : RadialAlias.RadiallySupported p.a p.b (u.axialResidual c n))
    (z : E) {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 2 (fun t => requestedStress p c u n (t,z) 0) r =
      -SignedStressPrimitive.adjusted p 2 (PressureStream.torusAverage (u.thetaResidual c n)) (r,z)
        ∧
    IntegratedMeanBalances.radialDivergence 1 (fun t => requestedStress p c u n (t,z) 1) r =
      -SignedStressPrimitive.adjusted p 1 (PressureStream.torusAverage (u.axialResidual c n)) (r,z)
        := by
  exact ⟨SignedStressPrimitive.angular_divergence p
    (PressureStream.torusAverage_contDiff ht) (PressureStream.torusAverage_supported hst) z hr,
    SignedStressPrimitive.axial_divergence p
      (PressureStream.torusAverage_contDiff hz) (PressureStream.torusAverage_supported hsz) z hr⟩

/-! ## Inverse jets and the signed quotient -/

theorem weights_smul (H : Mat2) (T : Vec2) (a : ℝ) (j : Fin 2) :
    SmoothCovariance.weights H (a • T) j = a * SmoothCovariance.weights H T j := by
  fin_cases j <;>
    simp [SmoothCovariance.weights, SmoothCovariance.cramerNumerator,
      Pi.smul_apply, smul_eq_mul] <;> ring

/-- Only primitive matrix/target jets and zeroth-order primary margins occur
in this record. There is no assumption on an inverse or a signed output. -/
structure CovarianceControl (s : StripData D) (H : ℕ → D → Mat2)
    (T : ℕ → D → Vec2) where
  matrix_jets : ∀ i j, PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
    (fun n x => H n x i j)
  target_jets : ∀ i, MeanClass s 0 (fun n x => T n x i)
  zeta_pos : ∀ x ∈ s.domain, 0 < s.zeta x
  b : ℝ
  M : ℝ
  c : ℝ
  b_pos : 0 < b
  M_one : 1 ≤ M
  c_pos : 0 < c
  determinant : ∀ n x, x ∈ s.domain →
    b ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H n x)).det|
  entries : ∀ n x, x ∈ s.domain → ∀ i j,
    |Real.sqrt (s.slow n) * H n x i j| ≤ M
  lower : ∀ n x, x ∈ s.domain → ∀ j,
    c * s.zeta x ≤ SmoothCovariance.weights (H n x) (T n x) j

namespace CovarianceControl

variable {s : StripData D} {H : ℕ → D → Mat2} {T : ℕ → D → Vec2}

theorem cone (h : CovarianceControl s H T) (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    SmoothCovariance.StrictCone (H n x) (T n x) :=
  (SmoothCovariance.weights_pos_iff _ _).mp
    (fun j => (mul_pos h.c_pos (h.zeta_pos x hx)).trans_le (h.lower n x hx j))

/-- Cramer's actual formula preserves every band exponent, including signed
targets. Its denominator estimates are taken from the same primary matrix. -/
theorem inverse_class (h : CovarianceControl s H T) {R : ℕ → D → Vec2} {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i)) (j : Fin 2) :
    MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j) := by
  have hR0 (i : Fin 2) : MeanClass s 0 (fun n x => s.epsilon n ^ (-β) * R n x i) := by
    simpa only [smul_eq_mul, add_neg_cancel] using (hR i).band_smul (bandBound_rpow s (-β))
  have h0 := PrimaryPulseBounds.covariance_weights_class
    (PrimaryPulseBounds.sqrt_slow_polynomial s)
    (fun n => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (s.one_le_slow n))).ne')
    h.matrix_jets hR0 h.b_pos h.M_one h.determinant h.entries j
  have hβ := h0.band_smul (bandBound_rpow s β)
  apply LinearWaveBounds.class_congr (by simpa only [zero_add] using hβ)
  intro n x hx
  dsimp only
  rw [SmoothCovariance.inverse_formula _ _ (h.cone n hx).det_ne_zero]
  change s.epsilon n ^ β * SmoothCovariance.weights (H n x)
    (s.epsilon n ^ (-β) • R n x) j = _
  rw [weights_smul, ← mul_assoc, ← Real.rpow_add (s.epsilon_pos n),
    add_neg_cancel, Real.rpow_zero, one_mul]

theorem inverse_control (h : CovarianceControl s H T) (j : Fin 2) :
    SignedCovariance.InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j) := by
  apply SignedCovariance.inverseControl_of_lower
    (fun n x hx => (PartitionedCovariance.amplitudes_are_inverse_weights (h.cone n hx) j).1)
    h.c_pos 0
  intro n x hx
  simpa only [pow_zero, div_one, SmoothCovariance.inverse_formula _ _ (h.cone n hx).det_ne_zero]
    using h.lower n x hx j

theorem increment_class (h : CovarianceControl s H T) {R : ℕ → D → Vec2} {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i)) (j : Fin 2) :
    WaveClass s (fun _ _ => 1) β
      (fun n x => SignedCovariance.increment (H n x) (T n x) (R n x) j) :=
  SignedCovariance.increment_wave_class j h.zeta_pos (fun n _ hx => h.cone n hx)
    (h.inverse_class h.target_jets j) (h.inverse_class hR j) (h.inverse_control j)

end CovarianceControl

noncomputable def signedScalar (s : StripData D) (H : ℕ → D → Mat2)
    (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ) (j : Fin 2) : ℕ → D → ℝ :=
  fun n x => Real.sqrt (s.epsilon n) * SignedCovariance.increment (H n x) (T n x) (R n x) j * mask
    n x

noncomputable def signedVector (s : StripData D) (H : ℕ → D → Mat2)
    (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ) (v : ℕ → D → Space) (j : Fin 2) :
    ℕ → D → Space := fun n x => signedScalar s H T R mask j n x • v n x

theorem signedScalar_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {β : ℝ} (h : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (j : Fin 2) :
    WaveClass s (fun _ _ => 1) (β + 1 / 2) (signedScalar s H T R mask j) := by
  have hi := h.increment_class hR j
  have hh := (LinearWaveBounds.unweighted_smul hm (show MemClass s (fun _ x => Real.sqrt (s.zeta
    x)) β
    (fun n x => SignedCovariance.increment (H n x) (T n x) (R n x) j) from by
      simpa only [WaveClass, mul_one] using hi))
  have hh' := hh.band_smul (bandBound_rpow s (1 / 2))
  apply LinearWaveBounds.class_congr (by simpa only [WaveClass, mul_one, zero_add] using hh')
  intro n x _
  simp only [signedScalar, smul_eq_mul, ← Real.sqrt_eq_rpow]
  ring

theorem signedVector_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {v : ℕ → D → Space} {P : ℕ → D → ℝ} {β : ℝ}
    (h : CovarianceControl s H T) (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v) (j : Fin 2) :
    WaveClass s P (β + 1 / 2) (signedVector s H T R mask v j) := by
  have hs := signedScalar_class h hR hm j
  have h := hs.smul hv
  simp only [mul_one, add_zero] at h
  exact h

/-! ## The same homogeneous fundamental and its constructed pressure -/

noncomputable def homogeneousCoefficients (a : LinearWaveBounds.WaveCoefficients D)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space) :
    LinearWaveBounds.WaveCoefficients D :=
  { a with
    amplitude := fun n x => CurlClassBounds.complexify (v n x)
    pressure := fun n => ParticularWaveBounds.projectedPressure (a.frequency n)
      (a.normal s d n) (Ndot n) (v n) (fun x => A n x (v n x)) (fun _ => 0) }

noncomputable def coefficients (a : LinearWaveBounds.WaveCoefficients D)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients D :=
  homogeneousCoefficients a s d (signedVector s H T R mask v j) Ndot A

/-- Every signed amplitude and pressure bound is obtained from the actual
inverse quotient and the primitive homogeneous fundamental. The input wave
bound supplies only the already fixed background geometry. -/
theorem coefficients_inputBounds
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    {a : LinearWaveBounds.WaveCoefficients D} {P₀ P : ℕ → D → ℝ} {α₀ β κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) (j : Fin 2) :
    LinearWaveBounds.InputBounds s P (β + 1 / 2) κ d
      (coefficients a s d H T R mask v Ndot A j) := by
  have hs := signedVector_class hcov hR hm hv j
  have ha := hs.map CurlClassBounds.complexify
  have hp := ParticularWaveBounds.pressure_class hN hNdot hA hs
    (MemClass.zero hs.weight_nonneg) hb hlo hhi hK
  exact { hbase with
    amplitude := fun i => CurlClassBounds.class_component ha i
    pressure := hp }

/-- Equality along an actual straight fast orbit, imposed on the primitive
slow data, not on the signed solve or its derivatives. -/
def FrozenAlong (v : D) (f : ℕ → D → E) : Prop :=
  ∀ n x (t : ℝ), f n (x + t • v) = f n x

theorem FrozenAlong.derivative {v : D} {f : ℕ → D → E}
    (hf : FrozenAlong v f) (n : ℕ) {x : D} (hd : DifferentiableAt ℝ (f n) x) :
    fderiv ℝ (f n) x v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hh : HasDerivAt (fun t : ℝ => f n (x + t • v)) (fderiv ℝ (f n) x v) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hl
    simpa only [zero_smul, add_zero] using hd.hasFDerivAt
  have he : (fun t : ℝ => f n (x + t • v)) = fun _ => f n x := funext (hf n x)
  rw [he] at hh
  exact hh.unique (hasDerivAt_const (0 : ℝ) (f n x))

theorem signedScalar_frozen {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {v : D}
    (hH : FrozenAlong v H) (hT : FrozenAlong v T) (hR : FrozenAlong v R)
    (hm : FrozenAlong v mask) (j : Fin 2) :
    FrozenAlong v (signedScalar s H T R mask j) := by
  intro n x t
  simp only [signedScalar, hH n x t, hT n x t, hR n x t, hm n x t]

theorem along_smul (V : D → D) {f : D → ℝ} {g : D → E} {x : D}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along V (fun y => f y • g y) x = along V f x • g x + f x • along V g x := by
  simp only [along, fderiv_fun_smul hf hg, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  exact add_comm _ _

theorem projectedRhs_smul (N Ndot v Av : Space) (δ c : ℝ) :
    TangentProjection.projectedRhs N Ndot (c • v) (c • Av) 0 δ =
      c • TangentProjection.projectedRhs N Ndot v Av 0 δ := by
  ext i
  simp [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    inner_smul_right, PiLp.smul_apply]
  ring

theorem shear_smul (R F G : D → ℝ) (Vr : D → D) (v : D → ComplexVector)
    (c : D → ℝ) (x : D) :
    LinearWaveResidual.shear R F G Vr (fun y => c y • v y) x =
      c x • LinearWaveResidual.shear R F G Vr v x := by
  ext i
  fin_cases i <;> simp [LinearWaveResidual.shear, Complex.real_smul] <;> ring

/-- Scaling the actual homogeneous projected ODE by the frozen inverse
coefficient gives the signed principal equation, with its pressure constructed
from the same normal and action. No signed equation is an input. -/
theorem coefficients_principal_zero
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    (a : LinearWaveBounds.WaveCoefficients D)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T) {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) {P : ℕ → D → ℝ} (hv : MemClass s P 0 v)
    (hHf : FrozenAlong d.fast H) (hTf : FrozenAlong d.fast T)
    (hRf : FrozenAlong d.fast R) (hmf : FrozenAlong d.fast mask)
    (hK : ∀ n, a.frequency n ≠ 0)
    (hode : ∀ n x, x ∈ s.domain → along (d.fastField n) (v n) x =
      TangentProjection.projectedRhs (a.normal s d n x) (Ndot n x) (v n x)
        (A n x (v n x)) 0 (s.epsilon n * a.frequency n ^ 2 * ‖a.normal s d n x‖ ^ 2))
    (haction : ∀ n x, x ∈ s.domain → CurlClassBounds.complexify (A n x (v n x)) =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n)
        (d.radialField n) (fun y => CurlClassBounds.complexify (v n y)) x)
    (j : Fin 2) (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    (coefficients a s d H T R mask v Ndot A j).principal s d n x = 0 := by
  have hs := signedScalar_class hcov hR hm j
  have hsD := ((hs.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hvD := ((hv.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hfreeze := (signedScalar_frozen hHf hTf hRf hmf j).derivative n hsD
  have hfast : along (d.fastField n) (signedScalar s H T R mask j n) x = 0 := by
    simp only [along, LinearWaveBounds.GraphDirections.fastField, map_smul, hfreeze, smul_zero]
  have hd : along (d.fastField n) (signedVector s H T R mask v j n) x =
      TangentProjection.projectedRhs (a.normal s d n x) (Ndot n x)
        (signedVector s H T R mask v j n x) (A n x (signedVector s H T R mask v j n x))
        0 (s.epsilon n * a.frequency n ^ 2 * ‖a.normal s d n x‖ ^ 2) := by
    change along (d.fastField n) (fun y => signedScalar s H T R mask j n y • v n y) x = _
    rw [along_smul _ hsD hvD, hfast, zero_smul, zero_add, hode n x hx]
    simp only [signedVector, map_smul, projectedRhs_smul]
  have hact : CurlClassBounds.complexify (A n x (signedVector s H T R mask v j n x)) =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n)
        (d.radialField n) (fun y => CurlClassBounds.complexify (signedVector s H T R mask v j n y))
          x := by
    simp only [signedVector, map_smul]
    rw [shear_smul, haction n x hx]
  have hh := ParticularWaveBounds.principal_eq_neg_source_of_projected
    (s.epsilon n) (a.frequency n) (hK n) (a.radius n) (a.frequencyBase n) (a.axialBase n)
    (a.phase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
    (signedVector s H T R mask v j n) (Ndot n)
    (fun y => A n y (signedVector s H T R mask v j n y)) (fun _ => 0)
    (hsD.smul hvD) hd hact
  simpa only [coefficients, homogeneousCoefficients, LinearWaveBounds.WaveCoefficients.principal,
    LinearWaveBounds.WaveCoefficients.normal, map_zero, neg_zero] using hh

/-! ## Instantiation with the constructed primary phase and pulse -/

noncomputable def phaseMatrix {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) : ℕ → D → Mat2 :=
  PrimaryPulseBounds.chartCovariance pref (fun j => (F j).frame)
    (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L) χ

noncomputable def phaseFundamental {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ℕ → D → Space :=
  fun n x => PrimaryPulseBounds.normalizedPulse ((F j).frame n)
    ((F j).lam n) ((F j).u n) ((F j).L n) (χ n x)

noncomputable def phaseEnvelope {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ℕ → D → ℝ :=
  fun n x => PrimaryPulseBounds.referenceP ((F j).lam n) ((F j).u n)
    ((F j).L n) ((F j).L n * (χ n x).2)

theorem phaseFundamental_class {s : StripData D}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → χ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (j : Fin 2) : MemClass s (phaseEnvelope F χ j) 0 (phaseFundamental F χ j) := by
  have hp := (F j).pulse_jets.comp hχ hscale hmap
  exact hp.memClass s (fun _ => rfl) (fun _ => rfl)

theorem phaseMatrix_jets {s : StripData D}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n)
    (hpref : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => pref j n)) (i j : Fin 2) :
    PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
      (fun n x => phaseMatrix F pref χ n x i j) := by
  apply ((PrimaryPulseBounds.EnvelopeJets.of_polynomial
    (PrimaryPulseBounds.primaryCovariance_entry_polynomial U pref (fun j => (F j).frame)
      (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L) hpref
      (fun j => (F j).pulse_jets) (fun j => (F j).lam_pos) (fun j => (F j).u_pos)
      (fun j => (F j).L_pos) i j)).comp
        (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale hmap).to_polynomial
  intro n x hx
  rfl

/-- The matrix jets in this constructor are proved from the actual primary
ODE, including its Gaussian initial normalization and slot integrals. -/
noncomputable def phaseControl {s : StripData D}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (T : ℕ → D → Vec2)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ U.carrier n)
    (hpref : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => pref j n))
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (phaseMatrix F pref χ n
        x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * phaseMatrix F pref χ n x i j| ≤ M)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (phaseMatrix F pref χ n x) (T n x) j) :
    CovarianceControl s (phaseMatrix F pref χ) T where
  matrix_jets := phaseMatrix_jets F pref χ hscale hχ hmap hpref
  target_jets := hT
  zeta_pos := hζ
  b := b
  M := M
  c := c
  b_pos := hb
  M_one := hM
  c_pos := hc
  determinant := hdet
  entries := hentry
  lower := hlower

/-- Same phase fundamental, same integrated matrix, arbitrary signed target.
There is no assumed estimate for the inverse, the fundamental, or the result. -/
theorem phase_signedVector_class {s : StripData D}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → χ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (hpref : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => pref j n))
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (phaseMatrix F pref χ n
        x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * phaseMatrix F pref χ n x i j| ≤ M)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (phaseMatrix F pref χ n x) (T n x) j)
    {B κ : ℝ} (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (j : Fin 2) :
    WaveClass s (phaseEnvelope F χ j) (B - κ)
      (signedVector s (phaseMatrix F pref χ) T R mask (phaseFundamental F χ j) j) := by
  have hc := phaseControl F pref χ T hscale hχ (fun n x hx => (hmap n x hx).1)
    hpref hT hζ hb hM hc hdet hentry hlower
  have hh := signedVector_class hc hR hm (phaseFundamental_class F χ hscale hχ hmap j) j
  convert! hh using 1
  ring

/-! ## Literal harmonic blocks, with the same carrier metadata -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem conjugatePair_apply (a : D → ℂ) (j : ℤ) (x : D) :
    ErrorHarmonics.conjugatePair 1 a j x =
      (if j = 1 then a x / 2 else 0) + conj (if -j = 1 then a x / 2 else 0) := by
  classical
  change Finsupp.single (1 : ℤ) (fun x => a x / 2) j x +
    conj (Finsupp.single (1 : ℤ) (fun x => a x / 2) (-j) x) = _
  by_cases hj : j = 1 <;> by_cases hjn : -j = 1 <;>
    simp [hj, hjn, eq_comm]

noncomputable def coefficientBlock (frequency : ℕ → ℝ) (phase : ℕ → D → ℝ)
    (angularFrequency : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    CorrectionState.HarmonicBlock D where
  velocity n i := ErrorHarmonics.conjugatePair 1 (fun x => v n x i)
  pressure n := ErrorHarmonics.conjugatePair 1 (p n)
  frequency := frequency
  phase := phase
  angularFrequency := angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_band (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (coefficientBlock k Φ kp v p).BandLimited 1 :=
  ⟨fun n i => ErrorHarmonics.band_conjugatePair 1 (fun x => v n x i),
    fun n => ErrorHarmonics.band_conjugatePair 1 (p n)⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_symmetric (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (∀ n i, HarmonicFields.ConjugateSymmetric ((coefficientBlock k Φ kp v p).velocity n i)) ∧
    ∀ n, HarmonicFields.ConjugateSymmetric ((coefficientBlock k Φ kp v p).pressure n) :=
  ⟨fun n i => ErrorHarmonics.conjugatePair_symmetric 1 (fun x => v n x i),
    fun n => ErrorHarmonics.conjugatePair_symmetric 1 (p n)⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_zero_coefficient (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (∀ n i, (coefficientBlock k Φ kp v p).velocity n i 0 = 0) ∧
    ∀ n, (coefficientBlock k Φ kp v p).pressure n 0 = 0 := by
  constructor
  · intro n i
    ext x
    simp only [coefficientBlock, conjugatePair_apply]
    norm_num
  · intro n
    ext x
    simp only [coefficientBlock, conjugatePair_apply]
    norm_num

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_velocity (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (coefficientBlock k Φ kp v p).oscillation n x i =
      (v n x.1 i * HarmonicFields.character 1 (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  exact ErrorHarmonics.pairedBlock_evaluation 1 k Φ kp v n x i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_pressure (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) (n : ℕ) (x : D × ℝ) :
    (coefficientBlock k Φ kp v p).oscillatoryPressure n x =
      (p n x.1 * HarmonicFields.character 1 (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  have h := congrArg Complex.re (ErrorHarmonics.field_conjugatePair 1 (p n) (k n) (Φ n) (kp n) x)
  simp only [Complex.ofReal_re] at h
  exact h

theorem conjugatePair_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {a : ℕ → D → ℂ} (ha : MemClass s w α a) (j : ℤ) :
    MemClass s w α (fun n x => ErrorHarmonics.conjugatePair 1 (a n) j x) := by
  have hp := LinearWaveBounds.constant_complex_mul ha (1 / 2)
  have hn := hp.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  by_cases hj : j = 1
  · subst j
    simpa [conjugatePair_apply, div_eq_mul_inv,
      mul_comm] using hp
  by_cases hjn : -j = 1
  · simpa [conjugatePair_apply, hj, hjn, div_eq_mul_inv, mul_comm] using hn
  · simpa [conjugatePair_apply, hj, hjn] using
      (MemClass.zero (E := ℂ) (α := α) ha.weight_nonneg)

theorem coefficientBlock_classes {s : StripData D} {P : ℕ → D → ℝ} {α γ : ℝ}
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    {v : ℕ → D → ComplexVector} {p : ℕ → D → ℂ}
    (hv : WaveClass s P α v) (hp : WaveClass s P γ p) :
    (coefficientBlock k Φ kp v p).WaveBounds s P α ∧
    (coefficientBlock k Φ kp v p).PressureBounds s P γ := by
  exact ⟨fun i j _ => conjugatePair_class (CurlClassBounds.class_component hv i) j,
    fun j _ => conjugatePair_class hp j⟩

/-- The full cylindrical construction is evaluated at angle zero to obtain
the coefficient algebra. Its physical angle is reintroduced by the unchanged
integer carrier, as proved in `blockOfCoefficients_represents`. -/
noncomputable def blockOfCoefficients (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (kp : ℕ → ℤ) : CorrectionState.HarmonicBlock D :=
  coefficientBlock a.frequency (fun n x => a.phase n (x,0)) kp
    (fun n x => a.amplitude n (x,0)) (fun n x => a.pressure n (x,0))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem blockOfCoefficients_represents
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent a.amplitude)
    (hp : ErrorHarmonics.AngleIndependent a.pressure)
    (hphase : ∀ n x θ, a.frequency n * a.phase n (x,θ) =
      a.frequency n * a.phase n (x,0) + (kp n : ℝ) * θ) :
    (blockOfCoefficients a kp).oscillation =
      (fun n x i => (vectorMode (a.frequency n) (a.phase n) (a.amplitude n) x i).re) ∧
    (blockOfCoefficients a kp).oscillatoryPressure =
      (fun n x => (mode (a.frequency n) (a.phase n) (a.pressure n) x).re) := by
  constructor
  · funext n x i
    rw [blockOfCoefficients, coefficientBlock_velocity]
    have hc := HarmonicFields.character_eq_carrier 1 (a.frequency n) (a.phase n) x
    simp only [Int.cast_one, mul_one] at hc
    rw [← hphase, hc]
    simp only [vectorMode, mode, ha n x.1 x.2]
  · funext n x
    rw [blockOfCoefficients, coefficientBlock_pressure]
    have hc := HarmonicFields.character_eq_carrier 1 (a.frequency n) (a.phase n) x
    simp only [Int.cast_one, mul_one] at hc
    rw [← hphase, hc]
    simp only [mode, hp n x.1 x.2]

/-! ## The bar operation preserves the actual flat mean class -/

theorem meanClass_radialAverage
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → ℝ × E → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hglobal : MeanMomentBounds.GlobalBandJets ε S α f)
    (hclass : MeanClass (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR
      ε S hε hεone hS) α f)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (hL : ‖L‖ ≤ 1) (v : ℝ × E)
    (hpreserve : ∀ x (t : ℝ), (L x + t • v).1 = x.1) :
    MeanClass (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR
      ε S hε hεone hS) α (fun n => MeanMomentBounds.affineAverage L v 0 1 (f n)) := by
  let s : StripData (ℝ × E) :=
    WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS
  refine ⟨hclass.weight_nonneg,
    fun n => (MeanMomentBounds.affineAverage_contDiff L v 0 1 (hf n)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hclass.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hall : ∀ k : ℕ, ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ k (f n) y‖ ≤ A := by
    intro k
    obtain ⟨A, _, q, hA⟩ := hglobal k
    exact ⟨A * ε n ^ α * S n ^ q, fun y => hA n y k le_rfl⟩
  have hh := MeanMomentBounds.affineAverage_jet_bound L hL v zero_le_one (hf n) hall j x
    (majorant s (fun _ y => s.zeta y) α C p n x) (fun t _ => by
      have hx' : L x + t • v ∈ s.domain := by
        change (L x + t • v).1 ∈ Ioo a b
        rw [hpreserve]
        exact hx
      have hh := hb n (L x + t • v) hx' j hj
      simpa only [s, majorant, StripData.growth, WeightedRadialPrimitive.logStripData,
        hpreserve] using hh)
  simpa only [sub_zero, mul_one] using hh

theorem meanClass_liftedTorusAverage
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift E → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR
      ε S hε hεone hS) α f) :
    MeanClass (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR
      ε S hε hεone hS) α (fun n => MeanMomentBounds.liftedTorusAverage (f n)) := by
  have hg := MeanMomentBounds.meanClass_globalBandJets ha hcL hcR ε S hε hεone hS hf hs hclass
  have hi := meanClass_radialAverage ha hcL hcR ε S hε hεone hS hf hg hclass
    MeanMomentBounds.eraseAuxX MeanMomentBounds.norm_eraseAuxX_le MeanMomentBounds.auxX
    (fun x t => by simp only [MeanMomentBounds.eraseAuxX_add_smul])
  have hgi := hg.affineAverage hf MeanMomentBounds.eraseAuxX MeanMomentBounds.norm_eraseAuxX_le
    MeanMomentBounds.auxX zero_le_one
  have ho := meanClass_radialAverage ha hcL hcR ε S hε hεone hS
    (fun n => MeanMomentBounds.affineAverage_contDiff _ _ _ _ (hf n)) hgi hi
    MeanMomentBounds.eraseAuxY MeanMomentBounds.norm_eraseAuxY_le MeanMomentBounds.auxY
    (fun x t => by simp only [MeanMomentBounds.eraseAuxY_add_smul])
  simpa only [MeanMomentBounds.liftedTorusAverage_eq_affine] using ho

theorem sigma_liftedTorusAverage (p : SignedStressPrimitive.Patch) (e : ℕ)
    (f : PressureStream.Lift E → ℝ) (x : PressureStream.Lift E) :
    SignedStressPrimitive.sigma p e (MeanMomentBounds.liftedTorusAverage f) x =
      SignedStressPrimitive.barSigma p e f (x.1, x.2.1) := by
  rcases x with ⟨r,z,Y⟩
  simp only [SignedStressPrimitive.sigma, SignedStressPrimitive.barSigma,
    SignedStressPrimitive.primitive, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral, TransportPrimitive.totalIntegral,
    SignedStressPrimitive.weightedSource, MeanMomentBounds.liftedTorusAverage,
    TransportPrimitive.shift, zero_mul, zero_smul, Prod.mk_add_mk, add_zero]

theorem meanClass_barSigma
    (p : SignedStressPrimitive.Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift E → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported p.a p.b (f n))
    (hclass : MeanClass (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR
      ε S hε hεone hS) α f) :
    MeanClass (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR
      ε S hε hεone hS) α
      (fun n (x : PressureStream.Lift E) => SignedStressPrimitive.barSigma p e (f n) (x.1,x.2.1))
        := by
  have hb := meanClass_liftedTorusAverage p.a_pos hcL hcR ε S hε hεone hS hf hs hclass
  have hh := SignedStressPrimitive.meanClass_sigma p e hcL hcR ε S hε hεone hS α
    (fun n => MeanMomentBounds.liftedTorusAverage (f n))
    (fun n => MeanMomentBounds.liftedTorusAverage_contDiff (hf n))
    (fun n => MeanMomentBounds.liftedTorusAverage_supported (hs n)) hb
  change MeanClass _ α (fun n x =>
    SignedStressPrimitive.sigma p e (MeanMomentBounds.liftedTorusAverage (f n)) x) at hh
  simp only [sigma_liftedTorusAverage] at hh
  exact hh

noncomputable def normalizedRequest (s : StripData (PressureStream.Lift E))
    (p : SignedStressPrimitive.Patch) (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) : ℕ → PressureStream.Lift E → Vec2 :=
  fun n x => (s.epsilon n)⁻¹ • requestedStress p c u n (x.1,x.2.1)

theorem normalizedRequest_frozen (s : StripData (PressureStream.Lift E))
    (p : SignedStressPrimitive.Patch) (c : CorrectionState.Context (PressureStream.Lift E))
    (u : CorrectionState.State (PressureStream.Lift E)) (v : PressureStream.Plane) :
    FrozenAlong (0,(0,v)) (normalizedRequest s p c u) := by
  rintro n ⟨r,z,Y⟩ t
  simp only [normalizedRequest, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

theorem normalizedRequest_class
    (p : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (c : CorrectionState.Context (PressureStream.Lift E)) (u : CorrectionState.State
      (PressureStream.Lift E))
    {α : ℝ} (ht : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hst : ∀ n, RadialAlias.RadiallySupported p.a p.b (u.thetaResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.a p.b (u.axialResidual c n))
    (hct : MeanClass (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR
      ε S hε hεone hS) α (u.thetaResidual c))
    (hcz : MeanClass (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR
      ε S hε hεone hS) α (u.axialResidual c)) (i : Fin 2) :
    MeanClass (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR
      ε S hε hεone hS) (α - 1)
      (fun n x => normalizedRequest
        (WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR ε S hε hεone hS)
        p c u n x i) := by
  let s : StripData (PressureStream.Lift E) :=
    WeightedRadialPrimitive.logStripData p.a p.b cL cR p.a_pos hcL hcR ε S hε hεone hS
  have hbar : MeanClass s α (fun n (x : PressureStream.Lift E) => requestedStress p c u n
    (x.1,x.2.1) i) := by
    fin_cases i
    · exact meanClass_barSigma p 2 hcL hcR ε S hε hεone hS ht hst hct
    · exact meanClass_barSigma p 1 hcL hcR ε S hε hεone hS hz hsz hcz
  have hh := hbar.band_smul (bandBound_rpow s (-1))
  simpa only [normalizedRequest, Pi.smul_apply, smul_eq_mul, Real.rpow_neg_one, sub_eq_add_neg]
    using hh

/-! ## Angular independence is proved before taking a zero-angle section -/

structure AngularInputs (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (a : LinearWaveBounds.WaveCoefficients D) (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2)
    (mask : ℕ → D → ℝ) (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (ψ : ℕ → D → ℝ) (m : ℕ → ℝ) : Prop where
  radius : FrozenAlong d.angular a.radius
  radial_base : FrozenAlong d.angular a.radialBase
  frequency_base : FrozenAlong d.angular a.frequencyBase
  axial_base : FrozenAlong d.angular a.axialBase
  radial_profile : CopyAngularInvariance.Invariant d.angular d.radialProfile
  phase : ∀ n, CopyAngularInvariance.AffinePhase d.angular (m n) (a.phase n)
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain
  matrix : FrozenAlong d.angular H
  primary_target : FrozenAlong d.angular T
  signed_target : FrozenAlong d.angular R
  mask : FrozenAlong d.angular mask
  fundamental : FrozenAlong d.angular v
  normal_motion : FrozenAlong d.angular Ndot
  action : FrozenAlong d.angular A
  cutoff : FrozenAlong d.angular ψ

namespace AngularInputs

variable {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
  {a : LinearWaveBounds.WaveCoefficients D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
  {mask : ℕ → D → ℝ} {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
  {ψ : ℕ → D → ℝ} {m : ℕ → ℝ}

theorem radialField (h : AngularInputs s d a H T R mask v Ndot A ψ m) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (d.radialField n) := by
  intro x t
  simp only [LinearWaveBounds.GraphDirections.radialField, h.radial_profile x t]

theorem normal (h : AngularInputs s d a H T R mask v Ndot A ψ m) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.normal s d n) :=
  CopyAngularInvariance.phaseNormal_invariant (h.radius n) (h.radialField n)
    (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _) (h.phase n)

theorem amplitude (h : AngularInputs s d a H T R mask v Ndot A ψ m) (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((coefficients a s d H T R mask v Ndot A j).amplitude
      n) := by
  intro x t
  simp only [coefficients, homogeneousCoefficients, signedVector, signedScalar,
    h.matrix n x t, h.primary_target n x t, h.signed_target n x t,
    h.mask n x t, h.fundamental n x t]

theorem pressure (h : AngularInputs s d a H T R mask v Ndot A ψ m) (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((coefficients a s d H T R mask v Ndot A j).pressure
      n) := by
  intro x t
  simp only [coefficients, homogeneousCoefficients, ParticularWaveBounds.projectedPressure,
    signedVector, signedScalar, h.matrix n x t, h.primary_target n x t,
    h.signed_target n x t, h.mask n x t, h.fundamental n x t, h.action n x t,
    h.normal_motion n x t, h.normal n x t]

theorem corrected_amplitude (h : AngularInputs s d a H T R mask v Ndot A ψ m)
    (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular
      (((coefficients a s d H T R mask v Ndot A j).corrected s d ψ).amplitude n) := by
  exact CopyAngularInvariance.corrected_amplitude_invariant
    (a := coefficients a s d H T R mask v Ndot A j) (s := s) (d := d) ψ h.radius h.radialField
    (fun _ => CopyAngularInvariance.Invariant.const _) (fun n => ⟨m n, h.phase n⟩)
    (h.amplitude j) h.cutoff n

theorem corrected_pressure (h : AngularInputs s d a H T R mask v Ndot A ψ m)
    (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular
      (((coefficients a s d H T R mask v Ndot A j).corrected s d ψ).pressure n) :=
  CopyAngularInvariance.corrected_pressure_invariant
    (a := coefficients a s d H T R mask v Ndot A j) (s := s) (d := d) ψ (h.pressure j) h.cutoff n

theorem exactConditions (h : AngularInputs s d a H T R mask v Ndot A ψ m)
    (hRne : ∀ n x, x ∈ s.domain → a.radius n x ≠ 0)
    (hDrR : ∀ n x, x ∈ s.domain → along (d.radialField n) (a.radius n) x = 1)
    (j : Fin 2) : LinearWaveBounds.ExactConditions s d
      ((coefficients a s d H T R mask v Ndot A j).corrected s d ψ) := by
  exact CopyAngularInvariance.exactConditions_corrected_of_invariants
    (a := coefficients a s d H T R mask v Ndot A j) (s := s) (d := d) ψ h.phase_smooth hRne hDrR
    h.radius h.radial_base h.frequency_base h.axial_base h.radialField
    (fun _ => CopyAngularInvariance.Invariant.const _) (fun n => ⟨m n, h.phase n⟩)
    (h.amplitude j) (h.pressure j) h.cutoff

end AngularInputs

theorem signedBlock_represents
    {s : StripData (D × ℝ)} {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {H : ℕ → D × ℝ → Mat2} {T R : ℕ → D × ℝ → Vec2} {mask : ℕ → D × ℝ → ℝ}
    {v Ndot : ℕ → D × ℝ → Space} {A : ℕ → D × ℝ → Space →L[ℝ] Space}
    {ψ : ℕ → D × ℝ → ℝ} {m : ℕ → ℝ}
    (h : AngularInputs s d a H T R mask v Ndot A ψ m)
    (hθ : d.angular = (0,1)) (kp : ℕ → ℤ) (hkp : ∀ n, a.frequency n * m n = (kp n : ℝ))
    (j : Fin 2) :
    let z := (coefficients a s d H T R mask v Ndot A j).corrected s d ψ
    (blockOfCoefficients z kp).oscillation =
      (fun n x i => (vectorMode (a.frequency n) (a.phase n) (z.amplitude n) x i).re) ∧
    (blockOfCoefficients z kp).oscillatoryPressure =
      (fun n x => (mode (a.frequency n) (a.phase n) (z.pressure n) x).re) := by
  apply blockOfCoefficients_represents
  · intro n x t
    apply CopyAngularInvariance.invariant_eq_zeroSlice
    simpa only [hθ] using h.corrected_amplitude j n
  · intro n x t
    apply CopyAngularInvariance.invariant_eq_zeroSlice
    simpa only [hθ] using h.corrected_pressure j n
  · intro n x t
    change a.frequency n * a.phase n (x,t) = a.frequency n * a.phase n (x,0) + _
    have hp := CopyAngularInvariance.affinePhase_eq_zeroSlice (by simpa only [hθ] using h.phase n)
      x t
    rw [hp, mul_add, ← mul_assoc, hkp]

/-! ## Restriction of actual coefficient jets to the angular section -/

noncomputable def zeroSection : D →L[ℝ] (D × ℝ) := (ContinuousLinearMap.id ℝ D).prod 0

theorem zeroSection_norm_le : ‖zeroSection (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [zeroSection, Prod.norm_def]

noncomputable def sectionStrip (s : StripData (D × ℝ)) : StripData D where
  domain := (zeroSection (D := D)) ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage (zeroSection (D := D)).continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (zeroSection x)
  delta_pos := fun _ hx => s.delta_pos _ hx
  zeta := fun x => s.zeta (zeroSection x)
  zeta_smooth := s.zeta_smooth.comp (zeroSection (D := D)).contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun _ hx => s.zeta_nonneg _ hx

theorem class_zeroSection {s : StripData (D × ℝ)} {w : ℕ → D × ℝ → ℝ} {α : ℝ}
    {f : ℕ → D × ℝ → E} (hf : MemClass s w α f) :
    MemClass (sectionStrip s) (fun n x => w n (x,0)) α (fun n x => f n (x,0)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n _ hx,
    fun n => (hf.smooth n).comp (zeroSection (D := D)).contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hc := PhaseJetBounds.norm_jet_comp_linear s.isOpen_domain (hf.smooth n)
    (zeroSection (D := D)) hx j
  have hpow : ‖zeroSection (D := D)‖ ^ j ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) zeroSection_norm_le
  have hh := hc.trans (mul_le_of_le_one_right (norm_nonneg _) hpow)
  exact hh.trans (hb n (x,0) hx j hj)

theorem blockOfCoefficients_classes
    {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α γ : ℝ}
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (ha : WaveClass s P α a.amplitude) (hp : WaveClass s P γ a.pressure) :
    (blockOfCoefficients a kp).WaveBounds (sectionStrip s) (fun n x => P n (x,0)) α ∧
    (blockOfCoefficients a kp).PressureBounds (sectionStrip s) (fun n x => P n (x,0)) γ :=
  coefficientBlock_classes a.frequency (fun n x => a.phase n (x,0)) kp
    (class_zeroSection ha) (class_zeroSection hp)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_re_field (c : HarmonicFields.Coefficients D) (k : ℝ)
    (Φ : D → ℝ) (kp : ℤ) (x : D) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, (HarmonicFields.field c k Φ kp (x,θ)).re) / (2 * Real.pi) =
      (HarmonicFields.angularMean (fun θ => HarmonicFields.field c k Φ kp (x,θ))).re := by
  have hi := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
    ((HarmonicFields.field_angular_continuous c k Φ kp x).intervalIntegrable (0 : ℝ) (2 * Real.pi))
  change (∫ θ in (0 : ℝ)..2 * Real.pi, (HarmonicFields.field c k Φ kp (x,θ)).re) =
    (∫ θ in (0 : ℝ)..2 * Real.pi, HarmonicFields.field c k Φ kp (x,θ)).re at hi
  rw [hi]
  simp [HarmonicFields.angularMean, HarmonicFields.period, Complex.mul_re, div_eq_mul_inv,
    ← Complex.ofReal_inv, mul_comm]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- These are actual angular integrals of the real velocity and pressure. -/
theorem coefficientBlock_mean_zero (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) (hkp : ∀ n, kp n ≠ 0) :
    (∀ i, CorrectionState.angularAverage (fun n x => (coefficientBlock k Φ kp v p).oscillation n x
      i) = 0) ∧
    CorrectionState.angularAverage (coefficientBlock k Φ kp v p).oscillatoryPressure = 0 := by
  constructor
  · intro i
    funext n x
    change (∫ θ in (0 : ℝ)..2 * Real.pi,
      (HarmonicFields.field ((coefficientBlock k Φ kp v p).velocity n i) (k n) (Φ n) (kp n)
        (x,θ)).re) /
      (2 * Real.pi) = 0
    rw [angularAverage_re_field, HarmonicFields.angularMean_field _ _ _ (hkp n),
      (coefficientBlock_zero_coefficient k Φ kp v p).1 n i]
    rfl
  · funext n x
    change (∫ θ in (0 : ℝ)..2 * Real.pi,
      (HarmonicFields.field ((coefficientBlock k Φ kp v p).pressure n) (k n) (Φ n) (kp n)
        (x,θ)).re) /
      (2 * Real.pi) = 0
    rw [angularAverage_re_field, HarmonicFields.angularMean_field _ _ _ (hkp n),
      (coefficientBlock_zero_coefficient k Φ kp v p).2 n]
    rfl

/-! ## Actual homogeneous ODE under the native clock -/

theorem normalizedPulse_along
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (f : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (f.coefficient 1) (U ×ˢ Icc 0 L))
    (χ : D → Q × ℝ) (V : D → D) {x : D}
    (hp : (χ x).1 ∈ U) (ht : (χ x).2 ∈ Ioo (0 : ℝ) 1)
    (hk : f.Kinematics (χ x).1 (Icc 0 L))
    (hv : DifferentiableAt ℝ (fun y => PrimaryPulseBounds.normalizedPulse f lam u L (χ y)) x)
    (hclock : ∀ t : ℝ, χ (x + t • V x) = ((χ x).1, (χ x).2 + t / L)) :
    along V (fun y => PrimaryPulseBounds.normalizedPulse f lam u L (χ y)) x =
      TangentProjection.projectedRhs (f.normal ((χ x).1,L*(χ x).2))
        (f.normalMotion ((χ x).1,L*(χ x).2)) (PrimaryPulseBounds.normalizedPulse f lam u L (χ x))
        (MovingFrameODE.baseAction (f.F ((χ x).1,L*(χ x).2)) (f.shear ((χ x).1,L*(χ x).2))
          (PrimaryPulseBounds.normalizedPulse f lam u L (χ x))) 0 (f.viscosity ((χ x).1,L*(χ x).2))
            := by
  have hd := PrimaryPulseBounds.normalizedPulse_hasDerivAt f lam u hL U hA hp hk ht
  have ht' : HasDerivAt (fun t : ℝ => (χ x).2 + t / L) (1 / L) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const L).const_add (χ x).2)
  have hd' : HasDerivAt (fun t : ℝ => PrimaryPulseBounds.normalizedPulse f lam u L
      ((χ x).1, (χ x).2 + t / L)) ((1 / L) • (L •
        TangentProjection.projectedRhs (f.normal ((χ x).1,L*(χ x).2))
          (f.normalMotion ((χ x).1,L*(χ x).2)) (PrimaryPulseBounds.normalizedPulse f lam u L (χ x))
          (MovingFrameODE.baseAction (f.F ((χ x).1,L*(χ x).2)) (f.shear ((χ x).1,L*(χ x).2))
            (PrimaryPulseBounds.normalizedPulse f lam u L (χ x))) 0 (f.viscosity ((χ x).1,L*(χ
              x).2)))) 0 := by
    simpa only [Prod.mk.eta, Function.comp_def] using hd.scomp_of_eq (0 : ℝ) ht' (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • V x) (V x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (V x)).const_add x
  have hv' : HasDerivAt (fun t : ℝ => PrimaryPulseBounds.normalizedPulse f lam u L (χ (x+t•V x)))
      (along V (fun y => PrimaryPulseBounds.normalizedPulse f lam u L (χ y)) x) 0 := by
    simpa only [along, Function.comp_def] using hv.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by
      simp)
  simp only [hclock] at hv'
  have he := hv'.unique hd'
  simpa only [smul_smul, one_div, inv_mul_cancel₀ hL.ne', one_smul, Prod.mk.eta] using he

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem phaseFundamental_tangent {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) (n : ℕ) (x : D) :
    ⟪((F j).frame n).normal ((χ n x).1, (F j).L n * (χ n x).2), phaseFundamental F χ j n x⟫_ℝ = 0
      := by
  exact ((F j).frame n).ambient_tangent _ _

theorem phase_coefficients_principal_zero
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    (a : LinearWaveBounds.WaveCoefficients D)
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) {T R : ℕ → D → Vec2} {mask : ℕ → D → ℝ}
    {Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → χ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (hcov : CovarianceControl s (phaseMatrix F pref χ) T) {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i)) (hm : UnweightedClass s 0 mask)
    (hHf : FrozenAlong d.fast (phaseMatrix F pref χ)) (hTf : FrozenAlong d.fast T)
    (hRf : FrozenAlong d.fast R) (hmf : FrozenAlong d.fast mask)
    (hK : ∀ n, a.frequency n ≠ 0) (j : Fin 2)
    (hcoef : ∀ n, ContinuousOn (((F j).frame n).coefficient 1) (U.carrier n ×ˢ Icc 0 ((F j).L n)))
    (hkin : ∀ n x, x ∈ s.domain → ((F j).frame n).Kinematics (χ n x).1 (Icc 0 ((F j).L n)))
    (hclock : ∀ n x, x ∈ s.domain → ∀ t : ℝ,
      χ n (x + t • d.fastField n x) = ((χ n x).1, (χ n x).2 + t / (F j).L n))
    (hnormal : ∀ n x, x ∈ s.domain → ((F j).frame n).normal ((χ n x).1,(F j).L n*(χ n x).2) =
      a.normal s d n x)
    (hmotion : ∀ n x, x ∈ s.domain → ((F j).frame n).normalMotion ((χ n x).1,(F j).L n*(χ n x).2) =
      Ndot n x)
    (haction : ∀ n x, x ∈ s.domain → ∀ z : Space,
      MovingFrameODE.baseAction (((F j).frame n).F ((χ n x).1,(F j).L n*(χ n x).2))
        (((F j).frame n).shear ((χ n x).1,(F j).L n*(χ n x).2)) z = A n x z)
    (hdamp : ∀ n x, x ∈ s.domain → ((F j).frame n).viscosity ((χ n x).1,(F j).L n*(χ n x).2) =
      s.epsilon n * a.frequency n ^ 2 * ‖a.normal s d n x‖ ^ 2)
    (hphysical : ∀ n x, x ∈ s.domain → CurlClassBounds.complexify (A n x (phaseFundamental F χ j n
      x)) =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n) (d.radialField n)
        (fun y => CurlClassBounds.complexify (phaseFundamental F χ j n y)) x) :
    ∀ n x, x ∈ s.domain →
      (coefficients a s d (phaseMatrix F pref χ) T R mask (phaseFundamental F χ j) Ndot A
        j).principal s d n x = 0 := by
  have hv := phaseFundamental_class F χ hscale hχ hmap j
  apply coefficients_principal_zero a hcov hR hm hv hHf hTf hRf hmf hK _ hphysical j
  intro n x hx
  have hd := normalizedPulse_along ((F j).frame n) ((F j).lam n) ((F j).u n) ((F j).L_pos n)
    (U.carrier n) (hcoef n) (χ n) (d.fastField n) (hmap n x hx).1 (hmap n x hx).2 (hkin n x hx)
    (((hv.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)) (hclock n
      x hx)
  simp only [phaseFundamental, hnormal n x hx, hmotion n x hx, haction n x hx, hdamp n x hx] at hd ⊢
  exact hd

/-! ## The constructed curl, pressure, and retained linear error -/

noncomputable def exactCoefficients (a : LinearWaveBounds.WaveCoefficients D)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (ψ : ℕ → D → ℝ) (j : Fin 2) : LinearWaveBounds.WaveCoefficients D :=
  (coefficients a s d H T R mask v Ndot A j).corrected s d ψ

theorem signed_bounds
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    {a : LinearWaveBounds.WaveCoefficients D} {P₀ P : ℕ → D → ℝ} {α₀ B κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a) (hκ : κ ≤ 1 / 2)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask ψ : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    {radius : D → ℝ} (hradius : a.radius = fun _ => radius)
    (hψ : UnweightedClass s 0 ψ) (j : Fin 2) :
    let z := coefficients a s d H T R mask v Ndot A j
    WaveClass s P (B - κ) (z.corrected s d ψ).amplitude ∧
    WaveClass s P (B + 1 / 2 - κ) (z.corrected s d ψ).pressure ∧
    WaveClass s P (B + 1 / 2 - 2 * κ)
      (fun n x => (z.corrected s d ψ).amplitude n x - (z.withCutoff ψ).amplitude n x) ∧
    WaveClass s P (B + 1 / 2 - 4 * κ) (z.constructedGood s d ψ) := by
  let z := coefficients a s d H T R mask v Ndot A j
  have hi : LinearWaveBounds.InputBounds s P (B - κ) κ d z := by
    convert! coefficients_inputBounds hbase hcov hR hm hv hN hNdot hA hb hlo hhi hK j using 1
    ring
  have hc := (hi.with_cutoff hψ).curlCorrection_class hradius hN hb hlo hhi hK
  have he := (hi.with_cutoff hψ).add_curl_amplitude hκ
    (fun i => CurlClassBounds.class_component hc i)
  have hdiff : WaveClass s P ((B - κ) + 1 / 2 - κ)
      (fun n x => (z.corrected s d ψ).amplitude n x - (z.withCutoff ψ).amplitude n x) := by
    apply LinearWaveBounds.class_congr hc
    intro n x hx
    simp only [LinearWaveBounds.WaveCoefficients.corrected,
      LinearWaveBounds.WaveCoefficients.addAmplitude, add_sub_cancel_left]
  refine ⟨LinearWaveBounds.component_classes he.amplitude, ?_, ?_, ?_⟩
  · convert! he.pressure using 1
    ring
  · convert! hdiff using 1
    ring
  · convert! hi.constructed_goodCoefficient_class hκ hψ hradius hN hb hlo hhi hK using 1
    ring

theorem normalDot_complexify (N v : Space) :
    normalDot N (CurlClassBounds.complexify v) = (⟪N,v⟫_ℝ : ℂ) := by
  simp [normalDot, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem coefficients_tangent {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    (a : LinearWaveBounds.WaveCoefficients D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (ht : ∀ n x, x ∈ s.domain → ⟪a.normal s d n x, v n x⟫_ℝ = 0) (j : Fin 2)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    normalDot ((coefficients a s d H T R mask v Ndot A j).normal s d n x)
      ((coefficients a s d H T R mask v Ndot A j).amplitude n x) = 0 := by
  change normalDot (a.normal s d n x) (CurlClassBounds.complexify (signedScalar s H T R mask j n x
    • v n x)) = 0
  rw [normalDot_complexify, inner_smul_right, ht n x hx, mul_zero]
  rfl

theorem signed_curl_realization
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    {a : LinearWaveBounds.WaveCoefficients D} {P₀ P : ℕ → D → ℝ} {α₀ β κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask ψ : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T) (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    (hψ : UnweightedClass s 0 ψ) (j : Fin 2) (n : ℕ)
    (G : CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hfreq : a.frequency n ≠ 0) (hphase : ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (ht : ∀ n x, x ∈ s.domain → ⟪a.normal s d n x, v n x⟫_ℝ = 0) :
    let z := coefficients a s d H T R mask v Ndot A j
    ∀ x ∈ s.domain,
      CurlClassBounds.cylindricalCurl (a.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) ((z.withCutoff ψ).curlPotential s d n) x =
          vectorMode (a.frequency n) (a.phase n) ((z.corrected s d ψ).amplitude n) x ∧
      cylindricalDivergence (a.radius n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
        (vectorMode (a.frequency n) (a.phase n) ((z.corrected s d ψ).amplitude n)) x = 0 := by
  dsimp only
  have hi := coefficients_inputBounds hbase hcov hR hm hv hN hNdot hA hb hlo hhi hK j
  have hn : ∀ x ∈ s.domain, a.normal s d n x ≠ 0 := by
    intro x hx hz
    have h := hlo n x hx
    rw [hz, norm_zero] at h
    exact (not_le_of_gt hb) h
  intro x hx
  exact ⟨LinearWaveBounds.corrected_realizes_curl hi hψ n G hfreq hphase hn
      (fun x hx => coefficients_tangent a H T R mask v Ndot A ht j n hx) hx,
    LinearWaveBounds.corrected_divergence hi hψ n G hfreq hphase hn
      (fun x hx => coefficients_tangent a H T R mask v Ndot A ht j n hx) hx⟩

/-- Exact residual identity for the signed increment. The slot derivative
is kept as a separate nonzero field and is not included in the good bound. -/
theorem signed_linear_identity
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    {a : LinearWaveBounds.WaveCoefficients D} {P₀ P : ℕ → D → ℝ} {α₀ β κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a) (hκ : κ ≤ 1 / 2)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask ψ : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T) (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    {radius : D → ℝ} (hradius : a.radius = fun _ => radius)
    (hψ : UnweightedClass s 0 ψ) {m : ℕ → ℝ}
    (hangle : AngularInputs s d a H T R mask v Ndot A ψ m)
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain (a.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n))
    (hHf : FrozenAlong d.fast H) (hTf : FrozenAlong d.fast T)
    (hRf : FrozenAlong d.fast R) (hmf : FrozenAlong d.fast mask)
    (hfreq : ∀ n, a.frequency n ≠ 0)
    (hode : ∀ n x, x ∈ s.domain → along (d.fastField n) (v n) x =
      TangentProjection.projectedRhs (a.normal s d n x) (Ndot n x) (v n x)
        (A n x (v n x)) 0 (s.epsilon n * a.frequency n ^ 2 * ‖a.normal s d n x‖ ^ 2))
    (haction : ∀ n x, x ∈ s.domain → CurlClassBounds.complexify (A n x (v n x)) =
      LinearWaveResidual.shear (a.radius n) (a.frequencyBase n) (a.axialBase n)
        (d.radialField n) (fun y => CurlClassBounds.complexify (v n y)) x) (j : Fin 2) :
    let z := coefficients a s d H T R mask v Ndot A j
    ∀ n x, x ∈ s.domain →
      (z.corrected s d ψ).harmonicResidual s d n x =
        (fun i => (z.constructedGood s d ψ n x i +
          LinearWaveBounds.excludedSlotError d ψ z.amplitude 0 n x i) *
          carrier (a.frequency n) (a.phase n) x) := by
  have hi := coefficients_inputBounds hbase hcov hR hm hv hN hNdot hA hb hlo hhi hK j
  have hs := coefficients_principal_zero a hcov hR hm hv hHf hTf hRf hmf hfreq hode haction j
  have hs' : ∀ n x, x ∈ s.domain →
      (coefficients a s d H T R mask v Ndot A j).principal s d n x =
        -(0 : ℕ → D → ComplexVector) n x := by simpa using hs
  have hg := hangle.exactConditions (fun n => (hG n).radius_ne) (fun n => (hG n).radial_radius) j
  have hres := (LinearWaveBounds.constructed_linear_wave_with_excluded
    hi hκ hψ hradius hN hb hlo hhi hK hs' hg).2
  dsimp only
  intro n x hx
  ext i
  have hv := congrFun (hres n x hx) i
  simpa only [Pi.add_apply, Pi.zero_apply, zero_mul, add_zero, coefficients,
    homogeneousCoefficients] using hv

/-! ## The same native pulse blocks in the exact covariance identity -/

section NativeBlocks

open PartitionedCovariance

noncomputable def nativeUnit {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : TorusInverse.Plane) : Space :=
  !₂[covered (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) Y,
    covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j 0) Y,
    covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j 1) Y]

noncomputable def nativeTangentBlock {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (a : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) :
    CorrectionState.HarmonicBlock TorusInverse.Plane :=
  coefficientBlock (fun _ => 1) (fun _ => P.phases j) (fun _ => P.modes j)
    (fun _ Y => CurlClassBounds.complexify
      ((outer * (Real.sqrt ε * a j * mask D U q x)) • nativeUnit P hdet j Y)) 0

theorem real_character_one (a t : ℝ) :
    ((a : ℂ) * HarmonicFields.character 1 t).re = a * Real.cos t := by
  simp [HarmonicFields.character, Complex.mul_re, Complex.exp_re]

theorem nativeTangentBlock_radial {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (a : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (n : ℕ) (Y : TorusInverse.Plane) (θ : ℝ) :
    (nativeTangentBlock P hdet outer ε a q x j).oscillation n (Y,θ) 0 =
      SignedCovariance.radialWith P hdet outer ε a q x j Y θ := by
  rw [nativeTangentBlock, coefficientBlock_velocity]
  change ((outer * (Real.sqrt ε * a j * mask D U q x) *
    covered (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) Y : ℝ) *
    HarmonicFields.character 1 (1 * P.phases j Y + (P.modes j : ℝ) * θ)).re = _
  rw [real_character_one]
  simp only [SignedCovariance.radialWith, wave, one_mul, add_comm]

theorem nativeTangentBlock_tangent {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (a : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) (n : ℕ) (Y : TorusInverse.Plane) (θ : ℝ) :
    (nativeTangentBlock P hdet outer ε a q x j).oscillation n (Y,θ) i.succ =
      SignedCovariance.tangentWith P hdet outer ε a q x j i Y θ := by
  rw [nativeTangentBlock, coefficientBlock_velocity]
  have hv : nativeUnit P hdet j Y i.succ =
      covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) Y := by fin_cases i <;> rfl
  simp only [ CurlClassBounds.complexify_apply, PiLp.smul_apply,
    hv]
  rw [real_character_one]
  simp only [SignedCovariance.tangentWith, wave, one_mul, add_comm, smul_eq_mul]

noncomputable def nativeAssembly {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) :
    TorusInverse.Plane → ℝ → Fin 3 → ℝ := fun Y θ i =>
  ∑ᶠ v : UnsignedLabel × Fin 2,
    (nativeTangentBlock (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2).oscillation 0 (Y,θ) i

theorem nativeAssembly_radial {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (Y : TorusInverse.Plane) (θ : ℝ)
      :
    nativeAssembly P hdet outer ε a q x Y θ 0 =
      SignedCovariance.assembledRadialWith P hdet outer ε a q x Y θ := by
  simp only [nativeAssembly, nativeTangentBlock_radial, SignedCovariance.assembledRadialWith]

theorem nativeAssembly_tangent {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (i : Fin 2) (Y : TorusInverse.Plane) (θ : ℝ) :
    nativeAssembly P hdet outer ε a q x Y θ i.succ =
      SignedCovariance.assembledTangentWith P hdet outer ε a q x i Y θ := by
  simp only [nativeAssembly, nativeTangentBlock_tangent, SignedCovariance.assembledTangentWith]

theorem nativeAssembly_requested_cross {D h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : SlotSystem D h vr vt) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (N : ℕ) (hN : 1 ≤ N) (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position)
    (T0 : Vec2) (p : SignedStressPrimitive.Patch)
    (c : CorrectionState.Context (PressureStream.Lift E)) (u : CorrectionState.State
      (PressureStream.Lift E))
    (n : ℕ) (z : ℝ × E)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (P U).matrix (chartTarget h q N T0 U)) (i : Fin 2) :
    let primary := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SmoothCovariance.amplitudes (P U).matrix (chartTarget h q N T0 U)) q x
    let signed := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SignedCovariance.increment (P U).matrix (chartTarget h q N T0 U)
        (SignedCovariance.chartStress h N (requestedStress p c u n z) U)) q x
    doubleAverage (fun Y θ => primary Y θ 0 * signed Y θ i.succ + signed Y θ 0 * primary Y θ
      i.succ) =
      requestedStress p c u n z i := by
  dsimp only
  simp_rw [nativeAssembly_radial, nativeAssembly_tangent]
  exact SignedCovariance.physical_signed_cross_covariance sys hdet N hN P hq hqN x T0
    (requestedStress p c u n z) hcone i

theorem nativeAssembly_signed_square {D h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : SlotSystem D h vr vt) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (N : ℕ) (hN : 1 ≤ N) (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (T R : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (hε : ∀ U, mask D (tailLabel N U) q x ≠ 0 → 0 ≤ ε U) (i : Fin 2) :
    let signed := nativeAssembly P hdet outer ε
      (fun U => SignedCovariance.increment (P U).matrix (T U) (R U)) q x
    doubleAverage (fun Y θ => signed Y θ 0 * signed Y θ i.succ) =
      ∑ᶠ U : UnsignedLabel, outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
        SignedCovariance.squareColumn (P U).matrix (T U) (R U) i := by
  dsimp only
  simp_rw [nativeAssembly_radial, nativeAssembly_tangent]
  exact SignedCovariance.assembled_signed_square sys hdet N hN P outer ε T R hq x hε i

end NativeBlocks

theorem signed_square_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    (h : CovarianceControl s H T) (B κ : ℝ)
    (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i)) (i : Fin 2) :
    MeanClass s (2 * B - 2 * κ)
      (fun n x => s.epsilon n * SignedCovariance.squareColumn (H n x) (T n x) (R n x) i) :=
  SignedCovariance.native_signed_square_class B κ i h.zeta_pos (fun n _ hx => h.cone n hx)
    (h.inverse_class h.target_jets) (h.inverse_class hR) h.inverse_control
    (fun j => PrimaryPulseBounds.polynomial_memClass s (h.matrix_jets i j))

/-! ## Canonical pulse binding for the matrix and the native blocks -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem phaseMatrix_eq_canonical_pair
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (n : ℕ) (x : D)
    (hp : (χ n x).1 ∈ U.carrier n)
    (hA : ∀ j, ContinuousOn (((F j).frame n).coefficient 1)
      (U.carrier n ×ˢ Icc 0 ((F j).L n)))
    (hk : ∀ j, ((F j).frame n).Kinematics (χ n x).1 (Icc 0 ((F j).L n)))
    {D₀ h : ℝ} {vr vt : TorusInverse.Plane} {sys : PartitionedCovariance.SlotSystem D₀ h vr vt}
    {label : PartitionedCovariance.UnsignedLabel} (P : PartitionedCovariance.PairData sys label)
    (hpulse : ∀ j, P.pulses j = PrimaryPulseBounds.canonicalPrimaryPulse ((F j).frame n)
      ((F j).lam n) ((F j).u n) ((F j).L_pos n) (U.carrier n) (hA j) (χ n x).1 hp (hk j))
    (hpref : ∀ j, pref j n = PartitionedCovariance.nativePrefactor vr vt sys.radius * P.ci j * (F
      j).L n) :
    phaseMatrix F pref χ n x = P.matrix := by
  have he := PrimaryPulseBounds.primaryCovariance_eq_canonicalPairMatrix pref
    (fun j => (F j).frame) (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L)
    n (U.carrier n) (χ n x).1 hp (fun j => (F j).L_pos n) hA hk vr vt sys.radius P.ci hpref
  have hps : P.pulses = fun j => PrimaryPulseBounds.canonicalPrimaryPulse ((F j).frame n)
      ((F j).lam n) ((F j).u n) ((F j).L_pos n) (U.carrier n) (hA j) (χ n x).1 hp (hk j) := funext
        hpulse
  simpa only [phaseMatrix, PrimaryPulseBounds.chartCovariance,
    PartitionedCovariance.PairData.matrix,
    hps] using he

theorem nativeUnit_eq_canonical_pulse
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {D₀ h : ℝ} {vr vt : TorusInverse.Plane} {sys : PartitionedCovariance.SlotSystem D₀ h vr vt}
    {label : PartitionedCovariance.UnsignedLabel} (P : PartitionedCovariance.PairData sys label)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2)
    (f : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (f.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : f.Kinematics p (Icc 0 L))
    (hpulse : P.pulses j = PrimaryPulseBounds.canonicalPrimaryPulse f lam u hL U hA p hp hk)
    (Y : TorusInverse.Plane) (i : Fin 3) :
    nativeUnit P hdet j Y i = PartitionedCovariance.covered (SlotColoring.nativeIndex h label.1)
      (PartitionedCovariance.nativePulse vr vt (PartitionedCovariance.slotCenter h
        (PartitionedCovariance.signedLabel label j)) hdet (P.ci j) sys.radius
        (fun z => PrimaryPulseBounds.localPrimaryProfile f lam u L sys.radius p z i)) Y := by
  have hr : (P.pulses j).radialProfile sys.radius =
      fun z => PrimaryPulseBounds.localPrimaryProfile f lam u L sys.radius p z 0 := by
    funext z
    rw [hpulse]
    exact PrimaryPulseBounds.canonicalPrimaryPulse_radialProfile f lam u sys.radius hL U hA p hp hk
      z
  have ht (i : Fin 2) : (P.pulses j).tangentProfile sys.radius i =
      fun z => PrimaryPulseBounds.localPrimaryProfile f lam u L sys.radius p z i.succ := by
    funext z
    rw [hpulse]
    exact PrimaryPulseBounds.canonicalPrimaryPulse_tangentProfile f lam u sys.radius hL U hA p hp
      hk z i
  fin_cases i
  · change PartitionedCovariance.covered _ (P.rawRadial hdet j) _ = _
    simp only [PartitionedCovariance.PairData.rawRadial, hr]
    rfl
  · change PartitionedCovariance.covered _ (P.rawTangent hdet j 0) _ = _
    simp only [PartitionedCovariance.PairData.rawTangent, ht]
    rfl
  · change PartitionedCovariance.covered _ (P.rawTangent hdet j 1) _ = _
    simp only [PartitionedCovariance.PairData.rawTangent, ht]
    rfl

theorem masked_signed_square_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    (h : CovarianceControl s H T) (B κ : ℝ)
    (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i))
    {mask : ℕ → D → ℝ} (hm : UnweightedClass s 0 mask) (i : Fin 2) :
    MeanClass s (2 * B - 2 * κ)
      (fun n x => mask n x ^ 2 * (s.epsilon n * SignedCovariance.squareColumn (H n x) (T n x) (R n
        x) i)) := by
  have hmm := LinearWaveBounds.unweighted_mul hm hm
  have hh := LinearWaveBounds.unweighted_smul hmm (signed_square_class h B κ hR i)
  simpa only [zero_add, smul_eq_mul, pow_two] using hh

/-! ## Exported blocks for the correction state -/

noncomputable def signedBlock (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (s : StripData (D × ℝ)) (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (H : ℕ → D × ℝ → Mat2) (T R : ℕ → D × ℝ → Vec2) (mask : ℕ → D × ℝ → ℝ)
    (v Ndot : ℕ → D × ℝ → Space) (A : ℕ → D × ℝ → Space →L[ℝ] Space)
    (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) (j : Fin 2) : CorrectionState.HarmonicBlock D :=
  blockOfCoefficients (exactCoefficients a s d H T R mask v Ndot A ψ j) kp

theorem signedBlock_bounds
    {s : StripData (D × ℝ)} {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {P₀ P : ℕ → D × ℝ → ℝ} {α₀ B κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a) (hκ : κ ≤ 1 / 2)
    {H : ℕ → D × ℝ → Mat2} {T R : ℕ → D × ℝ → Vec2} {mask ψ : ℕ → D × ℝ → ℝ}
    {v Ndot : ℕ → D × ℝ → Space} {A : ℕ → D × ℝ → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    {radius : D × ℝ → ℝ} (hradius : a.radius = fun _ => radius)
    (hψ : UnweightedClass s 0 ψ) (kp : ℕ → ℤ) (j : Fin 2) :
    (signedBlock a s d H T R mask v Ndot A ψ kp j).WaveBounds
      (sectionStrip s) (fun n x => P n (x,0)) (B - κ) ∧
    (signedBlock a s d H T R mask v Ndot A ψ kp j).PressureBounds
      (sectionStrip s) (fun n x => P n (x,0)) (B + 1 / 2 - κ) := by
  have hs := signed_bounds hbase hκ hcov hR hm hv hN hNdot hA hb hlo hhi hK hradius hψ j
  exact blockOfCoefficients_classes _ kp hs.1 hs.2.1

theorem signedBlock_band
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (s : StripData (D × ℝ)) (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (H : ℕ → D × ℝ → Mat2) (T R : ℕ → D × ℝ → Vec2) (mask : ℕ → D × ℝ → ℝ)
    (v Ndot : ℕ → D × ℝ → Space) (A : ℕ → D × ℝ → Space →L[ℝ] Space)
    (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) (j : Fin 2) :
    (signedBlock a s d H T R mask v Ndot A ψ kp j).BandLimited 1 :=
  coefficientBlock_band _ _ _ _ _

noncomputable def gaussianBlock (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ)
    (kp : ℕ → ℤ) : CorrectionState.HarmonicBlock D :=
  ErrorHarmonics.gaussianBlock d ψ a.amplitude 0 1 a.frequency (fun n x => a.phase n (x,0)) kp

/-- The error block is evaluated from the actual cutoff derivative and the
same uncut signed coefficient. It has the original carrier and its conjugate. -/
theorem gaussianBlock_represents
    {s : StripData (D × ℝ)} {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {H : ℕ → D × ℝ → Mat2} {T R : ℕ → D × ℝ → Vec2} {mask : ℕ → D × ℝ → ℝ}
    {v Ndot : ℕ → D × ℝ → Space} {A : ℕ → D × ℝ → Space →L[ℝ] Space}
    {ψ : ℕ → D × ℝ → ℝ} {m : ℕ → ℝ}
    (h : AngularInputs s d a H T R mask v Ndot A ψ m)
    (hθ : d.angular = (0,1)) (hψ : ∀ n, ContDiff ℝ ∞ (ψ n))
    (kp : ℕ → ℤ) (hkp : ∀ n, a.frequency n * m n = (kp n : ℝ)) (j : Fin 2) :
    let z := coefficients a s d H T R mask v Ndot A j
    (gaussianBlock z d ψ kp).oscillation = fun n x i =>
      (LinearWaveBounds.excludedSlotError d ψ z.amplitude 0 n x i *
        carrier (a.frequency n) (a.phase n) x).re := by
  have hψa : ErrorHarmonics.AngleIndependent ψ := by
    intro n x t
    apply CopyAngularInvariance.invariant_eq_zeroSlice
    have hc := h.cutoff n
    simp only [hθ] at hc
    exact hc
  have ha : ErrorHarmonics.AngleIndependent (coefficients a s d H T R mask v Ndot A j).amplitude :=
    by
    intro n x t
    apply CopyAngularInvariance.invariant_eq_zeroSlice
    simpa only [hθ] using h.amplitude j n
  have hs : ErrorHarmonics.AngleIndependent (0 : ℕ → D × ℝ → ComplexVector) := by
    intro n x t
    rfl
  have hp : ∀ n x t, a.frequency n * a.phase n (x,t) =
      a.frequency n * a.phase n (x,0) + (kp n : ℝ) * t := by
    intro n x t
    rw [CopyAngularInvariance.affinePhase_eq_zeroSlice (Φ := a.phase n) (m := m n)
      (by simpa only [hθ] using h.phase n) x t,
      mul_add, ← mul_assoc, hkp]
  have he := ErrorHarmonics.gaussianBlock_represents d 1 a.frequency
    (fun n x => a.phase n (x,0)) a.phase kp hψ hψa ha hs hp
  dsimp only
  funext n x i
  have hi := congrFun (congrFun (congrFun he n) x) i
  simpa only [gaussianBlock, ErrorHarmonics.gaussianField, vectorMode, mode,
    Int.cast_one, mul_one, coefficients, homogeneousCoefficients] using hi

/-! The realization hypothesis below concerns only the already constructed
unit pulse and chart. It never identifies or bounds a signed output. The
canonical unit pulse and its matrix are identified by the two preceding
canonical-pulse theorems. -/

theorem signed_tangent_native_realization
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    (a : LinearWaveBounds.WaveCoefficients D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask ψ : ℕ → D → ℝ)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    {D₀ h : ℝ} {vr vt : TorusInverse.Plane} {sys : PartitionedCovariance.SlotSystem D₀ h vr vt}
    {label : PartitionedCovariance.UnsignedLabel} (P : PartitionedCovariance.PairData sys label)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer q : ℝ) (position : SlotColoring.Position) (T₀ R₀ : Vec2)
    (j : Fin 2) (n : ℕ) (x : D) (Y : TorusInverse.Plane) (θ : ℝ)
    (hH : H n x = P.matrix) (hT : T n x = T₀) (hR : R n x = R₀)
    (hm : mask n x = PartitionedCovariance.mask D₀ label q position)
    (hpulse : ψ n x • v n x = nativeUnit P hdet j Y)
    (hphase : a.frequency n * a.phase n x = P.phases j Y + (P.modes j : ℝ) * θ)
    (i : Fin 3) :
    outer * (vectorMode (a.frequency n) (a.phase n)
      (((coefficients a s d H T R mask v Ndot A j).withCutoff ψ).amplitude n) x i).re =
      (nativeTangentBlock P hdet outer (s.epsilon n)
        (SignedCovariance.increment P.matrix T₀ R₀) q position j).oscillation 0 (Y,θ) i := by
  have hi := congrArg (fun z : Space => z i) hpulse
  change ψ n x * v n x i = nativeUnit P hdet j Y i at hi
  have hc : carrier (a.frequency n) (a.phase n) x =
      HarmonicFields.character 1 (P.phases j Y + (P.modes j : ℝ) * θ) := by
    rw [← hphase]
    simpa only [Int.cast_one, mul_one] using
      (HarmonicFields.character_eq_carrier 1 (a.frequency n) (a.phase n) x).symm
  rw [nativeTangentBlock, coefficientBlock_velocity]
  simp only [vectorMode, mode, coefficients, homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, signedVector, signedScalar,
    Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, CurlClassBounds.complexify_apply,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero, hH, hT, hR, hm, hc, one_mul]
  rw [show ψ n x * (Real.sqrt (s.epsilon n) * SignedCovariance.increment P.matrix T₀ R₀ j *
      PartitionedCovariance.mask D₀ label q position * v n x i) =
        (Real.sqrt (s.epsilon n) * SignedCovariance.increment P.matrix T₀ R₀ j *
          PartitionedCovariance.mask D₀ label q position) * nativeUnit P hdet j Y i by
    rw [← hi]
    ring]
  ring

end NavierStokes.SignedWaveUpdate
