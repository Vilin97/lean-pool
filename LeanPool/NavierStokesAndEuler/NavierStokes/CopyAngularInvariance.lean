/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve
import LeanPool.NavierStokesAndEuler.NavierStokes.CopySolveCompatibility

/-!
# Angular invariance of constructed stripped copy and curl coefficients

Only primitive translation identities are assumed. The actual copy solve,
its pressure, and the stripped cylindrical curl inherit those identities.
The oscillatory carrier retains its separate angular character.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CopyAngularInvariance

open Set Function Filter
open scoped ContDiff Topology BigOperators InnerProductSpace
open CommonCoverSolve TorusInverse

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Invariant, given by `∀ (x : D) (t : ℝ), f (x + t • θ) = f x`. -/
noncomputable def Invariant (θ : D) {E : Type} (f : D → E) : Prop :=
  ∀ (x : D) (t : ℝ), f (x + t • θ) = f x

/-- Affine phase, given by `∀ (x : D) (t : ℝ), Φ (x + t • θ) = Φ x + m * t`. -/
noncomputable def AffinePhase (θ : D) (m : ℝ) (Φ : D → ℝ) : Prop :=
  ∀ (x : D) (t : ℝ), Φ (x + t • θ) = Φ x + m * t

namespace Invariant

variable {θ : D} {E F G : Type} {f : D → E} {g : D → F}

theorem const (e : E) : Invariant θ (fun _ : D => e) := fun _ _ => rfl

theorem map (hf : Invariant θ f) (T : E → F) : Invariant θ (fun x => T (f x)) := by
  intro x t
  exact congrArg T (hf x t)

theorem map₂ (hf : Invariant θ f) (hg : Invariant θ g) (T : E → F → G) :
    Invariant θ (fun x => T (f x) (g x)) := by
  intro x t
  exact congrArg₂ T (hf x t) (hg x t)

theorem component {ι : Type} {F : ι → Type} {f : D → ∀ i, F i}
    (hf : Invariant θ f) (i : ι) : Invariant θ (fun x => f x i) := hf.map (fun v => v i)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem tsum_invariant {ι : Type} {f : ι → D → E} (hf : ∀ i, Invariant θ (f i)) :
    Invariant θ (fun x => ∑' i, f i x) := by
  intro x t
  apply tsum_congr
  intro i
  exact hf i x t

/-- Translation covariance of the actual Fréchet derivative, including its
canonical zero value when the original function is not differentiable. -/
theorem fderiv_invariant (hf : Invariant θ f) : Invariant θ (fderiv ℝ f) := by
  intro x t
  have he : (fun y => f (y + t • θ)) = f := funext (fun y => hf y t)
  rw [← fderiv_comp_add_right (t • θ), he]

theorem iteratedFDeriv_invariant (hf : Invariant θ f) (j : ℕ) :
    Invariant θ (iteratedFDeriv ℝ j f) := by
  intro x t
  have he : (fun y => f (y + t • θ)) = f := funext (fun y => hf y t)
  rw [← iteratedFDeriv_comp_add_right j (t • θ) x, he]

theorem along {V : D → D} (hf : Invariant θ f) (hV : Invariant θ V) :
    Invariant θ (HarmonicCalculus.along V f) := by
  intro x t
  simp only [HarmonicCalculus.along, hf.fderiv_invariant x t, hV x t]

theorem directional_zero (hf : Invariant θ f) (x : D) : fderiv ℝ f x θ = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hline : HasDerivAt (fun t : ℝ => f (x + t • θ)) (fderiv ℝ f x θ) 0 := by
      apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      · simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const θ).const_add x)
      · simp
    have he : (fun t : ℝ => f (x + t • θ)) = fun _ => f x := funext (hf x)
    rw [he] at hline
    exact hline.unique (hasDerivAt_const 0 (f x))
  · rw [fderiv_zero_of_not_differentiableAt hd, _root_.zero_apply]

theorem along_zero (hf : Invariant θ f) (x : D) :
    HarmonicCalculus.along (fun _ => θ) f x = 0 := hf.directional_zero x

end Invariant

namespace AffinePhase

variable {θ : D} {m : ℝ} {Φ : D → ℝ}

theorem fderiv_invariant (hΦ : AffinePhase θ m Φ) : Invariant θ (fderiv ℝ Φ) := by
  intro x t
  have he : (fun y => Φ (y + t • θ)) = fun y => Φ y + m * t := funext (fun y => hΦ y t)
  rw [← fderiv_comp_add_right (t • θ), he, fderiv_add_const]

theorem along_invariant (hΦ : AffinePhase θ m Φ) {V : D → D} (hV : Invariant θ V) :
    Invariant θ (HarmonicCalculus.along V Φ) := by
  intro x t
  simp only [HarmonicCalculus.along, hΦ.fderiv_invariant x t, hV x t]

theorem directional_eq (hΦ : AffinePhase θ m Φ) {x : D} (hd : DifferentiableAt ℝ Φ x) :
    fderiv ℝ Φ x θ = m := by
  have hline : HasDerivAt (fun t : ℝ => Φ (x + t • θ)) (fderiv ℝ Φ x θ) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    · simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const θ).const_add x)
    · simp
  have he : (fun t : ℝ => Φ (x + t • θ)) = fun t => Φ x + m * t := funext (hΦ x)
  rw [he] at hline
  have href : HasDerivAt (fun t : ℝ => Φ x + m * t) m 0 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul m).const_add (Φ x)
  exact hline.unique href

end AffinePhase

/-! ## Actual copy solves under angular translation of the slow parameter -/

section CopySolve

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

theorem slow_shift_apply {F : Type} {f : P × Plane → F} {θ : P}
    (hf : Invariant (θ, (0 : Plane)) f) (p : P) (Y : Plane) (t : ℝ) :
    f (p + t • θ, Y) = f (p, Y) := by
  simpa using hf (p, Y) t

theorem anchoredSolve_invariant (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (θ : P) (hA : Invariant (θ, (0 : Plane)) d.coefficient)
    (hB : Invariant (θ, (0 : Plane)) d.forcingMap)
    (hf : Invariant (θ, (0 : Plane)) d.source) (j : Frequency) (s : ℝ) :
    Invariant (θ, (0 : Plane)) (fun x => d.anchoredSolve g hab j x s) := by
  rintro ⟨p, Y⟩ t
  change d.anchoredSolve g hab j (p + t • θ, Y + t • (0 : Plane)) s = _
  rw [smul_zero, add_zero]
  have hAp : d.coefficientPath (a := a) (b := b) g j (p + t • θ, Y) =
      d.coefficientPath g j (p, Y) := by
    apply CopySolveCompatibility.pathFamily_congr
    intro u
    exact slow_shift_apply hA p _ t
  have hfp : d.forcingPath (a := a) (b := b) g j (p + t • θ, Y) =
      d.forcingPath g j (p, Y) := by
    apply CopySolveCompatibility.pathFamily_congr
    intro u
    simp only [LinearData.forcingAlong, slow_shift_apply hB, slow_shift_apply hf]
  simp only [LinearData.anchoredSolve, hAp, hfp]

theorem copySolve_invariant (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (θ : P) (hA : Invariant (θ, (0 : Plane)) d.coefficient)
    (hB : Invariant (θ, (0 : Plane)) d.forcingMap)
    (hf : Invariant (θ, (0 : Plane)) d.source) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (d.copySolve g hab j) := by
  rintro ⟨p, Y⟩ t
  change d.copySolve g hab j (p + t • θ, Y + t • (0 : Plane)) = _
  rw [smul_zero, add_zero]
  unfold LinearData.copySolve
  exact slow_shift_apply (anchoredSolve_invariant d g hab θ hA hB hf j _) p Y t

theorem localizedCopy_invariant (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (θ : P) (hA : Invariant (θ, (0 : Plane)) d.coefficient)
    (hB : Invariant (θ, (0 : Plane)) d.forcingMap)
    (hf : Invariant (θ, (0 : Plane)) d.source) (κ : Plane → ℝ) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (d.localizedCopy g hab κ j) := by
  rintro ⟨p, Y⟩ t
  change d.localizedCopy g hab κ j (p + t • θ, Y + t • (0 : Plane)) = _
  rw [smul_zero, add_zero]
  simp only [LinearData.localizedCopy, slow_shift_apply (copySolve_invariant d g hab θ hA hB hf j)]

theorem commonSolve_invariant (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (θ : P) (hA : Invariant (θ, (0 : Plane)) d.coefficient)
    (hB : Invariant (θ, (0 : Plane)) d.forcingMap)
    (hf : Invariant (θ, (0 : Plane)) d.source) (κ : Plane → ℝ) :
    Invariant (θ, (0 : Plane)) (d.commonSolve g hab κ) := by
  intro x t
  apply tsum_congr
  intro j
  exact localizedCopy_invariant d g hab θ hA hB hf κ j x t

theorem copySolve_angular_zero (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (θ : P) (hA : Invariant (θ, (0 : Plane)) d.coefficient)
    (hB : Invariant (θ, (0 : Plane)) d.forcingMap)
    (hf : Invariant (θ, (0 : Plane)) d.source) (j : Frequency) (x : P × Plane) :
    HarmonicCalculus.along (fun _ => (θ, (0 : Plane))) (d.copySolve g hab j) x = 0 :=
  (copySolve_invariant d g hab θ hA hB hf j).along_zero x

end CopySolve

/-! ## Tangent data and the actual pressure formula -/

section Tangent

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

/-- Tangent invariant data, collecting `normal`, `normalDot`, `action`, `damping`, `source`. -/
structure TangentInvariant (θ : P) (d : TangentData P H) : Prop where
  normal : Invariant (θ, (0 : Plane)) d.normal
  normalDot : Invariant (θ, (0 : Plane)) d.normalDot
  action : Invariant (θ, (0 : Plane)) d.action
  damping : Invariant (θ, (0 : Plane)) d.damping
  source : Invariant (θ, (0 : Plane)) d.source

omit [CompleteSpace H] in
theorem TangentInvariant.coefficient {θ : P} {d : TangentData P H} (h : TangentInvariant θ d) :
    Invariant (θ, (0 : Plane)) d.linearData.coefficient := by
  intro x t
  simp only [TangentData.linearData, h.normal x t, h.normalDot x t, h.action x t, h.damping x t]

omit [CompleteSpace H] in
theorem TangentInvariant.forcingMap {θ : P} {d : TangentData P H} (h : TangentInvariant θ d) :
    Invariant (θ, (0 : Plane)) d.linearData.forcingMap := by
  intro x t
  simp only [TangentData.linearData, h.normal x t]

theorem TangentInvariant.copySolve_invariant {θ : P} {d : TangentData P H} (h : TangentInvariant θ
    d)
    (g : Geometry) (hab : a ≤ b) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (d.linearData.copySolve g hab j) :=
  NavierStokes.CopyAngularInvariance.copySolve_invariant d.linearData g hab θ
    h.coefficient h.forcingMap h.source j

/-- Copy native point, given by `(x.1, g.coordinates j x.2)`. -/
noncomputable def copyNativePoint (g : Geometry) (j : Frequency) (x : P × Plane) : P × Plane :=
  (x.1, g.coordinates j x.2)

theorem native_invariant {F : Type} {θ : P} {f : P × Plane → F}
    (hf : Invariant (θ, (0 : Plane)) f) (g : Geometry) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (fun x => f (copyNativePoint g j x)) := by
  rintro ⟨p, Y⟩ t
  change f (copyNativePoint g j (p + t • θ, Y + t • (0 : Plane))) = _
  rw [smul_zero, add_zero]
  unfold copyNativePoint
  exact slow_shift_apply hf p _ t

/-- Same scalar formula as the particular-wave pressure, evaluated on the
constructed copy solve and the actual source at the current common point. -/
noncomputable def copyPressureReal (d : TangentData P H) (g : Geometry) (hab : a ≤ b)
    (j : Frequency) (x : P × Plane) : ℝ :=
  TangentProjection.pressureCoefficient (d.normal (copyNativePoint g j x))
    (d.normalDot (copyNativePoint g j x)) (d.linearData.copySolve g hab j x)
    (d.action (copyNativePoint g j x) (d.linearData.copySolve g hab j x)) (d.source x)

/-- Copy pressure, given by `Complex.I * (copyPressureReal d g hab j x : ℂ) / (K : ℂ)`. -/
noncomputable def copyPressure (d : TangentData P H) (g : Geometry) (hab : a ≤ b)
    (j : Frequency) (K : ℝ) (x : P × Plane) : ℂ :=
  Complex.I * (copyPressureReal d g hab j x : ℂ) / (K : ℂ)

theorem TangentInvariant.copyPressureReal_invariant {θ : P} {d : TangentData P H}
    (h : TangentInvariant θ d) (g : Geometry) (hab : a ≤ b) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (copyPressureReal d g hab j) := by
  intro x t
  simp only [copyPressureReal, native_invariant h.normal g j x t,
    native_invariant h.normalDot g j x t, native_invariant h.action g j x t,
    h.copySolve_invariant g hab j x t, h.source x t]

theorem TangentInvariant.copyPressure_invariant {θ : P} {d : TangentData P H}
    (h : TangentInvariant θ d) (g : Geometry) (hab : a ≤ b) (j : Frequency) (K : ℝ) :
    Invariant (θ, (0 : Plane)) (copyPressure d g hab j K) :=
  (h.copyPressureReal_invariant g hab j).map (fun r : ℝ => Complex.I * (r : ℂ) / (K : ℂ))

theorem TangentInvariant.copyPressure_angular_zero {θ : P} {d : TangentData P H}
    (h : TangentInvariant θ d) (g : Geometry) (hab : a ≤ b) (j : Frequency) (K : ℝ)
    (x : P × Plane) :
    HarmonicCalculus.along (fun _ => (θ, (0 : Plane))) (copyPressure d g hab j K) x = 0 :=
  (h.copyPressure_invariant g hab j K).along_zero x

theorem nativeCutoff_invariant (θ : P) (g : Geometry) (κ : Plane → ℝ) (j : Frequency) :
    Invariant (θ, (0 : Plane)) (fun x : P × Plane => κ (g.coordinates j x.2)) := by
  have hY : Invariant (θ, (0 : Plane)) (fun x : P × Plane => x.2) := by
    intro x t
    change x.2 + t • (0 : Plane) = x.2
    simp
  exact hY.map (fun Y => κ (g.coordinates j Y))

/-- Common pressure, given by `∑' j : Frequency, (κ (g.coordinates j x.2) : ℂ) * copyPressure d
g hab j K x`. -/
noncomputable def commonPressure (d : TangentData P H) (g : Geometry) (hab : a ≤ b)
    (κ : Plane → ℝ) (K : ℝ) (x : P × Plane) : ℂ :=
  ∑' j : Frequency, (κ (g.coordinates j x.2) : ℂ) * copyPressure d g hab j K x

theorem TangentInvariant.commonPressure_invariant {θ : P} {d : TangentData P H}
    (h : TangentInvariant θ d) (g : Geometry) (hab : a ≤ b) (κ : Plane → ℝ) (K : ℝ) :
    Invariant (θ, (0 : Plane)) (commonPressure d g hab κ K) := by
  apply Invariant.tsum_invariant
  intro j
  exact (nativeCutoff_invariant θ g κ j).map₂ (h.copyPressure_invariant g hab j K)
    (fun r p => (r : ℂ) * p)

theorem TangentInvariant.commonPressure_angular_zero {θ : P} {d : TangentData P H}
    (h : TangentInvariant θ d) (g : Geometry) (hab : a ≤ b) (κ : Plane → ℝ) (K : ℝ)
    (x : P × Plane) :
    HarmonicCalculus.along (fun _ => (θ, (0 : Plane))) (commonPressure d g hab κ K) x = 0 :=
  (h.commonPressure_invariant g hab κ K).along_zero x

end Tangent

/-! ## Invariance of the actual stripped cylindrical curl -/

section Curl

variable {θ : D} {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {m : ℝ}
  {a : D → CurlClassBounds.ComplexVector}

theorem phaseNormal_invariant (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hΦ : AffinePhase θ m Φ) :
    Invariant θ (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ) := by
  intro x t
  simp only [HarmonicCalculus.phaseNormal, hΦ.along_invariant hr x t,
    hΦ.along_invariant hθ x t, hΦ.along_invariant hz x t, hR x t]

theorem coefficient_invariant (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a) :
    Invariant θ (CurlClassBounds.coefficient R Vr Vθ Vz Φ a) :=
  (phaseNormal_invariant hR hr hθ hz hΦ).map₂ ha CurlClassBounds.normalCoefficient

theorem cylindricalCurl_invariant (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (ha : Invariant θ a) : Invariant θ (CurlClassBounds.cylindricalCurl R Vr Vθ Vz a) := by
  intro x t
  simp only [CurlClassBounds.cylindricalCurl, hR x t,
    (ha.component 2).along hθ x t, (ha.component 1).along hz x t,
    (ha.component 0).along hz x t, (ha.component 2).along hr x t,
    (ha.component 1).along hr x t, (ha.component 0).along hθ x t, ha x t]

theorem curlRemainder_invariant (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (ha : Invariant θ a) (K : ℝ) :
    Invariant θ (CurlClassBounds.curlRemainder K R Vr Vθ Vz a) :=
  (cylindricalCurl_invariant hR hr hθ hz ha).map
    (fun v => (1 / K) • (Complex.I • v))

theorem realizedCoefficient_invariant (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a) (K : ℝ) :
    Invariant θ (CurlClassBounds.realizedCoefficient K R Vr Vθ Vz Φ a) :=
  ha.map₂ (curlRemainder_invariant hR hr hθ hz (coefficient_invariant hR hr hθ hz hΦ ha) K)
    (fun u v => u + v)

theorem realizedCoefficient_angular_zero (hR : Invariant θ R)
    (hr : Invariant θ Vr) (hθ : Invariant θ Vθ) (hz : Invariant θ Vz)
    (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a) (K : ℝ) (i : Fin 3) (x : D) :
    HarmonicCalculus.along (fun _ => θ)
      (fun y => CurlClassBounds.realizedCoefficient K R Vr Vθ Vz Φ a y i) x = 0 :=
  ((realizedCoefficient_invariant hR hr hθ hz hΦ ha K).component i).along_zero x

end Curl

section ActualCopyCurl

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {θ : P} {d : TangentData P CurlClassBounds.RealVector} {a b : ℝ}

/-- The amplitude premise of the curl invariance theorem is discharged by
the actual tangent copy solve and invariant scalar mask. -/
theorem actualCopy_realizedCoefficient_invariant (hd : TangentInvariant θ d)
    (g : Geometry) (hab : a ≤ b) (j : Frequency)
    {R ψ : P × Plane → ℝ} {Vr Vz : P × Plane → P × Plane}
    {Φ : P × Plane → ℝ} {m : ℝ}
    (hR : Invariant (θ, (0 : Plane)) R) (hψ : Invariant (θ, (0 : Plane)) ψ)
    (hr : Invariant (θ, (0 : Plane)) Vr) (hz : Invariant (θ, (0 : Plane)) Vz)
    (hΦ : AffinePhase (θ, (0 : Plane)) m Φ) (K : ℝ) :
    Invariant (θ, (0 : Plane))
      (CurlClassBounds.realizedCoefficient K R Vr (fun _ => (θ, (0 : Plane))) Vz Φ
        (fun x => ψ x • CurlClassBounds.complexify (d.linearData.copySolve g hab j x))) := by
  apply realizedCoefficient_invariant hR hr (Invariant.const _) hz hΦ
  exact hψ.map₂ ((hd.copySolve_invariant g hab j).map CurlClassBounds.complexify) (fun r v => r • v)

end ActualCopyCurl

/-! ## The carrier has its angular character; only the coefficient is invariant -/

section HarmonicPhase

variable {θ : D} {Φ : D → ℝ} {m : ℝ}

theorem carrier_translate (hΦ : AffinePhase θ m Φ) (K : ℝ) (x : D) (t : ℝ) :
    HarmonicCalculus.carrier K Φ (x + t • θ) =
      Complex.exp (HarmonicCalculus.phaseFactor K * ((m * t : ℝ) : ℂ)) *
        HarmonicCalculus.carrier K Φ x := by
  simp only [HarmonicCalculus.carrier, hΦ x t, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem mode_translate {a : D → ℂ} (ha : Invariant θ a) (hΦ : AffinePhase θ m Φ)
    (K : ℝ) (x : D) (t : ℝ) :
    HarmonicCalculus.mode K Φ a (x + t • θ) =
      Complex.exp (HarmonicCalculus.phaseFactor K * ((m * t : ℝ) : ℂ)) *
        HarmonicCalculus.mode K Φ a x := by
  simp only [HarmonicCalculus.mode, ha x t, carrier_translate hΦ]
  ring

theorem vectorMode_translate {a : D → HarmonicCalculus.ComplexVector}
    (ha : Invariant θ a) (hΦ : AffinePhase θ m Φ) (K : ℝ) (x : D) (t : ℝ) :
    HarmonicCalculus.vectorMode K Φ a (x + t • θ) =
      Complex.exp (HarmonicCalculus.phaseFactor K * ((m * t : ℝ) : ℂ)) •
        HarmonicCalculus.vectorMode K Φ a x := by
  ext i
  exact mode_translate (ha.component i) hΦ K x t

/-- This version works with any chosen angular section, independently of
where the angular coordinate is stored in a product type. -/
theorem mode_eq_field_along {P : Type} {f : D → ℂ}
    (hf : Invariant θ f) (hΦ : AffinePhase θ m Φ) (σ : P → D)
    (k : ℝ) (j kp : ℤ) (hkp : (kp : ℝ) = k * m) (p : P) (t : ℝ) :
    HarmonicCalculus.mode ((j : ℝ) * k) Φ f (σ p + t • θ) =
      HarmonicFields.field (AddMonoidAlgebra.single j (fun p => f (σ p))) k (fun p => Φ (σ p)) kp
          (p, t) := by
  simp only [HarmonicCalculus.mode, HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor,
    HarmonicFields.field, HarmonicFields.evaluate_single, HarmonicFields.character]
  rw [hf (σ p) t, hΦ (σ p) t]
  simp only [hkp, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 2
  ring

theorem vectorMode_eq_field_along_component {P : Type} {a : D → HarmonicCalculus.ComplexVector}
    (ha : Invariant θ a) (hΦ : AffinePhase θ m Φ) (σ : P → D)
    (k : ℝ) (j kp : ℤ) (hkp : (kp : ℝ) = k * m) (p : P) (t : ℝ) (i : Fin 3) :
    HarmonicCalculus.vectorMode ((j : ℝ) * k) Φ a (σ p + t • θ) i =
      HarmonicFields.field (AddMonoidAlgebra.single j (fun p => a (σ p) i)) k (fun p => Φ (σ p)) kp
          (p, t) :=
  mode_eq_field_along (ha.component i) hΦ σ k j kp hkp p t

end HarmonicPhase

section Slice

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem invariant_eq_zeroSlice {f : P × ℝ → E} (hf : Invariant ((0 : P), (1 : ℝ)) f)
    (p : P) (t : ℝ) : f (p, t) = f (p, 0) := by
  simpa using hf (p, 0) t

theorem affinePhase_eq_zeroSlice {Φ : P × ℝ → ℝ} {m : ℝ}
    (hΦ : AffinePhase ((0 : P), (1 : ℝ)) m Φ) (p : P) (t : ℝ) :
    Φ (p, t) = Φ (p, 0) + m * t := by
  simpa using hΦ (p, 0) t

/-- The true full coefficient is equal to its zero-angle slice. The carrier
then agrees exactly with the existing finite-harmonic field constructor. -/
theorem mode_eq_field_single {f : P × ℝ → ℂ} {Φ : P × ℝ → ℝ} {m : ℝ}
    (hf : Invariant ((0 : P), (1 : ℝ)) f) (hΦ : AffinePhase ((0 : P), (1 : ℝ)) m Φ)
    (k : ℝ) (j kp : ℤ) (hkp : (kp : ℝ) = k * m) (p : P) (t : ℝ) :
    HarmonicCalculus.mode ((j : ℝ) * k) Φ f (p, t) =
      HarmonicFields.field (AddMonoidAlgebra.single j (fun p => f (p, 0))) k (fun p => Φ (p, 0)) kp
          (p, t) := by
  simp only [HarmonicCalculus.mode, HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor,
    HarmonicFields.field, HarmonicFields.evaluate_single, HarmonicFields.character]
  rw [invariant_eq_zeroSlice hf p t, affinePhase_eq_zeroSlice hΦ p t]
  simp only [hkp, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 2
  ring

end Slice

/-! ## ExactConditions for the actual corrected coefficient -/

section ExactConditions

open LinearWaveBounds WeightedClasses

variable {s : StripData D} {d : GraphDirections D} {a : WaveCoefficients D}

theorem base_invariant {θ : D} {R b F G : D → ℝ}
    (hR : Invariant θ R) (hb : Invariant θ b) (hF : Invariant θ F) (hG : Invariant θ G) :
    Invariant θ (LinearWaveResidual.base R b F G) := by
  intro x t
  simp only [LinearWaveResidual.base, hR x t, hb x t, hF x t, hG x t]

theorem exactConditions_of_invariants
    (hΦs : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hRne : ∀ n x, x ∈ s.domain → a.radius n x ≠ 0)
    (hDrR : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (d.radialField n) (a.radius n) x = 1)
    (hR : ∀ n, Invariant d.angular (a.radius n))
    (hb : ∀ n, Invariant d.angular (a.radialBase n))
    (hF : ∀ n, Invariant d.angular (a.frequencyBase n))
    (hG : ∀ n, Invariant d.angular (a.axialBase n))
    (hΦ : ∀ n, ∃ m, AffinePhase d.angular m (a.phase n))
    (ha : ∀ n, Invariant d.angular (a.amplitude n))
    (hp : ∀ n, Invariant d.angular (a.pressure n)) : ExactConditions s d a := by
  refine ⟨hΦs, hRne, hDrR, ?_, ?_, ?_, ?_⟩
  · intro n x _ i
    exact ((base_invariant (hR n) (hb n) (hF n) (hG n)).component i).along_zero x
  · intro n i x _
    exact ((ha n).component i).along_zero x
  · intro n
    obtain ⟨m, hm⟩ := hΦ n
    refine ⟨m, ?_⟩
    intro x hx
    exact hm.directional_eq (((hΦs n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
        simp))
  · intro n x _
    exact (hp n).along_zero x

theorem corrected_amplitude_invariant (ψ : ℕ → D → ℝ)
    (hR : ∀ n, Invariant d.angular (a.radius n))
    (hr : ∀ n, Invariant d.angular (d.radialField n))
    (hz : ∀ n, Invariant d.angular (d.axialField s n))
    (hΦ : ∀ n, ∃ m, AffinePhase d.angular m (a.phase n))
    (ha : ∀ n, Invariant d.angular (a.amplitude n))
    (hψ : ∀ n, Invariant d.angular (ψ n)) (n : ℕ) :
    Invariant d.angular ((a.corrected s d ψ).amplitude n) := by
  obtain ⟨m, hm⟩ := hΦ n
  exact realizedCoefficient_invariant (hR n) (hr n) (Invariant.const _) (hz n) hm
    ((hψ n).map₂ (ha n) (fun r v => r • v)) (a.frequency n)

theorem corrected_pressure_invariant (ψ : ℕ → D → ℝ)
    (hp : ∀ n, Invariant d.angular (a.pressure n))
    (hψ : ∀ n, Invariant d.angular (ψ n)) (n : ℕ) :
    Invariant d.angular ((a.corrected s d ψ).pressure n) :=
  (hψ n).map₂ (hp n) (fun r p => (r : ℂ) * p)

theorem exactConditions_corrected_of_invariants (ψ : ℕ → D → ℝ)
    (hΦs : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hRne : ∀ n x, x ∈ s.domain → a.radius n x ≠ 0)
    (hDrR : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (d.radialField n) (a.radius n) x = 1)
    (hR : ∀ n, Invariant d.angular (a.radius n))
    (hb : ∀ n, Invariant d.angular (a.radialBase n))
    (hF : ∀ n, Invariant d.angular (a.frequencyBase n))
    (hG : ∀ n, Invariant d.angular (a.axialBase n))
    (hr : ∀ n, Invariant d.angular (d.radialField n))
    (hz : ∀ n, Invariant d.angular (d.axialField s n))
    (hΦ : ∀ n, ∃ m, AffinePhase d.angular m (a.phase n))
    (ha : ∀ n, Invariant d.angular (a.amplitude n))
    (hp : ∀ n, Invariant d.angular (a.pressure n))
    (hψ : ∀ n, Invariant d.angular (ψ n)) : ExactConditions s d (a.corrected s d ψ) :=
  exactConditions_of_invariants hΦs hRne hDrR hR hb hF hG hΦ
    (corrected_amplitude_invariant ψ hR hr hz hΦ ha hψ)
    (corrected_pressure_invariant ψ hp hψ)

end ExactConditions

end NavierStokes.CopyAngularInvariance
