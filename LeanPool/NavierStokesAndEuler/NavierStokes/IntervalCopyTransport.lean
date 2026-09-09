/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledTangentTransport
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling

/-!
# Copy transport from continuity on the anchored interval

The actual Volterra constructor depends only on the coefficient and converted
forcing paths on its finite interval. These lemmas require continuity of
exactly those paths, including their endpoints. No continuation of the raw
tangent data or source outside the interval is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.IntervalCopyTransport

open Set Function Filter CommonCoverSolve TorusInverse ParticularWaveBounds
open CopySolveCompatibility ScaledTangentTransport
open scoped Topology ContDiff


section LinearPaths

variable {P Q V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- The derivative of the existing constructor needs only its two continuous
input paths on the actual integration interval. -/
theorem anchoredSolve_hasDerivAt (d : LinearData P V E) (g : Geometry)
    (hab : a ≤ b) (copy : Frequency) (p : P) (Y : Plane)
    (hA : Continuous (fun s : Icc a b => d.coefficientAlong g copy ((p, Y), s)))
    (hf : Continuous (fun s : Icc a b => d.forcingAlong g copy ((p, Y), s)))
    (s : Icc a b) :
    HasDerivAt (d.anchoredSolve g hab copy (p, Y))
      (d.coefficientAlong g copy ((p, Y), s) (d.anchoredSolve g hab copy (p, Y) s) +
        d.forcingAlong g copy ((p, Y), s)) s := by
  have hd := ParametricODE.solutionExtension_hasDerivAt hab
    (d.coefficientPath g copy (p, Y)) 0 (d.forcingPath g copy (p, Y)) s
  simp only [LinearData.coefficientPath, LinearData.forcingPath,
    SmoothPathFamily.pathFamily_apply _ _ hA, SmoothPathFamily.pathFamily_apply _ _ hf] at hd
  exact hd

/-- Uniqueness compares actual solutions on the finite interval. -/
theorem anchoredSolve_unique (d : LinearData P V E) (g : Geometry)
    (hab : a ≤ b) (copy : Frequency) (p : P) (Y : Plane)
    (hA : Continuous (fun s : Icc a b => d.coefficientAlong g copy ((p, Y), s)))
    (hf : Continuous (fun s : Icc a b => d.forcingAlong g copy ((p, Y), s)))
    {u : ℝ → E} (hu0 : u a = 0)
    (hu : ∀ s ∈ Icc a b, HasDerivAt u
      (d.coefficientAlong g copy ((p, Y), s) (u s) + d.forcingAlong g copy ((p, Y), s)) s) :
    EqOn u (d.anchoredSolve g hab copy (p, Y)) (Icc a b) := by
  apply TangentODE.linear_solution_unique hab
    (fun s => d.coefficientAlong g copy ((p, Y), s))
    (fun s => d.forcingAlong g copy ((p, Y), s))
    (continuousOn_iff_continuous_domRestrict.mpr hA) hu
    (fun s hs => anchoredSolve_hasDerivAt d g hab copy p Y hA hf ⟨s, hs⟩)
  rw [d.anchoredSolve_initial]
  exact hu0

/-- Affine clock transport of the anchored solve, with finite-path hypotheses
on the reference interval alone. -/
theorem anchoredSolve_timeData (d : LinearData P V E) (g : Geometry)
    (shift rate : ℝ) (hrate : 0 < rate) (hab : a ≤ b)
    (copy : Frequency) (p : P) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.coefficientAlong g copy ((p, Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.forcingAlong g copy ((p, Y), s)))
    {s : ℝ} (hs : s ∈ Icc a b) :
    (timeData d shift rate).anchoredSolve (timeGeometry g shift rate hrate.ne') hab copy (p, Y) s =
      d.anchoredSolve g (time_interval_mono shift hrate hab) copy (p, Y) (shift + rate * s) := by
  let clock : Icc a b → Icc (shift + rate * a) (shift + rate * b) := fun t =>
    ⟨shift + rate * t, time_interval_mono shift hrate t.property.1,
      time_interval_mono shift hrate t.property.2⟩
  have hc : Continuous clock := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hAc : Continuous (fun t : Icc a b =>
      (timeData d shift rate).coefficientAlong (timeGeometry g shift rate hrate.ne') copy ((p, Y),
          t)) := by
    simp only [coefficientAlong_timeData]
    exact (hA.comp hc).const_smul rate
  have hfc : Continuous (fun t : Icc a b =>
      (timeData d shift rate).forcingAlong (timeGeometry g shift rate hrate.ne') copy ((p, Y), t))
          := by
    simp only [forcingAlong_timeData]
    exact (hf.comp hc).const_smul rate
  let u := fun t => d.anchoredSolve g (time_interval_mono shift hrate hab) copy (p, Y)
    (shift + rate * t)
  have hu0 : u a = 0 := d.anchoredSolve_initial g _ copy (p, Y)
  have hu (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt u
      ((timeData d shift rate).coefficientAlong (timeGeometry g shift rate hrate.ne') copy ((p, Y),
          t) (u t) +
        (timeData d shift rate).forcingAlong (timeGeometry g shift rate hrate.ne') copy ((p, Y),
            t)) t := by
    have ht' : shift + rate * t ∈ Icc (shift + rate * a) (shift + rate * b) :=
      ⟨time_interval_mono shift hrate ht.1, time_interval_mono shift hrate ht.2⟩
    have hold := anchoredSolve_hasDerivAt d g (time_interval_mono shift hrate hab)
      copy p Y hA hf ⟨shift + rate * t, ht'⟩
    have hclock : HasDerivAt (fun t : ℝ => shift + rate * t) rate t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul rate).const_add shift
    simpa only [u, coefficientAlong_timeData, forcingAlong_timeData,
      _root_.smul_apply, smul_add, Function.comp_def] using hold.scomp t hclock
  exact (anchoredSolve_unique (timeData d shift rate) (timeGeometry g shift rate hrate.ne')
    hab copy p Y hAc hfc hu0 hu hs).symm

theorem copySolve_timeData (d : LinearData P V E) (g : Geometry)
    (shift rate : ℝ) (hrate : 0 < rate) (hab : a ≤ b)
    (copy : Frequency) (p : P) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.coefficientAlong g copy ((p, Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.forcingAlong g copy ((p, Y), s)))
    (hs : ((timeGeometry g shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    (timeData d shift rate).copySolve (timeGeometry g shift rate hrate.ne') hab copy (p, Y) =
      d.copySolve g (time_interval_mono shift hrate hab) copy (p, Y) := by
  unfold LinearData.copySolve
  rw [anchoredSolve_timeData d g shift rate hrate hab copy p Y hA hf hs]
  congr 1
  exact congrArg Prod.snd (coordinates_timeGeometry g shift rate hrate.ne' copy Y)

/-- Parameter/cover/source transport and exact equality of converted inputs
are algebraic. Only clock transport uses the two finite-path hypotheses. -/
theorem copySolve_of_compatibleInputs (d : LinearData P V E) (e : LinearData Q V E)
    (parameter : Q → P) (g : Geometry) (hab : a ≤ b)
    (gap : ℕ) (shift rate amplitude : ℝ) (hrate : 0 < rate)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      d.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hi : SameInputsAt e (transportData d parameter gap shift rate amplitude) q)
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    e.copySolve (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      amplitude • d.copySolve g (time_interval_mono shift hrate hab) copy
        (parameter q, coverPower gap Y) := by
  have he : e.copySolve (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      (transportData d parameter gap shift rate amplitude).copySolve
        (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) :=
    anchoredSolve_eq_of_sameInputs _ _ _ hab q hi copy Y _
  rw [he]
  unfold transportData transportGeometry
  rw [copySolve_scaleSource, copySolve_transform]
  congr 1
  apply copySolve_timeData d g shift rate hrate hab copy (parameter q) (coverPower gap Y) hA hf
  simpa only [transportGeometry, coordinates_refine] using hslot

end LinearPaths

section TangentPaths

variable {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copySolve_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    (transportTangent t parameter gap shift rate amplitude normalScale).linearData.copySolve
      (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      amplitude • t.linearData.copySolve g (time_interval_mono shift hrate hab) copy
        (parameter q, coverPower gap Y) :=
  copySolve_of_compatibleInputs t.linearData _ parameter g hab gap shift rate amplitude hrate
    q copy Y hA hf (transportTangent_sameInputs t parameter gap shift rate amplitude normalScale
        hnormal q) hslot

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyPressureReal_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    copyPressureReal (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      (rate * amplitude / normalScale) * copyPressureReal t g
        (time_interval_mono shift hrate hab) copy (parameter q, coverPower gap Y) := by
  simp only [copyPressureReal]
  rw [copySolve_transport t parameter g hab gap shift rate amplitude normalScale hrate hnormal
    q copy Y hA hf hslot]
  simp only [transportTangent, nativePoint, coordinates_transport,
    _root_.smul_apply, map_smul, smul_smul]
  rw [mul_comm amplitude rate]
  exact NormalScaling.pressureCoefficient_rescale (H := H) _ _ _ _ _ rate amplitude hnormal

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyPressure_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    copyPressure (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportGeometry g gap shift rate hrate.ne') hab copy frequency (q, Y) =
      ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
        copyPressure t g (time_interval_mono shift hrate hab) copy referenceFrequency
          (parameter q, coverPower gap Y) := by
  have hr : (referenceFrequency : ℂ) ≠ 0 := by exact_mod_cast hreference
  have hk : (frequency : ℂ) ≠ 0 := by exact_mod_cast hfrequency
  have hs : (normalScale : ℂ) ≠ 0 := by exact_mod_cast hnormal
  simp only [copyPressure, copyPressureReal_transport t parameter g hab gap shift rate amplitude
    normalScale hrate hnormal q copy Y hA hf hslot,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.real_smul]
  field_simp

end TangentPaths

section ComplexPaths

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {a b : ℝ}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyVelocity_transport (t : TangentData P ProblemStatement.Space) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hf : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    copyVelocity (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      amplitude • copyVelocity t g (time_interval_mono shift hrate hab) copy
        (parameter q, coverPower gap Y) := by
  unfold copyVelocity
  rw [copySolve_transport t parameter g hab gap shift rate amplitude normalScale hrate hnormal
    q copy Y hA hf hslot, map_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyVelocity_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    complexCopyVelocity (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
      amplitude • complexCopyVelocity t f g (time_interval_mono shift hrate hab) copy
        (parameter q, coverPower gap Y) := by
  simp only [complexCopyVelocity, realData_transport, imagData_transport]
  rw [copyVelocity_transport (realData t f) parameter g hab gap shift rate amplitude normalScale
    hrate hnormal q copy Y hA hReal hslot,
    copyVelocity_transport (imagData t f) parameter g hab gap shift rate amplitude normalScale
    hrate hnormal q copy Y hA hImag hslot]
  simp only [smul_add, smul_comm Complex.I amplitude]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyPressure_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : Continuous (fun s : Icc (shift + rate * a) (shift + rate * b) =>
      (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b) :
    complexCopyPressure (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap shift rate hrate.ne') hab copy frequency (q, Y) =
      ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
        complexCopyPressure t f g (time_interval_mono shift hrate hab) copy referenceFrequency
          (parameter q, coverPower gap Y) := by
  simp only [complexCopyPressure, realData_transport, imagData_transport]
  rw [copyPressure_transport (realData t f) parameter g hab gap shift rate amplitude normalScale
    referenceFrequency frequency hrate hnormal hreference hfrequency q copy Y hA hReal hslot,
    copyPressure_transport (imagData t f) parameter g hab gap shift rate amplitude normalScale
    referenceFrequency frequency hrate hnormal hreference hfrequency q copy Y hA hImag hslot]
  simp only [smul_add, Complex.real_smul]
  ring

private theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst c
  subst d
  rfl

private theorem continuous_interval_congr {E : Type*} [TopologicalSpace E]
    (F : ℝ → E) {a b c d : ℝ} (ha : a = c) (hb : b = d)
    (hf : Continuous (fun s : Icc c d => F s)) :
    Continuous (fun s : Icc a b => F s) := by
  subst c
  subst d
  exact hf

private theorem continuous_zeroEntry_interval {E : Type*} [TopologicalSpace E]
    (L rate : ℝ) (hrate : rate ≠ 0) (F : ℝ → E)
    (hf : Continuous (fun s : Icc 0 L => F s)) :
    Continuous (fun s : Icc (0 + rate * 0) (0 + rate * (L / rate)) => F s) := by
  have h0 : (0 : ℝ) + rate * 0 = 0 := by ring
  have h1 : (0 : ℝ) + rate * (L / rate) = L := by field_simp; simp
  exact continuous_interval_congr F h0 h1 hf

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Exact zero-entry velocity transport from the reference interval `[0,L]`.
The coefficient and the two converted forcing paths are the only analytic
inputs, all restricted to that finite interval. -/
theorem complexCopyVelocity_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc 0 L =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : Continuous (fun s : Icc 0 L =>
      (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : Continuous (fun s : Icc 0 L =>
      (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap 0 rate hrate.ne').coordinates copy Y).2 ∈ Icc 0 (L / rate)) :
    complexCopyVelocity (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le copy (q, Y) =
      amplitude • complexCopyVelocity t f g hL.le copy (parameter q, coverPower gap Y) := by
  have hlen : rate * (L / rate) = L := by field_simp
  have he := complexCopyVelocity_transport (a := 0) (b := L / rate) t f parameter g (div_pos hL
      hrate).le
    gap 0 rate amplitude normalScale hrate hnormal q copy Y
    (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)) hA)
    (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))
          hReal)
    (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))
          hImag) hslot
  refine he.trans (congrArg (fun z : HarmonicCalculus.ComplexVector => amplitude • z) ?_)
  exact interval_congr (fun a b hab => complexCopyVelocity t f g (a := a) (b := b) hab copy
    (parameter q, coverPower gap Y)) _ _ (by ring) (by simpa only [zero_add] using hlen)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The actual pressure retains both the clock/normal factor and the ratio
of reference to current frequency. -/
theorem complexCopyPressure_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (q : Q) (copy : Frequency) (Y : Plane)
    (hA : Continuous (fun s : Icc 0 L =>
      t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : Continuous (fun s : Icc 0 L =>
      (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : Continuous (fun s : Icc 0 L =>
      (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hslot : ((transportGeometry g gap 0 rate hrate.ne').coordinates copy Y).2 ∈ Icc 0 (L / rate)) :
    complexCopyPressure (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le copy frequency (q, Y) =
      ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
        complexCopyPressure t f g hL.le copy referenceFrequency (parameter q, coverPower gap Y) :=
            by
  have hlen : rate * (L / rate) = L := by field_simp
  have he := complexCopyPressure_transport (a := 0) (b := L / rate) t f parameter g (div_pos hL
      hrate).le
    gap 0 rate amplitude normalScale referenceFrequency frequency hrate hnormal hreference
        hfrequency
    q copy Y (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)) hA)
    (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))
          hReal)
    (continuous_zeroEntry_interval L rate hrate.ne'
      (fun s => (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))
          hImag) hslot
  refine he.trans (congrArg (fun z : ℂ =>
    ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) • z) ?_)
  exact interval_congr (fun a b hab => complexCopyPressure t f g (a := a) (b := b) hab copy
    referenceFrequency (parameter q, coverPower gap Y)) _ _ (by
        ring) (by simpa only [zero_add] using hlen)

end ComplexPaths

section ForcingContinuity

variable {P V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

/-- Continuity of the converted forcing can be checked on the finite native
coefficient segment and the corresponding finite common-coordinate path. -/
theorem forcingAlong_continuous (d : LinearData P V E) (g : Geometry)
    (copy : Frequency) (p : P) (Y : Plane)
    (hB : Continuous (fun s : Icc a b => d.forcingMap (p, ((g.coordinates copy Y).1, s))))
    (hf : Continuous (fun s : Icc a b => d.source (p, g.path copy Y s))) :
    Continuous (fun s : Icc a b => d.forcingAlong g copy ((p, Y), s)) :=
  hB.clm_apply hf

theorem real_forcingAlong_continuous (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    (copy : Frequency) (p : P) (Y : Plane)
    (hB : Continuous (fun s : Icc a b => t.linearData.forcingMap (p, ((g.coordinates copy Y).1,
        s))))
    (hf : Continuous (fun s : Icc a b => f (p, g.path copy Y s))) :
    Continuous (fun s : Icc a b => (realData t f).linearData.forcingAlong g copy ((p, Y), s)) :=
  forcingAlong_continuous (realData t f).linearData g copy p Y hB
    (realPart.continuous.comp hf)

theorem imag_forcingAlong_continuous (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    (copy : Frequency) (p : P) (Y : Plane)
    (hB : Continuous (fun s : Icc a b => t.linearData.forcingMap (p, ((g.coordinates copy Y).1,
        s))))
    (hf : Continuous (fun s : Icc a b => f (p, g.path copy Y s))) :
    Continuous (fun s : Icc a b => (imagData t f).linearData.forcingAlong g copy ((p, Y), s)) :=
  forcingAlong_continuous (imagData t f).linearData g copy p Y hB
    (imagPart.continuous.comp hf)

end ForcingContinuity

section Periodized

variable {P Q E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The algebraic periodization step only needs copy identities where its
reference cutoff is nonzero. The following theorems derive those identities
from the actual finite-path solve. -/
private theorem periodizedCopies_transport_of_nonzeroCutoff
    (g : Geometry) (parameter : Q → P) (gap : ℕ) (shift rate scale : ℝ)
    (hrate : rate ≠ 0) (cutoff : Plane → ℝ)
    (F : Frequency → Q × Plane → E) (G : Frequency → P × Plane → E)
    (q : Q) (Y : Plane)
    (hcopy : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      F copy (q, Y) = scale • G copy (parameter q, coverPower gap Y)) :
    periodizedCopies (transportGeometry g gap shift rate hrate)
      (cutoff ∘ nativeTimeMap shift rate) F (q, Y) =
      scale • periodizedCopies g cutoff G (parameter q, coverPower gap Y) := by
  unfold periodizedCopies
  calc
    _ = ∑' copy : Frequency, scale •
        (cutoff (g.coordinates copy (coverPower gap Y)) • G copy (parameter q, coverPower gap Y))
            := by
      apply tsum_congr
      intro copy
      simp only [Function.comp_apply, coordinates_transport]
      by_cases hz : cutoff (g.coordinates copy (coverPower gap Y)) = 0
      · simp only [hz, zero_smul, smul_zero]
      · rw [hcopy copy hz, smul_comm]
    _ = _ := tsum_const_smul'' scale

private theorem current_zeroEntry_slot (g : Geometry) (gap : ℕ) (L rate : ℝ)
    (hrate : 0 < rate) (cutoff : Plane → ℝ)
    (hcutoff : support cutoff ⊆ univ ×ˢ Icc 0 L) (copy : Frequency) (Y : Plane)
    (hactive : cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0) :
    ((transportGeometry g gap 0 rate hrate.ne').coordinates copy Y).2 ∈ Icc 0 (L / rate) := by
  apply (current_slot_iff g gap 0 rate hrate copy Y 0 (L / rate)).mpr
  have hlen : rate * (L / rate) = L := by field_simp
  simpa only [mul_zero, zero_add, hlen] using (hcutoff hactive).2

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Equality of the literal periodized velocities. Only active copies need
continuous reference paths, and only on the interval `[0,L]`. -/
theorem commonVelocity_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (cutoff : Plane → ℝ) (hcutoff : support cutoff ⊆ univ ×ˢ Icc 0 L)
    (q : Q) (Y : Plane)
    (hA : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))) :
    commonVelocity (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le
      (cutoff ∘ nativeTimeMap 0 rate) (q, Y) =
      amplitude • commonVelocity t f g hL.le cutoff (parameter q, coverPower gap Y) := by
  unfold commonVelocity
  apply periodizedCopies_transport_of_nonzeroCutoff
  intro copy hactive
  exact complexCopyVelocity_zeroEntry t f parameter g gap L rate amplitude normalScale
    hL hrate hnormal q copy Y (hA copy hactive) (hReal copy hactive) (hImag copy hactive)
    (current_zeroEntry_slot g gap L rate hrate cutoff hcutoff copy Y hactive)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Equality of the literal periodized pressures, with the same finite
reference paths and the actual inverse-frequency scaling. -/
theorem commonPressure_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    (cutoff : Plane → ℝ) (hcutoff : support cutoff ⊆ univ ×ˢ Icc 0 L)
    (q : Q) (Y : Plane)
    (hA : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        t.linearData.coefficientAlong g copy ((parameter q, coverPower gap Y), s)))
    (hReal : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        (realData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s)))
    (hImag : ∀ copy, cutoff (g.coordinates copy (coverPower gap Y)) ≠ 0 →
      Continuous (fun s : Icc 0 L =>
        (imagData t f).linearData.forcingAlong g copy ((parameter q, coverPower gap Y), s))) :
    commonPressure (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le
      (cutoff ∘ nativeTimeMap 0 rate) frequency (q, Y) =
      ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
        commonPressure t f g hL.le cutoff referenceFrequency (parameter q, coverPower gap Y) := by
  unfold commonPressure
  apply periodizedCopies_transport_of_nonzeroCutoff
  intro copy hactive
  exact complexCopyPressure_zeroEntry t f parameter g gap L rate amplitude normalScale
    referenceFrequency frequency hL hrate hnormal hreference hfrequency q copy Y
    (hA copy hactive) (hReal copy hactive) (hImag copy hactive)
    (current_zeroEntry_slot g gap L rate hrate cutoff hcutoff copy Y hactive)

end Periodized

end NavierStokes.IntervalCopyTransport
