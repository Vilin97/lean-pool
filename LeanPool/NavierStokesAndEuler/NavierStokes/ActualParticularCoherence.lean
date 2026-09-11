/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualReferenceRebase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCoreSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledTangentTransport

/-!
# Coherence of the actual particular increment

The source is the residual of the current state.  Its reference value is
rebased to the native cover before solving.  The identities below retain the
full auxiliary fibers and the differentiated copy cutoffs.
-/

section

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

end
end

end

section

/-!
# Naturality of the actual Gaussian cutoff error

The error is the sum of differentiated-cutoff terms and the uncovered
source. Both terms are transported from their primitive data before the
copy sum is taken.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.GaussianErrorNaturality

open Set Filter Function HarmonicCalculus LinearWaveBounds
open scoped Topology ContDiff

section CopyTransport

variable {D E I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fast_cutoff_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x)) :
    d.Dfast (fun m => a.cutoff m i) n x =
      rate * dr.Dfast (fun m => b.cutoff m i) nr (Γ x) := by
  have hc := hdiff.hasFDerivAt.comp x Γ.hasFDerivAt
  simp only [Function.comp_def] at hc
  simp only [GraphDirections.Dfast, along, hcutoff, hc.fderiv,
    ContinuousLinearMap.comp_apply, hfast, map_smul, smul_eq_mul]

theorem cutoffSum_transport (Γ : D →L[ℝ] E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i x = b.cutoff nr i (Γ x)) :
    a.cutoffSum n x = b.cutoffSum nr (Γ x) := by
  exact tsum_congr hcutoff

theorem localTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.localTail d n i x = (rate * c) • b.localTail dr nr i (Γ x) := by
  unfold PeriodizedWaveBounds.CopyData.localTail
  rw [fast_cutoff_transport Γ d dr a b n nr rate i x hcutoff hfast hdiff]
  by_cases hz : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) = 0
  · simp [hz]
  · rw [hamplitude hz, smul_smul, smul_smul]
    congr 1
    ring

/-- Only copies with a nonzero differentiated reference cutoff need an
amplitude comparison. No exterior continuation of a Volterra solve is assumed. -/
theorem globalTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.globalTail d n x = (rate * c) • b.globalTail dr nr (Γ x) := by
  change (∑' i, a.localTail d n i x) = (rate * c) • ∑' i, b.localTail dr nr i (Γ x)
  calc
    _ = ∑' i, (rate * c) • b.localTail dr nr i (Γ x) := tsum_congr fun i =>
      localTail_transport Γ d dr a b n nr rate c i x (hcutoff i) hfast (hdiff i) (hamplitude i)
    _ = _ := tsum_const_smul'' (rate * c)

/-- Full transport of the actual Gaussian error, including the source
on the part of the domain uncovered by native cutoffs. -/
theorem globalGaussian_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x))
    (hsource : a.source n x = (rate * c) • b.source nr (Γ x)) :
    a.globalGaussian d n x = (rate * c) • b.globalGaussian dr nr (Γ x) := by
  rw [PeriodizedWaveBounds.CopyData.globalGaussian,
    globalTail_transport Γ d dr a b n nr rate c x hcutoff hfast hdiff hamplitude,
    cutoffSum_transport Γ a b n nr x (fun i => congrFun (hcutoff i) x), hsource]
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, smul_add, smul_smul]
  congr 1
  congr 1
  ring

end CopyTransport

section ReferenceData

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState

/-- Parameter: an abbreviation for `PhysicalParticularWave.Parameter`. -/
abbrev Parameter := PhysicalParticularWave.Parameter
/-- Wave space: an abbreviation for `PhysicalParticularWave.WaveSpace`. -/
abbrev WaveSpace := PhysicalParticularWave.WaveSpace
/-- Cylinder: an abbreviation for `PhysicalParticularWave.Cylinder`. -/
abbrev Cylinder := PhysicalParticularWave.Cylinder

/-- The full native change of variables, conjugate to the actual
cylindrical change of band and common cover. -/
noncomputable def waveChange (h Q Qr : ℝ) (gap : ℕ) : WaveSpace →L[ℝ] WaveSpace :=
  PhysicalParticularWave.waveEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PhysicalParticularWave.cylinderChange h Q Qr gap).comp
      PhysicalParticularWave.waveEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem waveChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : WaveSpace) :
    waveChange h Q Qr gap x =
      ((PhysicalParticularWave.parameterChange h Q Qr x.1.1, x.1.2), coverPower gap x.2) := rfl

theorem waveChange_waveEquiv (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    waveChange h Q Qr gap (PhysicalParticularWave.waveEquiv x) =
      PhysicalParticularWave.waveEquiv (PhysicalParticularWave.cylinderChange h Q Qr gap x) := rfl

/-- The actual untransported reference data, evaluated at its own band. -/
noncomputable def referenceParameters (D : AssemblyData Parameter) :
    CorrectionStep.ParticularParameters Parameter where
  tangent j _ := D.reference.tangent j
  geometry _ := D.reference.geometry
  length _ := D.reference.length
  length_pos _ := D.reference.length_pos
  cutoff _ := D.reference.cutoff
  background := D.background
  directions := D.directions

/-- Native data as an element of `PeriodizedWaveBounds.CopyData WaveSpace Frequency`. -/
noncomputable def nativeData (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) :
    PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

/-- Reference data, given by `(referenceParameters D).copyData D.context D.state D.carrierBlock
D.gaussianInput D.aliasInput j`. -/
noncomputable def referenceData (D : AssemblyData Parameter) (j : ℤ) :
    PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (referenceParameters D).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

theorem copyData_amplitude (p : CorrectionStep.ParticularParameters Parameter)
    (C : Context (Parameter × Plane)) (u : State (Parameter × Plane))
    (b : HarmonicBlock (Parameter × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Parameter × Plane))
    (j : ℤ) (n : ℕ) (copy : Frequency) (x : WaveSpace) :
    (p.copyData C u b G A j).amplitude n copy x =
      complexCopyVelocity (p.tangent j n) (residualSource C u b G A j n)
        (p.geometry n) (p.length_pos n).le copy (x.1.1, x.2) :=
  complexCopyVelocity_angle (p.tangent j n) (residualSource C u b G A j n)
    (p.geometry n) (p.length_pos n).le copy x.1.1 x.1.2 x.2

theorem native_cutoff_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n : ℕ) (copy : Frequency) :
    (nativeData D h gap j).cutoff n copy = fun x =>
      (referenceData D j).cutoff D.reference.band copy
        (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  funext x
  change D.reference.cutoff
      (CopySolveCompatibility.nativeTimeMap 0
        (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
        ((CopySolveCompatibility.transportGeometry D.reference.geometry (gap n) 0
          (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
              _).coordinates copy x.2)) =
    D.reference.cutoff (D.reference.geometry.coordinates copy (coverPower (gap n) x.2))
  erw [ScaledTangentTransport.coordinates_transport]

theorem reference_cutoff_differentiable (D : AssemblyData Parameter) (j : ℤ)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (copy : Frequency) (x : WaveSpace) :
    DifferentiableAt ℝ ((referenceData D j).cutoff D.reference.band copy) x := by
  change DifferentiableAt ℝ (fun y : WaveSpace =>
    D.reference.cutoff (D.reference.geometry.coordinates copy y.2)) x
  exact ((hcutoff.comp (D.reference.geometry.coordinates_contDiff copy)).comp
    contDiff_snd).contDiffAt.differentiableAt (by simp)

/-- A nonzero actual directional derivative is supported in any closed
set supporting the original cutoff. -/
theorem along_ne_zero_mem_closed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {K : Set E} (hK : IsClosed K) (hf : support f ⊆ K)
    (V : E → E) {x : E} (hx : along V f x ≠ 0) : x ∈ K := by
  have hd : x ∈ support (fderiv ℝ f) := by
    intro hz
    apply hx
    simp only [along, hz, _root_.zero_apply]
  exact (closure_minimal hf hK) (support_fderiv_subset ℝ hd)

theorem reference_derivative_mem_slot (D : AssemblyData Parameter) (j : ℤ)
    {U : Set Parameter} (R : PhysicalParticularWave.ReferenceODE D j U)
    (copy : Frequency) {x : WaveSpace}
    (hx : D.directions.Dfast (fun m => (referenceData D j).cutoff m copy) D.reference.band x ≠ 0) :
    (D.reference.geometry.coordinates copy x.2).2 ∈ Icc 0 D.reference.length := by
  let K : Set WaveSpace := {y | (D.reference.geometry.coordinates copy y.2).2 ∈ Icc 0
      D.reference.length}
  have hK : IsClosed K := isClosed_Icc.preimage
    (((D.reference.geometry.coordinates_contDiff copy).continuous.comp continuous_snd).snd)
  apply along_ne_zero_mem_closed hK (V := D.directions.fastField D.reference.band) _ hx
  intro y hy
  exact (R.cutoff hy).2

theorem current_slot_of_reference_derivative (D : AssemblyData Parameter) (h : ℝ)
    (gap : ℕ → ℕ) (j : ℤ) (n : ℕ) {U : Set Parameter}
    (R : PhysicalParticularWave.ReferenceODE D j U) (copy : Frequency) (x : WaveSpace)
    (hx : D.directions.Dfast (fun m => (referenceData D j).cutoff m copy) D.reference.band
      (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) ≠ 0) :
    (((CorrectionStep.ParticularParameters.fromReference D h gap).geometry n).coordinates copy
        x.2).2 ∈
      Icc 0 ((CorrectionStep.ParticularParameters.fromReference D h gap).length n) := by
  let rate := PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
      D.reference.band)
  have hrate : 0 < rate := PhysicalParticularWave.ratioPower_pos
    (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band) _
  have hs := reference_derivative_mem_slot D j R copy hx
  change (D.reference.geometry.coordinates copy (coverPower (gap n) x.2)).2 ∈
    Icc 0 D.reference.length at hs
  apply (ScaledTangentTransport.current_slot_iff D.reference.geometry (gap n) 0 rate hrate
    copy x.2 0 (D.reference.length / rate)).mpr
  have hlen : rate * (D.reference.length / rate) = D.reference.length := by field_simp
  simpa only [zero_add, mul_zero, hlen] using hs

theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst c
  subst d
  rfl

theorem complexCopyVelocity_zeroEntry
    (t : TangentData Parameter ProblemStatement.Space) (f : Parameter × Plane → ComplexVector)
    (parameter : Parameter → Parameter) (g : Geometry) (gap : ℕ)
    (L rate amplitude normalScale : ℝ) (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set Parameter} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ)) (q : Parameter) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne').coordinates copy
        Y).2 ∈
      Icc 0 (L / rate)) :
    complexCopyVelocity (ScaledTangentTransport.transportTangent t parameter gap 0 rate amplitude
        normalScale)
      (ScaledTangentTransport.transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le copy
          (q, Y) =
        amplitude • complexCopyVelocity t f g hL.le copy (parameter q, coverPower gap Y) := by
  have he := ScaledTangentTransport.complexCopyVelocity_transport t f parameter g (div_pos hL
      hrate).le
    gap 0 rate amplitude normalScale hrate hnormal hA hB hf q hq copy Y hslot
  refine he.trans (congrArg (fun z : ComplexVector => amplitude • z) ?_)
  apply interval_congr (fun a b hab => complexCopyVelocity t f g (a := a) (b := b) hab
    copy (parameter q, coverPower gap Y)) _ _ (by ring)
  field_simp; simp

end ReferenceData

section ActualReference

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave

theorem native_source_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    (x : WaveSpace) :
    (nativeData D h gap j).source n x =
      (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
        velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band)) •
      (referenceData D j).source D.reference.band
        (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  exact congrFun (H.source_eq hn hr j) (x.1.1, x.2)

theorem native_amplitude_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (copy : Frequency) (x : WaveSpace)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1.1 ∈ U)
    (hslot : (((CorrectionStep.ParticularParameters.fromReference D h gap).geometry n).coordinates
        copy x.2).2 ∈
      Icc 0 ((CorrectionStep.ParticularParameters.fromReference D h gap).length n)) :
    (nativeData D h gap j).amplitude n copy x =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (referenceData D j).amplitude D.reference.band copy
          (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  unfold nativeData referenceData
  rw [copyData_amplitude, copyData_amplitude, H.source_eq hn hr j]
  exact complexCopyVelocity_zeroEntry (D.reference.tangent j) (referenceSource D j)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)) D.reference.geometry
        (gap n)
    D.reference.length (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (normalWeight (ChartScales.Q n) (ChartScales.Q D.reference.band)
      ((j : ℝ) * D.carrierBlock.frequency n) (referenceFrequency D j))
    D.reference.length_pos (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos
        D.reference.band) _)
    (normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band) hK hKr)
    R.coefficient R.forcing R.source x.1.1 hx copy x.2 hslot

/-- The fast transport hypothesis follows from the actual slot-direction
identities stored by the primitive copy geometry. -/
theorem fast_transport_of_slotDirections (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (n : ℕ)
    (hn : D.directions.fastScale n • D.directions.fast =
      ((0 : Parameter × ℝ), slotDirection ((CorrectionStep.ParticularParameters.fromReference D h
          gap).geometry n)))
    (hr : D.directions.fastScale D.reference.band • D.directions.fast =
      ((0 : Parameter × ℝ), slotDirection D.reference.geometry)) :
    waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast) := by
  rw [hn, hr]
  have he := ScaledTangentTransport.slotDirection_transport D.reference.geometry (gap n) 0
    (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
      (CoordinateAlgebra.A h + 1 / 2)).ne'
  have hh := congrArg (fun Y : Plane => ((0 : Parameter × ℝ), Y)) he
  simp only [Prod.mk.injEq, true_and, waveChange_apply, parameterChange, one_div, Prod.fst_zero,
      mul_zero, Prod.snd_zero, Prod.smul_mk, smul_zero, Prod.mk_eq_zero, and_self] at hh ⊢
  exact hh

/-- The actual transported reference solve has the derived Gaussian
source weight on the full native cylinder, including uncovered points. -/
theorem fromReference_globalGaussian (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : WaveSpace)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1.1 ∈ U) :
    (nativeData D h gap j).globalGaussian D.directions n x =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (referenceData D j).globalGaussian D.directions D.reference.band
          (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  rw [← clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)]
  apply globalGaussian_transport _ D.directions D.directions _ _ n D.reference.band _ _ x
    (native_cutoff_transport D h gap j n) hfast
  · exact fun copy => reference_cutoff_differentiable D j hcutoff copy _
  · intro copy hcopy
    exact native_amplitude_transport D h gap j n i H hn hr R hK hKr copy x hx
      (current_slot_of_reference_derivative D h gap j n R copy x hcopy)
  · exact native_source_transport D h gap j n i H hn hr x

theorem fromReference_globalGaussian_cylinder (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Cylinder)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (PhysicalParticularWave.waveEquiv x).1.1 ∈ U) :
    (nativeData D h gap j).globalGaussian D.directions n (PhysicalParticularWave.waveEquiv x) =
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) ^ 2 *
        ratioPower (ChartScales.Q n) (ChartScales.Q D.reference.band) (1 / 2)) •
      (referenceData D j).globalGaussian D.directions D.reference.band
        (PhysicalParticularWave.waveEquiv
          (cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x)) := by
  rw [pow_two, PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band)]
  simpa only [waveChange_waveEquiv] using
    fromReference_globalGaussian D h gap j n i H hn hr R hcutoff hK hKr hfast
      (PhysicalParticularWave.waveEquiv x) hx

end ActualReference

section HarmonicAssembly

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave
open scoped BigOperators

/-- A single actual Gaussian Fourier contribution transports with its
full angular carrier. The reference phase relation is primitive block
coherence; the Gaussian coefficient relation is proved from the solve. -/
theorem fromReference_gaussian_character (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Parameter × Plane) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1 ∈ U)
    (θ : ℝ) (k : Fin 3) :
    ((nativeData D h gap j).globalGaussian D.directions n (angleShuffle (x, 0)) k *
      HarmonicFields.character j (D.carrierBlock.frequency n * D.carrierBlock.phase n x +
        (D.carrierBlock.angularFrequency n : ℝ) * θ)).re =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
      ((referenceData D j).globalGaussian D.directions D.reference.band
        (angleShuffle (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) (gap n) x, 0)) k *
        HarmonicFields.character j (D.carrierBlock.frequency D.reference.band *
          D.carrierBlock.phase D.reference.band
            (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
              (ChartScales.Q_pos D.reference.band) (gap n) x) +
          (D.carrierBlock.angularFrequency D.reference.band : ℝ) * θ)).re := by
  have hg := fromReference_globalGaussian D h gap j n i H hn hr R hcutoff hK hKr hfast
    (angleShuffle (x, 0)) hx
  have hp := H.block.phase (x := x) hxpos
  dsimp only at hp
  rw [hg, hp, H.block.angular]
  simp only [Pi.smul_apply, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  rfl

/-- Naturality of the actual finite Gaussian harmonic block, with all
angular variables retained. No equality of Gaussian outputs is assumed. -/
theorem fromReference_gaussianBlock (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (N n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ∀ j ∈ modes N, ReferenceODE D j U)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Parameter × Plane) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1 ∈ U)
    (θ : ℝ) (k : Fin 3) :
    ((CorrectionStep.ParticularParameters.fromReference D h gap).gaussianBlock
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N).oscillation n (x, θ) k =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
      ((referenceParameters D).gaussianBlock D.context D.state D.carrierBlock D.gaussianInput
          D.aliasInput N).oscillation
        D.reference.band
        (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) (gap n) x, θ) k := by
  unfold CorrectionStep.ParticularParameters.gaussianBlock
  rw [assembledBlock_value, assembledBlock_value, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast ((mem_modes N j).mp hj).1
  exact fromReference_gaussian_character D h gap j n i H hn hr (R j hj) hcutoff
    (mul_ne_zero hj0 (hfrequency n)) (mul_ne_zero hj0 (hfrequency D.reference.band))
    hfast x hxpos hx θ k

/-- The same finite-block statement on the original full cylindrical
coordinates, with the source weight explicitly written as `c^2 * l`. -/
theorem fromReference_gaussianBlock_cylinder (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (N n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    {U : Set Parameter} (R : ∀ j ∈ modes N, ReferenceODE D j U)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Cylinder) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (PhysicalParticularWave.waveEquiv x).1.1 ∈ U) (k : Fin 3) :
    ((CorrectionStep.ParticularParameters.fromReference D h gap).gaussianBlock
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N).oscillation n
        (angleShuffle.symm (PhysicalParticularWave.waveEquiv x)) k =
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) ^ 2 *
        ratioPower (ChartScales.Q n) (ChartScales.Q D.reference.band) (1 / 2)) *
      ((referenceParameters D).gaussianBlock D.context D.state D.carrierBlock D.gaussianInput
          D.aliasInput N).oscillation
        D.reference.band
        (angleShuffle.symm (PhysicalParticularWave.waveEquiv
          (cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x))) k := by
  rw [pow_two, PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band)]
  exact fromReference_gaussianBlock D h gap N n i H hn hr R hcutoff hfrequency hfast
    ((PhysicalParticularWave.waveEquiv x).1.1, (PhysicalParticularWave.waveEquiv x).2)
    hxpos hx (PhysicalParticularWave.waveEquiv x).1.2 k

end HarmonicAssembly

end NavierStokes.GaussianErrorNaturality

end
end

end

section

/-!
# Continuity on the actual finite tangent-copy intervals

The projected operator is built from the selected frame's normal, normal
motion, base action, and damping. Only the native slow point and finite
clock interval enter its regularity; the transverse coordinate is free.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCopySliceRegularity

open Set Function Filter
open CommonCoverSolve PhaseJetBounds PrimaryPulseBounds
open CorrectionInitialization
open scoped ContDiff Topology InnerProductSpace

/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane
/-- Parameter: an abbreviation for `PhysicalParticularWave.Parameter`. -/
abbrev Parameter := PhysicalParticularWave.Parameter
/-- Label: an abbreviation for `ActualParticularStageControls.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualParticularStageControls.Label B N0

theorem negativeProjection_continuousOn {X : Type*} [TopologicalSpace X]
    {U : Set X} {N : X → Space} (hN : ContinuousOn N U)
    (hne : ∀ x ∈ U, N x ≠ 0) :
    ContinuousOn (fun x => negativeTangentProjection (N x)) U := by
  have hv : ContinuousOn (fun x => (⟪N x, N x⟫_ℝ)⁻¹ • N x) U :=
    ((hN.inner hN).inv₀ (fun x hx => inner_self_ne_zero.mpr (hne x hx))).fun_smul hN
  have hi := (innerSL ℝ).continuous.comp_continuousOn hN
  exact (continuousOn_const.sub
    (isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (hi.prodMk hv))).neg

section Frame

variable {ι : Type} {D : Domain ι PhaseCalculus.Slow}

/-- The actual ambient projected operator and forcing projection of the
selected frame are continuous on the entire closed slot. -/
theorem frame_slices (F : PhaseConstruction D) (i : ι) (j : ℤ)
    (p : PhaseCalculus.Slow) (hp : p ∈ D.carrier i) :
    Continuous (fun s : Icc (0 : ℝ) (F.L i) =>
      TangentODE.projectedOperator ((F.frame i).normal (p, s))
        ((F.frame i).normalMotion (p, s))
        (PrimaryCopyBridge.baseOperator ((F.frame i).F (p, s)) ((F.frame i).shear (p, s)))
        ((F.frame i).damping j (p, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (F.L i) => negativeTangentProjection ((F.frame i).normal (p,
        s))) := by
  have hd := (ActualParticularControl.selected_frame_jets F).smoothOn i
  have hmap : MapsTo (fun s : ℝ => (p, s)) (Icc 0 (F.L i)) ((D.slot F.V F.openV).carrier i) :=
    fun s hs => ⟨hp, F.interval i hs⟩
  have hn := (PrimaryCopyBridge.frame_normal_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hnd := (PrimaryCopyBridge.frame_normalMotion_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hA := (PrimaryCopyBridge.frame_baseOperator_continuousOn hd).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hδ : ContinuousOn (fun s : ℝ => (F.frame i).damping j (p, s)) (Icc 0 (F.L i)) :=
    (continuousOn_const.mul hd.viscosity.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hne : ∀ s ∈ Icc 0 (F.L i), (F.frame i).normal (p, s) ≠ 0 := by
    intro s hs
    exact MovingFrameODE.normal_ne_zero _
      ((ActualParticularControl.selected_kinematics F i hp).beta_ne_zero s hs)
  exact ⟨(PrimaryCopyBridge.projectedOperator_continuousOn hn hnd hA hδ hne).domRestrict,
    (negativeProjection_continuousOn hn hne).domRestrict⟩

end Frame

section Transport

variable {P Q : Type}

theorem transported_coefficient (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal : ℝ) (hn : normal ≠ 0) (q : Q) (Y : Plane) :
    (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
        normal).linearData.coefficient (q, Y) =
      rate • t.linearData.coefficient (φ q, CopySolveCompatibility.nativeTimeMap 0 rate Y) :=
  NormalScaling.projectedOperator_rescale _ _ _ rate _ hn

theorem transported_forcingMap (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal : ℝ) (hn : normal ≠ 0) (q : Q) (Y : Plane) :
    (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude normal).linearData.forcingMap
        (q, Y) =
      t.linearData.forcingMap (φ q, CopySolveCompatibility.nativeTimeMap 0 rate Y) :=
  NormalScaling.negativeTangentProjection_smul _ hn

theorem transported_slices (t : TangentData P Space) (φ : Q → P)
    (gap : ℕ) (rate amplitude normal L : ℝ) (hrate : 0 < rate) (hn : normal ≠ 0)
    (q : Q) (xi : ℝ)
    (hA : Continuous (fun s : Icc (0 : ℝ) L => t.linearData.coefficient (φ q, (xi, s))))
    (hB : Continuous (fun s : Icc (0 : ℝ) L => t.linearData.forcingMap (φ q, (xi, s)))) :
    Continuous (fun s : Icc (0 : ℝ) (L / rate) =>
      (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
          normal).linearData.coefficient (q, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (L / rate) =>
      (ScaledTangentTransport.transportTangent t φ gap 0 rate amplitude
          normal).linearData.forcingMap (q, (xi, s))) := by
  let clock : Icc (0 : ℝ) (L / rate) → Icc (0 : ℝ) L := fun s =>
    ⟨rate * s, mul_nonneg hrate.le s.property.1,
      by simpa only [mul_comm] using (le_div_iff₀ hrate).mp s.property.2⟩
  have hc : Continuous clock :=
    Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  constructor
  · apply ((hA.comp hc).fun_const_smul rate).congr
    intro s
    simpa only [Function.comp_apply, clock, CopySolveCompatibility.nativeTimeMap, zero_add] using
      (transported_coefficient t φ gap rate amplitude normal hn q (xi, s)).symm
  · apply (hB.comp hc).congr
    intro s
    simpa only [Function.comp_apply, clock, CopySolveCompatibility.nativeTimeMap, zero_add] using
      (transported_forcingMap t φ gap rate amplitude normal hn q (xi, s)).symm

end Transport

section Actual

open ActualParticularStageControls

variable {B N0 : ℕ}

theorem reference_slices (l : Label B N0) (j : ℤ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter p ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) (reference l).length =>
      ((reference l).tangent j).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) (reference l).length =>
      ((reference l).tangent j).linearData.forcingMap (p, (xi, s))) :=
  frame_slices (ActualPrimary.phases B N0 l.1) l.2 j (ActualSignedGeometry.swapParameter p) hp

theorem normalWeight_ne (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (reference l).band)
      ((j : ℝ) * ChartScales.carrier ActualPrimary.h n)
      ((j : ℝ) * ChartScales.carrier ActualPrimary.h (reference l).band) ≠ 0 := by
  rw [ScaledActualParticularControl.normalWeight_harmonic _ _ _ _ j hj]
  apply mul_ne_zero
  · exact div_ne_zero (ActualPrimary.chartCoefficients_frequency_pos l.1 l.2 _).ne'
      (ActualPrimary.chartCoefficients_frequency_pos l.1 l.2 _).ne'
  · exact (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _).ne'

/-- No transverse or copy restriction occurs in these two primitive slice
continuities. The only spatial hypothesis is the actual native phase cell. -/
theorem canonical_slices (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) ((canonicalParameters l).length n) =>
      ((canonicalParameters l).tangent j n).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) ((canonicalParameters l).length n) =>
      ((canonicalParameters l).tangent j n).linearData.forcingMap (p, (xi, s))) := by
  obtain ⟨hA, hB⟩ := reference_slices l j _ hp xi
  exact transported_slices ((reference l).tangent j) _ _ _ _ _ _
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _)
    (normalWeight_ne l j hj n) p xi hA hB

theorem actual_slices (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (xi : ℝ) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficient (p, (xi, s))) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap (p, (xi, s))) := by
  rw [parameters_eq_canonical x l hfrequency]
  exact canonical_slices l j hj n p hp xi

theorem actual_copy_slices (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter)
    (hp : ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2)
    (Y : Plane) (k : TorusInverse.Frequency) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficientAlong ((parameters x l).geometry n) k
          ((p, Y), s)) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap
        (p, ((((parameters x l).geometry n).coordinates k Y).1, s))) :=
  actual_slices x l hfrequency j hj n p hp _

end Actual

section SourceFiber

open ActualParticularStageControls

variable {B N0 : ℕ}

theorem native_parameter_eq (l : Label B N0) (n : ℕ) (p : Parameter) (Y : Plane) :
    ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) =
      ActualPrimaryCovariance.nativePoint n (p.1, (p.2, Y)) l.2 := by
  ext <;> simp [ActualSignedGeometry.swapParameter, PhysicalParticularWave.parameterChange,
    PhysicalParticularWave.ratioPower, ActualPrimaryCovariance.nativePoint,
    ActualPrimary.nativeSlow, ActualPrimary.toAbsolute, reference, Real.sqrt_eq_rpow,
    div_eq_mul_inv, mul_assoc, mul_comm]

theorem native_cell_of_refinedCarrier (l : Label B N0) (n : ℕ) (p : Parameter)
    (hT : 0 < p.2.1) {Y : Plane}
    (hY : (p.1, (p.2, Y)) ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    ActualSignedGeometry.swapParameter
      (PhysicalParticularWave.parameterChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (reference l).band) p) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
          N0).prepared.N).carrier l.2 := by
  rw [native_parameter_eq l n p Y]
  exact ActualCarrierGeometry.labelCarrier_in_cell l n hT
    (ActualCoreSupport.refinedCarrier_subset_broad (l.2, l.1) n hY)

/-- A nonempty refined source fiber supplies the native phase-cell
hypothesis. All copies and every transverse coordinate are then covered. -/
theorem actual_copy_slices_of_refinedFiber (x : CorrectionStep.CycleState (Label B N0)) (l : Label
    B N0)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h
        n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter) (hT : 0 < p.2.1)
    (hs : ∃ Z : Plane, (p.1, (p.2, Z)) ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n)
    (Y : Plane) (k : TorusInverse.Frequency) :
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.coefficientAlong ((parameters x l).geometry n) k
          ((p, Y), s)) ∧
    Continuous (fun s : Icc (0 : ℝ) ((parameters x l).length n) =>
      ((parameters x l).tangent j n).linearData.forcingMap
        (p, ((((parameters x l).geometry n).coordinates k Y).1, s))) := by
  obtain ⟨Z, hZ⟩ := hs
  exact actual_copy_slices x l hfrequency j hj n p (native_cell_of_refinedCarrier l n p hT hZ) Y k

end SourceFiber

end NavierStokes.ActualCopySliceRegularity

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularCoherence

open Set Function Filter WeightedClasses CorrectionState HarmonicCalculus
open CommonCoverSolve TorusInverse PhysicalParticularWave
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

/-- Label: an abbreviation for `ActualParticularStageControls.Label`. -/
abbrev Label := ActualParticularStageControls.Label

/-- The unchanged current-state copy construction. -/
noncomputable def copyData (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) : PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (ActualParticularStageControls.parameters x l).copyData
    (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j

/-- Corrected, constructed using `ActualParticularRealization.corrected`. -/
noncomputable def corrected (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) : LinearWaveBounds.WaveCoefficients WaveSpace :=
  ActualParticularRealization.corrected (ActualParticularStageControls.assembly x l)
    ActualParticularStageControls.associatedStrip h (ActualParticularStageControls.gap l) j

/-- Cylinder parameter, given by `(waveEquiv z).1.1`. -/
noncomputable def cylinderParameter (z : Cylinder) : Parameter := (waveEquiv z).1.1

/-- Cylinder domain, given by `{z | (cylinderParameter z).2 ∈ V}`. -/
noncomputable def cylinderDomain (V : Set Plane) : Set Cylinder :=
  {z | (cylinderParameter z).2 ∈ V}

theorem cylinderDomain_open {V : Set Plane} (hV : IsOpen V) : IsOpen (cylinderDomain V) :=
  hV.preimage waveEquiv.continuous.fst.fst.snd

/-- The target operator is the literal common-cover graph at the target
band.  This identification is independent of the current source. -/
theorem targetChart (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    ActualParticularRealization.TargetChart (ActualParticularStageControls.assembly x l)
      ActualParticularStageControls.associatedStrip h n (CommonWindow.index h n) := by
  constructor
  · rfl
  · funext z
    apply waveEquiv.injective
    change (ActualParticularStageControls.directions (B := B)).radialField n (waveEquiv z) = _
    rw [ActualReferenceRebase.associatedDirections_radial,
      ActualReferenceRebase.associatedContext_frame]
    rfl
  · rfl
  · funext z
    apply waveEquiv.injective
    change (ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip)
        n (waveEquiv z) = _
    rw [ActualReferenceRebase.associatedDirections_axial,
      ActualReferenceRebase.associatedContext_frame]
    rfl

theorem corrected_amplitude_chart (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    (fun z => (corrected x l j).amplitude n (waveEquiv z)) =
      CurlClassBounds.realizedCoefficient ((j : ℝ) * (x.coefficients.blocks l).frequency n)
        PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
        (fun z => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv z))
        (fun z => (ActualReferenceRebase.actualCoefficients x l j).amplitude n (waveEquiv z)) := by
  have hp := ActualParticularRealization.realizedCoefficient_pull waveEquiv
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    ((ActualParticularStageControls.assembly x l).background.radius n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
    ((ActualParticularStageControls.assembly x l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.assembly x l).directions.angular)
    ((ActualParticularStageControls.assembly x l).directions.axialField
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip) n)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude n)
  rw [(targetChart x l n).radius, (targetChart x l n).radial,
    (targetChart x l n).angular, (targetChart x l n).axial] at hp
  exact hp.symm

/-- Local agreement of the two primitive inputs propagates through the
entire curl correction, including all cutoff derivatives. -/
theorem corrected_eq_band_of_germs (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) (z : Cylinder)
    (ha : (fun y => (ActualReferenceRebase.actualCoefficients x l j).amplitude n (waveEquiv y))
      =ᶠ[𝓝 z] bandRaw (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j)
    (hphi : (fun y => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv y))
      =ᶠ[𝓝 z] bandPhase (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j) :
    vectorMode ((corrected x l j).frequency n) ((corrected x l j).phase n)
      ((corrected x l j).amplitude n) (waveEquiv z) =
      bandVelocity (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (CommonWindow.index h n)
        (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j z := by
  have hg := ParticularWaveAssembly.realizedCoefficient_germ ha
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (fun y => (ActualReferenceRebase.actualCoefficients x l j).phase n (waveEquiv y))
  have hq := ActualParticularRealization.realizedCoefficient_phase_germ hphi
    ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).axial
    (bandRaw (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
      (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) j)
  have hv := congrFun (corrected_amplitude_chart x l j n) z
  rw [(hg.trans hq).eq_of_nhds] at hv
  funext i
  change (corrected x l j).amplitude n (waveEquiv z) i *
    carrier ((j : ℝ) * (x.coefficients.blocks l).frequency n)
      ((ActualReferenceRebase.actualCoefficients x l j).phase n) (waveEquiv z) = _
  rw [hv]
  exact congrArg₂ (· * ·) rfl (PhysicalCurlCovariance.carrier_eq_of_products
    (congrArg (((j : ℝ) * (x.coefficients.blocks l).frequency n) * ·) hphi.eq_of_nhds))

/-- Forward cover order: the germ inputs are consequences of the current
state and coefficient identities, not assumptions about the solved wave. -/
theorem corrected_forward (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n (BaseChartJets.cellBand l.2) k)
    (HB : ActualReferenceRebase.BlockComparison x l V n (BaseChartJets.cellBand l.2) k)
    (j : ℤ) (hj : j ≠ 0)
    (hn : (x.coefficients.blocks l).frequency n ≠ 0)
    (hm : (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) ≠ 0)
    (z : Cylinder) (hz : z ∈ cylinderDomain V) :
    vectorMode ((corrected x l j).frequency n) ((corrected x l j).phase n)
      ((corrected x l j).amplitude n) (waveEquiv z) =
      bandVelocity (ActualReferenceRebase.nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (CommonWindow.index h n)
        (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j z := by
  apply corrected_eq_band_of_germs
  · filter_upwards [(cylinderDomain_open hV).mem_nhds hz] with y hy
    exact ActualReferenceRebase.actualAmplitude_forward x l hV htime n k hi HS HB j
      (cylinderParameter y) hy (waveEquiv y).1.2 (waveEquiv y).2
  · filter_upwards [(cylinderDomain_open hV).mem_nhds hz] with y hy
    exact (ActualReferenceRebase.actualPhase_forward x l V n k hi HB j hj hn hm
      (cylinderParameter y) hy (waveEquiv y).1.2 (waveEquiv y).2).symm

/-! ## Composition of the actual primitive copy data

These identities allow two current bands to be compared directly.  In
particular, they do not require extending a current reference-band state
outside the slow overlap on which state coherence was proved.
-/

theorem ratioPower_comp {Q Qm Qr : ℝ} (hQm : 0 < Qm) (a : ℝ) :
    ratioPower Q Qm a * ratioPower Qm Qr a = ratioPower Q Qr a := by
  unfold ratioPower
  exact div_mul_div_cancel₀ (Real.rpow_pos_of_pos hQm a).ne'

theorem parameterChange_comp (h Q Qm Qr : ℝ) (hQm : 0 < Qm) (p : Parameter) :
    parameterChange h Qm Qr (parameterChange h Q Qm p) = parameterChange h Q Qr p := by
  ext <;> simp only [parameterChange, ← mul_assoc]
  all_goals rw [mul_comm (ratioPower Qm Qr _), ratioPower_comp hQm]

theorem normalWeight_comp {Q Qm Qr K Km Kr : ℝ} (hQm : 0 < Qm) (hKm : Km ≠ 0) :
    normalWeight Q Qm K Km * normalWeight Qm Qr Km Kr = normalWeight Q Qr K Kr := by
  by_cases hK : K = 0
  · simp [normalWeight, hK]
  unfold normalWeight
  calc
    _ = ((Km / K) * (Kr / Km)) *
        (ratioPower Q Qm (1/2) * ratioPower Qm Qr (1/2)) := by ring
    _ = _ := by rw [ratioPower_comp hQm]; field_simp [hKm, hK]

theorem nativeTimeMap_comp (r s : ℝ) (z : Plane) :
    CopySolveCompatibility.nativeTimeMap 0 r (CopySolveCompatibility.nativeTimeMap 0 s z) =
      CopySolveCompatibility.nativeTimeMap 0 (r*s) z := by
  ext <;> simp [CopySolveCompatibility.nativeTimeMap, mul_assoc]

theorem scaledBasis_comp (e : Plane ≃L[ℝ] Plane) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    CommonCoverClass.scaledBasis (CommonCoverClass.scaledBasis e r hr) s hs =
      CommonCoverClass.scaledBasis e (r*s) (mul_ne_zero hr hs) := by
  apply ContinuousLinearEquiv.ext
  funext z
  simp only [CommonCoverClass.scaledBasis_apply, mul_assoc]

theorem transportGeometry_comp (g : Geometry) (k d : ℕ) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    CopySolveCompatibility.transportGeometry
      (CopySolveCompatibility.transportGeometry g k 0 r hr) d 0 s hs =
      CopySolveCompatibility.transportGeometry g (k+d) 0 (r*s) (mul_ne_zero hr hs) := by
  simp only [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.refineGeometry,
    CopySolveCompatibility.timeGeometry, scaledBasis_comp, Nat.add_assoc]
  simp

theorem transportTangent_comp (t : TangentData Parameter ProblemStatement.Space)
    (f g : Parameter → Parameter) (k d : ℕ) (r s a b v w : ℝ) :
    ScaledTangentTransport.transportTangent
      (ScaledTangentTransport.transportTangent t f k 0 r a v) g d 0 s b w =
      ScaledTangentTransport.transportTangent t (fun p => f (g p)) (k+d) 0
        (r*s) (a*b) (v*w) := by
  unfold ScaledTangentTransport.transportTangent
  congr 1 <;> funext z <;>
    simp [nativeTimeMap_comp, CopySolveCompatibility.coverPower_add,
      smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem gap_comp (l : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) :
    ActualParticularStageControls.gap l m + k = ActualParticularStageControls.gap l n := by
  unfold ActualParticularStageControls.gap
  omega

theorem parameters_geometry (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) :
    CopySolveCompatibility.transportGeometry ((ActualParticularStageControls.parameters x
        l).geometry m)
      k 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
        (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne' =
      (ActualParticularStageControls.parameters x l).geometry n := by
  change CopySolveCompatibility.transportGeometry
    (CopySolveCompatibility.transportGeometry (ActualParticularStageControls.reference l).geometry
      (ActualParticularStageControls.gap l m) 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))) _)
    k 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) _ = _
  erw [transportGeometry_comp, gap_comp l n m k hi hm]
  have hr : clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]
    exact ratioPower_comp (ChartScales.Q_pos m) _
  simp only [hr]
  rfl

theorem parameters_length (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m : ℕ) :
    (ActualParticularStageControls.parameters x l).length m /
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      (ActualParticularStageControls.parameters x l).length n := by
  change (_ / clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))) /
    clockWeight h (ChartScales.Q n) (ChartScales.Q m) = _
  rw [div_div, mul_comm]
  change _ / (ratioPower _ _ _ * ratioPower _ _ _) = _
  rw [ratioPower_comp (ChartScales.Q_pos m)]
  rfl

theorem parameters_cutoff (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n m : ℕ) :
    (ActualParticularStageControls.parameters x l).cutoff m ∘
      CopySolveCompatibility.nativeTimeMap 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) =
      (ActualParticularStageControls.parameters x l).cutoff n := by
  funext z
  change (ActualParticularStageControls.reference l).cutoff
    (CopySolveCompatibility.nativeTimeMap 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (CopySolveCompatibility.nativeTimeMap 0 (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
          z)) = _
  rw [nativeTimeMap_comp, mul_comm]
  change (ActualParticularStageControls.reference l).cutoff
    (CopySolveCompatibility.nativeTimeMap 0 (ratioPower _ _ _ * ratioPower _ _ _) z) = _
  rw [ratioPower_comp (ChartScales.Q_pos m)]
  rfl

theorem parameters_tangent (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0) :
    ScaledTangentTransport.transportTangent ((ActualParticularStageControls.parameters x l).tangent
        j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k 0
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q m))
      (normalWeight (ChartScales.Q n) (ChartScales.Q m)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency m)) =
      (ActualParticularStageControls.parameters x l).tangent j n := by
  change ScaledTangentTransport.transportTangent
    (ScaledTangentTransport.transportTangent (ActualParticularStageControls.reference l |>.tangent
        j)
      (parameterChange h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (ActualParticularStageControls.gap l m) 0
      (clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (velocityWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)))
      (normalWeight (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2))
        ((j : ℝ) * (x.coefficients.blocks l).frequency m)
        ((j : ℝ) * (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2)))) _ _ _ _ _ _
            = _
  rw [transportTangent_comp, gap_comp l n m k hi hm]
  have hp := funext (parameterChange_comp h (ChartScales.Q n) (ChartScales.Q m)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) (ChartScales.Q_pos m))
  rw [hp]
  have hr : clockWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]; exact ratioPower_comp (ChartScales.Q_pos m) _
  have ha : velocityWeight h (ChartScales.Q m) (ChartScales.Q (BaseChartJets.cellBand l.2)) *
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) := by
    rw [mul_comm]; exact ratioPower_comp (ChartScales.Q_pos m) _
  rw [hr, ha, mul_comm (normalWeight _ _ _ _), normalWeight_comp (ChartScales.Q_pos m) hKm]
  rfl

/-- Actual source transport on the two-band overlap.  All fast variables
remain free, and all excluded residual terms are retained. -/
theorem source_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (p : Parameter) (hp : p.2 ∈ V) (Y : Plane) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
      (ActualParticularStageControls.assembly x l).aliasInput j n (p,Y) =
    ScaledTangentTransport.transportSource
      (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
        (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly
            x l).carrierBlock
        (ActualParticularStageControls.assembly x l).gaussianInput
        (ActualParticularStageControls.assembly x l).aliasInput j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m))
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q m)) (p,Y) := by
  have he := HS.source (ActualInitialCoherence.context_band B htime n m k hi)
    (PhysicalMeanDomain.slowDomain_open hV) (GaugeStateCoherence.bandScale_pos n m).ne'
      HB j (x := CorrectionStep.cycleAssoc.symm (p,Y)) hp
  rw [ActualReferenceRebase.state_sourceWeight] at he
  rw [ActualReferenceRebase.assembly_source]
  change _ = (clockWeight _ _ _ * velocityWeight _ _ _) • _
  rw [clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos m),
    ActualReferenceRebase.assembly_source]
  simpa only [← ActualReferenceRebase.associatedChart_stateChart,
    PhysicalResidualNaturality.associatedChart_apply] using he

/-! ## The global linear map and its actual spatial directions -/

/-- Absolute map, given by
`ActualParticularStageControls.nativeToFull.toContinuousLinearEquiv.trans
(ActualPrimaryCoherence.absoluteChart n)`. -/
noncomputable def absoluteMap (n : ℕ) : WaveSpace ≃L[ℝ] ActualPrimaryCoherence.Absolute :=
  ActualParticularStageControls.nativeToFull.toContinuousLinearEquiv.trans
    (ActualPrimaryCoherence.absoluteChart n)

/-- Band map, given by `(absoluteMap n).trans (absoluteMap m).symm`. -/
noncomputable def bandMap (n m : ℕ) : WaveSpace ≃L[ℝ] WaveSpace :=
  (absoluteMap n).trans (absoluteMap m).symm

theorem absoluteMap_band (n m : ℕ) (z : WaveSpace) :
    absoluteMap m (bandMap n m z) = absoluteMap n z :=
  (absoluteMap m).apply_symm_apply _

theorem bandMap_apply (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (z : WaveSpace) :
    bandMap n m z = ((parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,z.1.2),
      coverPower k z.2) := by
  apply (absoluteMap m).injective
  rw [absoluteMap_band]
  change (ActualPrimaryCoherence.absoluteChart n) (ActualParticularStageControls.nativeToFull z) =
    (ActualPrimaryCoherence.absoluteChart m) _
  rw [ActualPrimaryCoherence.absoluteChart_apply, ActualPrimaryCoherence.absoluteChart_apply]
  apply Prod.ext
  · symm
    change toAbsolute m (CorrectionStep.cycleAssoc.symm
      (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m)
        k (z.1.1,z.2))) = _
    rw [ActualReferenceRebase.associatedChart_stateChart]
    exact ActualPrimaryCoherence.toAbsolute_bandChart n m k hi _
  · rfl

theorem absoluteMap_radius (n : ℕ) (z : WaveSpace) :
    ActualPrimaryCoherence.absoluteRadius (absoluteMap n z) =
      Real.sqrt (ChartScales.Q n) * z.1.1.1 :=
  ActualPrimaryCoherence.absoluteChart_radius n (ActualParticularStageControls.nativeToFull z)

theorem absoluteMap_radial (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).radialField n z) =
      Real.sqrt (ChartScales.Q n) • ActualPrimaryCoherence.absoluteRadial (absoluteMap n z) := by
  simp only [absoluteMap, ActualParticularStageControls.directions,
    ParticularWaveBounds.reindex_radialField, ParticularWaveBounds.reindexVector,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_radial B n _

theorem absoluteMap_fast (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).fastField n z) =
      ChartScales.Q n ^ (1+h) • ActualPrimaryCoherence.absoluteFast (absoluteMap n z) := by
  simp only [absoluteMap, ActualParticularStageControls.directions,
    ParticularWaveBounds.reindex_fastField, ParticularWaveBounds.reindexVector,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_fast B n _

theorem between_direction {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e f : E ≃L[ℝ] F) (a b : ℝ) (hb : b ≠ 0) (U V : E → E) (W : F → F)
    (he : ∀ z, e (U z) = a • W (e z)) (hf : ∀ z, f (V z) = b • W (f z)) (z : E) :
    (e.trans f.symm) (U z) = (a/b) • V ((e.trans f.symm) z) := by
  apply f.injective
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    map_smul, hf, he, smul_smul, div_mul_cancel₀ _ hb]

theorem bandMap_fast (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).fastField n z) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualParticularStageControls.directions (B := B)).fastField m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.rpow_pos_of_pos (ChartScales.Q_pos m) (1+h)).ne' _ _ _
    (absoluteMap_fast B n) (absoluteMap_fast B m) z
  change _ = (ChartScales.Q n ^ (1+h) / ChartScales.Q m ^ (1+h)) • _ at he
  simp only [clockWeight, ratioPower, CoordinateAlgebra.A,
    show (1/2 : ℝ) + h + 1/2 = 1+h by ring] at he ⊢
  exact he

theorem absoluteMap_axial (B n : ℕ) (z : WaveSpace) :
    absoluteMap n ((ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip) n z) =
      Real.sqrt (ChartScales.Q n) • ActualPrimaryCoherence.absoluteAxial (absoluteMap n z) := by
  change (ActualPrimaryCoherence.absoluteChart n)
    (ActualParticularStageControls.nativeToFull
      (ActualParticularStageControls.nativeToFull.symm
        ((PrimaryResidualClass.directions (commonContext B)).axialField
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
              standardRegion)) n
          (ActualParticularStageControls.nativeToFull z)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_axial B n standardRegion _

theorem absoluteMap_angular (B n : ℕ) (z : WaveSpace) :
    absoluteMap n (ActualParticularStageControls.directions (B := B)).angular =
      ActualPrimaryCoherence.absoluteAngular (absoluteMap n z) := by
  change (ActualPrimaryCoherence.absoluteChart n)
    (ActualParticularStageControls.nativeToFull
      (ActualParticularStageControls.nativeToFull.symm
        (PrimaryResidualClass.directions (commonContext B)).angular)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ActualPrimaryCoherence.absoluteChart_angular B n _

theorem bandMap_radial (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).radialField n z) =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) •
        (ActualParticularStageControls.directions (B := B)).radialField m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne' _ _ _
    (absoluteMap_radial B n) (absoluteMap_radial B m) z
  simp only [Real.sqrt_eq_rpow, ratioPower] at he ⊢
  exact he

theorem bandMap_axial (B n m : ℕ) (z : WaveSpace) :
    bandMap n m ((ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip) n z) =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) •
        (ActualParticularStageControls.directions (B := B)).axialField
          (CorrectionStep.ParticularParameters.nativeStrip
              ActualParticularStageControls.associatedStrip)
            m (bandMap n m z) := by
  have he := between_direction (absoluteMap n) (absoluteMap m) _ _
    (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne' _ _ _
    (absoluteMap_axial B n) (absoluteMap_axial B m) z
  simp only [Real.sqrt_eq_rpow, ratioPower] at he ⊢
  exact he

theorem bandMap_angular (B n m : ℕ) (z : WaveSpace) :
    bandMap n m (ActualParticularStageControls.directions (B := B)).angular =
      (ActualParticularStageControls.directions (B := B)).angular := by
  have he := between_direction (absoluteMap n) (absoluteMap m) 1 1 one_ne_zero
    (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
    (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
    ActualPrimaryCoherence.absoluteAngular
    (by simpa only [one_smul] using absoluteMap_angular B n)
    (by simpa only [one_smul] using absoluteMap_angular B m) z
  simp only [div_self one_ne_zero, one_smul] at he
  exact he

theorem bandMap_radius (n m : ℕ) (z : WaveSpace) :
    (bandMap n m z).1.1.1 =
      ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) * z.1.1.1 := by
  have he := absoluteMap_radius m (bandMap n m z)
  rw [absoluteMap_band, absoluteMap_radius] at he
  have hm := (Real.sqrt_pos.mpr (ChartScales.Q_pos m)).ne'
  calc
    _ = (Real.sqrt (ChartScales.Q n) * z.1.1.1) / Real.sqrt (ChartScales.Q m) :=
      (eq_div_iff hm).2 (by simpa only [mul_comm] using he.symm)
    _ = _ := by
      unfold ratioPower
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      ring

theorem reference_cutoff_smooth (l : Label B N0) :
    ContDiff ℝ ∞ (ActualParticularStageControls.reference l).cutoff := by
  change ContDiff ℝ ∞ (fun z : Plane =>
    (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff _ z.2)
  exact (clockWindow l.2).cutoff_contDiff.mul
    ((GaussianTailFlat.slotCutoff_contDiff _).comp contDiff_snd)

theorem reference_cutoff_support (l : Label B N0) :
    support (ActualParticularStageControls.reference l).cutoff ⊆
      univ ×ˢ Icc 0 (ActualParticularStageControls.reference l).length := by
  classical
  intro z hz
  refine ⟨mem_univ _, ?_⟩
  have hL := (ActualParticularStageControls.reference l).length_pos
  have hs : GaussianTailFlat.slotCutoff (ActualParticularStageControls.reference l).length z.2 ≠ 0
      := by
    intro he
    apply hz
    change (clockWindow l.2).cutoff z * GaussianTailFlat.slotCutoff _ z.2 = 0
    exact (congrArg ((clockWindow l.2).cutoff z * ·) he).trans (mul_zero _)
  constructor
  · by_contra hlt
    apply hs
    apply GaussianTailFlat.slotCutoff_zero hL
    rw [abs_of_neg (by linarith : z.2 - (ActualParticularStageControls.reference l).length/2 < 0)]
    linarith
  · by_contra hgt
    apply hs
    apply GaussianTailFlat.slotCutoff_zero hL
    rw [abs_of_pos (by linarith : 0 < z.2 - (ActualParticularStageControls.reference l).length/2)]
    linarith

theorem parameter_cutoff_smooth (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    ContDiff ℝ ∞ ((ActualParticularStageControls.parameters x l).cutoff n) := by
  apply (reference_cutoff_smooth l).comp
  exact contDiff_fst.prodMk (contDiff_const.add (contDiff_const.mul contDiff_snd))

theorem parameter_cutoff_support (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (n : ℕ) :
    support ((ActualParticularStageControls.parameters x l).cutoff n) ⊆
      univ ×ˢ Icc 0 ((ActualParticularStageControls.parameters x l).length n) := by
  intro z hz
  have hb := (reference_cutoff_support l hz).2
  have hr : 0 < clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) :=
    ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) _
  change 0 ≤ 0 + clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) * z.2
      ∧
    0 + clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) * z.2 ≤ _ at hb
  refine ⟨mem_univ _, ?_, ?_⟩
  · exact nonneg_of_mul_nonneg_right (by simpa using hb.1) hr
  · apply (le_div_iff₀ hr).2
    have hh := hb.2
    simp only [zero_add, mul_comm] at hh ⊢
    exact hh

/-- Source, constructed using `ParticularWaveAssembly.residualSource`. -/
noncomputable def source (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) : Parameter × Plane → ComplexVector :=
  ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
    (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
        l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j n

/-- Only finite path continuity of the actual input equation is required.
There is no continuation in the clock variable in this record. -/
structure PathRegular (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (Y : Plane) (copy : Frequency) : Prop where
  coefficient : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
      =>
    ((ActualParticularStageControls.parameters x l).tangent j n).linearData.coefficientAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))
  realForcing : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
      =>
    (ParticularWaveBounds.realData ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n)).linearData.forcingAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))
  imagForcing : Continuous (fun s : Icc 0 ((ActualParticularStageControls.parameters x l).length n)
      =>
    (ParticularWaveBounds.imagData ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n)).linearData.forcingAlong
      ((ActualParticularStageControls.parameters x l).geometry n) copy ((p,Y),s))

section CopyComparison

variable (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
  {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
  (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
  (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
  (HS : ActualReferenceRebase.StateComparison x V n m k)
  (HB : ActualReferenceRebase.BlockComparison x l V n m k)
  (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
  (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
  (p : Parameter) (hp : p.2 ∈ V) (Y : Plane)

include hV htime hi hm HS HB hKn hKm hp in
theorem copy_amplitude_band (copy : Frequency)
    (H : PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy)
    (hslot : (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length n)) :
    ParticularWaveBounds.complexCopyVelocity ((ActualParticularStageControls.parameters x
        l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le copy (p,Y) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.complexCopyVelocity ((ActualParticularStageControls.parameters x
            l).tangent j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le copy
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
        l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have hz : ((CopySolveCompatibility.transportGeometry
      ((ActualParticularStageControls.parameters x l).geometry m) k 0 r hr.ne').coordinates copy
          Y).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length m / r) := by
    simpa only [r, parameters_geometry x l n m k hi hm, parameters_length x l n m] using hslot
  have he := IntervalCopyTransport.complexCopyVelocity_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn p copy Y
    H.coefficient H.realForcing H.imagForcing hz
  have hs := ActualReferenceRebase.copyVelocity_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le p
    (source_band x l hV htime n m k hi HS HB j p hp) copy Y
  apply hs.trans
  dsimp only [r, c, s] at he
  simp only [parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm] at he
  refine Eq.trans ?_ he
  exact GaussianErrorNaturality.interval_congr
    (fun a b hab => ParticularWaveBounds.complexCopyVelocity _ _ _ hab copy (p,Y))
    _ _ rfl (parameters_length x l n m).symm

include hV htime hi hm HS HB hKn hKm hp in
theorem common_amplitude_band
    (H : ∀ copy, PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy) :
    ParticularWaveBounds.commonVelocity ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le
      ((ActualParticularStageControls.parameters x l).cutoff n) (p,Y) =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.commonVelocity ((ActualParticularStageControls.parameters x l).tangent
            j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le
          ((ActualParticularStageControls.parameters x l).cutoff m)
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
        l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have he := IntervalCopyTransport.commonVelocity_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn
    ((ActualParticularStageControls.parameters x l).cutoff m) (parameter_cutoff_support x l m) p Y
    (fun copy _ => (H copy).coefficient) (fun copy _ => (H copy).realForcing)
    (fun copy _ => (H copy).imagForcing)
  have hs := ActualReferenceRebase.commonVelocity_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le
    ((ActualParticularStageControls.parameters x l).cutoff n) p
    (source_band x l hV htime n m k hi HS HB j p hp) Y
  apply hs.trans
  dsimp only [r, c, s] at he
  simp only [parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm, parameters_cutoff x l n m] at he
  refine Eq.trans ?_ he
  exact GaussianErrorNaturality.interval_congr
    (fun a b hab => ParticularWaveBounds.commonVelocity _ _ _ hab _ (p,Y))
    _ _ rfl (parameters_length x l n m).symm

include hV htime hi hm HS HB hKn hKm hp in
theorem common_pressure_band
    (H : ∀ copy, PathRegular x l j m (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p)
      (coverPower k Y) copy) :
    ParticularWaveBounds.commonPressure ((ActualParticularStageControls.parameters x l).tangent j n)
      (source x l j n) ((ActualParticularStageControls.parameters x l).geometry n)
      ((ActualParticularStageControls.parameters x l).length_pos n).le
      ((ActualParticularStageControls.parameters x l).cutoff n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) (p,Y) =
      pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        ParticularWaveBounds.commonPressure ((ActualParticularStageControls.parameters x l).tangent
            j m)
          (source x l j m) ((ActualParticularStageControls.parameters x l).geometry m)
          ((ActualParticularStageControls.parameters x l).length_pos m).le
          ((ActualParticularStageControls.parameters x l).cutoff m)
          ((j : ℝ) * (x.coefficients.blocks l).frequency m)
          (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p,coverPower k Y) := by
  let r := clockWeight h (ChartScales.Q n) (ChartScales.Q m)
  let c := velocityWeight h (ChartScales.Q n) (ChartScales.Q m)
  let s := normalWeight (ChartScales.Q n) (ChartScales.Q m)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) ((j : ℝ) * (x.coefficients.blocks
        l).frequency m)
  have hr : 0 < r := ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _
  have hsn : s ≠ 0 := normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm
  have he := IntervalCopyTransport.commonPressure_zeroEntry
    ((ActualParticularStageControls.parameters x l).tangent j m) (source x l j m)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualParticularStageControls.parameters x l).geometry m) k
    ((ActualParticularStageControls.parameters x l).length m) r c s
    ((j : ℝ) * (x.coefficients.blocks l).frequency m) ((j : ℝ) * (x.coefficients.blocks
        l).frequency n)
    ((ActualParticularStageControls.parameters x l).length_pos m) hr hsn hKm hKn
    ((ActualParticularStageControls.parameters x l).cutoff m) (parameter_cutoff_support x l m) p Y
    (fun copy _ => (H copy).coefficient) (fun copy _ => (H copy).realForcing)
    (fun copy _ => (H copy).imagForcing)
  dsimp only [r, c, s] at he
  rw [pressure_scaling (ChartScales.Q_pos n) (ChartScales.Q_pos m) hKn hKm] at he
  have hs := ActualReferenceRebase.commonPressure_source_congr
    ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
    (ScaledTangentTransport.transportSource (source x l j m)
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m)) k r c)
    ((ActualParticularStageControls.parameters x l).geometry n)
    ((ActualParticularStageControls.parameters x l).length_pos n).le
    ((ActualParticularStageControls.parameters x l).cutoff n)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) p
    (source_band x l hV htime n m k hi HS HB j p hp) Y
  exact hs.trans (by simpa only [r, c, parameters_tangent x l j n m k hi hm hKm,
    parameters_geometry x l n m k hi hm, parameters_length x l n m, parameters_cutoff x l n m]
        using he)

end CopyComparison

theorem copy_cutoff_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (copy : Frequency) :
    (copyData x l j).cutoff n copy = fun z => (copyData x l j).cutoff m copy (bandMap n m z) := by
  funext z
  rw [bandMap_apply n m k hi]
  change (ActualParticularStageControls.parameters x l).cutoff n
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy z.2) =
    (ActualParticularStageControls.parameters x l).cutoff m
      (((ActualParticularStageControls.parameters x l).geometry m).coordinates copy (coverPower k
          z.2))
  rw [← parameters_geometry x l n m k hi hm, ← parameters_cutoff x l n m]
  exact congrArg ((ActualParticularStageControls.parameters x l).cutoff m)
    (ScaledTangentTransport.coordinates_transport _ k 0 _ _ copy z.2)

theorem copy_cutoff_smooth (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (copy : Frequency) :
    ContDiff ℝ ∞ ((copyData x l j).cutoff n copy) :=
  ((parameter_cutoff_smooth x l n).comp
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates_contDiff copy)).comp
        contDiff_snd

theorem copy_derivative_slot (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (copy : Frequency) {z : WaveSpace}
    (hz : (ActualParticularStageControls.directions (B := B)).Dfast
      (fun n => (copyData x l j).cutoff n copy) n z ≠ 0) :
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy z.2).2 ∈
      Icc 0 ((ActualParticularStageControls.parameters x l).length n) := by
  apply GaussianErrorNaturality.along_ne_zero_mem_closed
    (isClosed_Icc.preimage
      ((((ActualParticularStageControls.parameters x l).geometry n).coordinates_contDiff
          copy).continuous.comp
        continuous_snd).snd) _
    ((ActualParticularStageControls.directions (B := B)).fastField n) hz
  intro y hy
  exact (parameter_cutoff_support x l n hy).2

theorem gaussian_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) n z =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B))
          m (bandMap n m z) := by
  rw [← clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  apply GaussianErrorNaturality.globalGaussian_transport (bandMap n m).toContinuousLinearMap
    (ActualParticularStageControls.directions (B := B)) (ActualParticularStageControls.directions
        (B := B))
    (copyData x l j) (copyData x l j) n m
  · exact copy_cutoff_band x l j n m k hi hm
  · exact bandMap_fast B n m z
  · intro copy
    exact (copy_cutoff_smooth x l j m copy).contDiffAt.differentiableAt (by simp)
  · intro copy hne
    have hd := GaussianErrorNaturality.fast_cutoff_transport (bandMap n m).toContinuousLinearMap
      (ActualParticularStageControls.directions (B := B)) (ActualParticularStageControls.directions
          (B := B))
      (copyData x l j) (copyData x l j) n m
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m)) copy z
      (copy_cutoff_band x l j n m k hi hm copy) (bandMap_fast B n m z)
      ((copy_cutoff_smooth x l j m copy).contDiffAt.differentiableAt (by simp))
    have hdn : (ActualParticularStageControls.directions (B := B)).Dfast
        (fun n => (copyData x l j).cutoff n copy) n z ≠ 0 := by
      rw [hd]
      exact mul_ne_zero (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne' hne
    have hs := copy_derivative_slot x l j n copy hdn
    change (copyData x l j).amplitude n copy z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (copyData x l j).amplitude m copy (bandMap n m z)
    rw [bandMap_apply n m k hi]
    simp only [copyData, GaussianErrorNaturality.copyData_amplitude]
    exact copy_amplitude_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 copy (H copy) hs
  · change (copyData x l j).source n z =
      (clockWeight h (ChartScales.Q n) (ChartScales.Q m) *
        velocityWeight h (ChartScales.Q n) (ChartScales.Q m)) •
        (copyData x l j).source m (bandMap n m z)
    rw [bandMap_apply n m k hi]
    exact source_band x l hV htime n m k hi HS HB j z.1.1 hz z.2

/-! ## Actual finite-path inputs and zero source fibers -/

/-- Source inputs data, collecting `continuous`, `supported`, `ordered`. -/
structure SourceInputs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0) : Prop where
  continuous : ∀ j n p, p.2 ∈ standardRegion.carrier →
    Continuous (fun Y : Plane => source x l j n (p,Y))
  supported : ∀ j n p, p.2 ∈ standardRegion.carrier → ∀ Y,
    source x l j n (p,Y) ≠ 0 →
      (p.1,(p.2,Y)) ∈ ActualCoreSupport.refinedCarrier (l.2,l.1) n
  ordered : ∀ j n p, p.2 ∈ standardRegion.carrier → ∀ Y,
    source x l j n (p,Y) ≠ 0 →
      CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)

theorem SourceInputs.pathRegular {x : CorrectionStep.CycleState (Label B N0)} {l : Label B N0}
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    (j : ℤ) (hj : j ≠ 0) (n : ℕ) (p : Parameter) (hp : p.2 ∈ standardRegion.carrier)
    (hne : ∃ Y, source x l j n (p, Y) ≠ 0) (Y : Plane) (copy : Frequency) :
    PathRegular x l j n p Y copy := by
  have hs : ∃ Z : Plane, (p.1,(p.2,Z)) ∈ ActualCoreSupport.refinedCarrier (l.2,l.1) n := by
    obtain ⟨Z,hZ⟩ := hne
    exact ⟨Z,I.supported j n p hp Z hZ⟩
  have ha := ActualCopySliceRegularity.actual_copy_slices_of_refinedFiber x l hfrequency j hj n p
    (standardRegion.time_pos p.2 hp) hs Y copy
  let G : Geometry := (ActualParticularStageControls.parameters x l).geometry n
  let L : ℝ := (ActualParticularStageControls.parameters x l).length n
  have ht : Continuous (fun s : Icc (0 : ℝ) L => (Y,(s : ℝ))) :=
    continuous_const.prodMk continuous_subtype_val
  have hpath := (G.path_contDiff copy).continuous.comp ht
  have hf := (I.continuous j n p hp).comp hpath
  dsimp only [Function.comp_def] at hf
  exact ⟨ha.1, IntervalCopyTransport.real_forcingAlong_continuous _ _ _ _ _ _ ha.2 hf,
    IntervalCopyTransport.imag_forcingAlong_continuous _ _ _ _ _ _ ha.2 hf⟩

theorem copy_amplitude_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p, Y) = 0)
    (theta : ℝ) (Y : Plane) (copy : Frequency) :
    (copyData x l j).amplitude n copy ((p,theta),Y) = 0 := by
  rw [copyData, GaussianErrorNaturality.copyData_amplitude]
  exact ParticularWaveBounds.complexCopyVelocity_zero_of_path _ _ _ _ copy p Y (fun _ _ => hz _)

theorem raw_amplitude_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p, Y) = 0)
    (theta : ℝ) (Y : Plane) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n ((p,theta),Y) = 0 := by
  change (∑' copy, (copyData x l j).cutoff n copy ((p,theta),Y) •
    (copyData x l j).amplitude n copy ((p,theta),Y)) = 0
  simp only [copy_amplitude_zero x l j n p hz, smul_zero, tsum_zero]

theorem raw_pressure_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (p : Parameter) (hz : ∀ Y, source x l j n (p, Y) = 0) (theta : ℝ) (Y : Plane) :
    (ActualReferenceRebase.actualCoefficients x l j).pressure n ((p,theta),Y) = 0 := by
  rw [ActualReferenceRebase.actualCoefficients, CorrectionStep.ParticularParameters.common_pressure
    _ _ _ _ _ _ _ _ hKn]
  change (∑' copy, ((ActualParticularStageControls.parameters x l).cutoff n
    (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y) : ℂ) *
      ParticularWaveBounds.complexCopyPressure _ _ _ _ copy _ (p,Y)) = 0
  trans ∑' _ : Frequency, (0 : ℂ)
  · apply tsum_congr
    intro copy
    by_cases hc : (ActualParticularStageControls.parameters x l).cutoff n
        (((ActualParticularStageControls.parameters x l).geometry n).coordinates copy Y) = 0
    · simp only [hc, Complex.ofReal_zero, zero_mul]
    · change (_ : ℂ) * ParticularWaveBounds.complexCopyPressure
        ((ActualParticularStageControls.parameters x l).tangent j n) (source x l j n)
        ((ActualParticularStageControls.parameters x l).geometry n)
        ((ActualParticularStageControls.parameters x l).length_pos n).le copy
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) (p,Y) = 0
      rw [ParticularWaveBounds.complexCopyPressure_zero_of_path _ _ _ _ copy _ p Y
        (fun _ _ => hz _) (parameter_cutoff_support x l n hc).2, mul_zero]
  · exact tsum_zero

theorem gaussian_zero (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n : ℕ) (p : Parameter) (hz : ∀ Y, source x l j n (p, Y) = 0)
    (theta : ℝ) (Y : Plane) :
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B))
      n ((p,theta),Y) = 0 := by
  have hs : (copyData x l j).source n ((p,theta),Y) = 0 := hz Y
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, PeriodizedWaveBounds.CopyData.globalTail,
    PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail, copy_amplitude_zero x l
        j n p hz,
    smul_zero, tsum_zero, hs, add_zero]

theorem raw_amplitude_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m z) := by
  rw [bandMap_apply n m k hi, ActualReferenceRebase.actualCoefficients,
    CorrectionStep.ParticularParameters.common_amplitude,
    CorrectionStep.ParticularParameters.common_amplitude]
  exact common_amplitude_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 H

theorem raw_pressure_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hm : CommonWindow.index h m ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0)
    (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (H : ∀ copy, PathRegular x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1) (coverPower k z.2) copy) :
    (ActualReferenceRebase.actualCoefficients x l j).pressure n z =
      pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).pressure m (bandMap n m z) := by
  rw [bandMap_apply n m k hi, ActualReferenceRebase.actualCoefficients,
    CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hKn,
    CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hKm]
  exact common_pressure_band x l hV htime n m k hi hm HS HB j hKn hKm z.1.1 hz z.2 H

/-- All three raw output identities are derived from the current source.
A zero source fiber needs no ODE regularity or ordering premise. -/
theorem raw_outputs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z.1.1.2 ∈ V)
    (hmap : (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1).2 ∈
        standardRegion.carrier) :
    (ActualReferenceRebase.actualCoefficients x l j).amplitude n z =
        velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m z) ∧
    (ActualReferenceRebase.actualCoefficients x l j).pressure n z =
        pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (ActualReferenceRebase.actualCoefficients x l j).pressure m (bandMap n m z) ∧
    (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) n z =
        sourceWeight h (ChartScales.Q n) (ChartScales.Q m) •
          (copyData x l j).globalGaussian (ActualParticularStageControls.directions (B := B)) m
              (bandMap n m z) := by
  classical
  have hk (a : ℕ) : (j : ℝ) * (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact mul_ne_zero (by
        exact_mod_cast hj) (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h a)).ne'
  by_cases hne : ∃ Y, source x l j m
      (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,Y) ≠ 0
  · have hm := let ⟨Y,hY⟩ := hne; I.ordered j m _ hmap Y hY
    have H := I.pathRegular hfrequency j hj m _ hmap hne
    exact ⟨raw_amplitude_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _),
      raw_pressure_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _),
      gaussian_band x l hV htime n m k hi hm HS HB j (hk n) (hk m) z hz (H _)⟩
  · have hm : ∀ Y, source x l j m
        (parameterChange h (ChartScales.Q n) (ChartScales.Q m) z.1.1,Y) = 0 := by
      simpa only [not_exists, not_not] using hne
    have hn : ∀ Y, source x l j n (z.1.1,Y) = 0 := by
      intro Y
      rw [show source x l j n (z.1.1,Y) = _ from source_band x l hV htime n m k hi HS HB j _ hz Y]
      change (_ : ℝ) • source x l j m (_,_) = 0
      rw [hm, smul_zero]
    rw [bandMap_apply n m k hi]
    simp only [raw_amplitude_zero x l j n z.1.1 hn, raw_amplitude_zero x l j m _ hm,
      raw_pressure_zero x l j n (hk n) z.1.1 hn, raw_pressure_zero x l j m (hk m) _ hm,
      gaussian_zero x l j n z.1.1 hn, gaussian_zero x l j m _ hm, smul_zero, and_self]

/-- Wave domain, given by `{z | z.1.1.2 ∈ V}`. -/
noncomputable def waveDomain (V : Set Plane) : Set WaveSpace := {z | z.1.1.2 ∈ V}

theorem waveDomain_open {V : Set Plane} (hV : IsOpen V) : IsOpen (waveDomain V) :=
  hV.preimage continuous_fst.fst.snd

theorem parameterChange_slow (n m : ℕ) (p : Parameter) :
    (parameterChange h (ChartScales.Q n) (ChartScales.Q m) p).2 =
      GaugeStateCoherence.bandSlowEquiv h n m p.2 :=
  congrArg (fun z : CorrectionStep.CyclePoint => z.2.1)
    (ActualReferenceRebase.associatedChart_stateChart n m 0 (p,0))

theorem phase_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    {V : Set Plane} (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k) (j : ℤ) (hj : j ≠ 0)
    (hn : (x.coefficients.blocks l).frequency n ≠ 0) (hm : (x.coefficients.blocks l).frequency m ≠
        0)
    (z : WaveSpace) (hz : z ∈ waveDomain V) :
    (ActualReferenceRebase.actualCoefficients x l j).phase n z =
      (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m (bandMap n m z) := by
  have hp := HB.phase (x := CorrectionStep.cycleAssoc.symm (z.1.1,z.2)) hz
  dsimp only at hp
  rw [← ActualReferenceRebase.associatedChart_stateChart,
    PhysicalResidualNaturality.associatedChart_apply] at hp
  rw [bandMap_apply n m k hi]
  change (x.coefficients.blocks l).phase n (CorrectionStep.cycleAssoc.symm (z.1.1,z.2)) +
      ((x.coefficients.blocks l).angularFrequency n : ℝ) /
        (x.coefficients.blocks l).frequency n * z.1.2 = _
  rw [HB.angular]
  exact (ActualReferenceRebase.carrier_phase_rebase hn hm (by exact_mod_cast hj) hp).symm

theorem corrected_amplitude_of_germs (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (n m : ℕ) (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0) (z : WaveSpace)
    (ha : (ActualReferenceRebase.actualCoefficients x l j).amplitude n =ᶠ[𝓝 z]
      fun y => velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m y))
    (hp : (ActualReferenceRebase.actualCoefficients x l j).phase n =ᶠ[𝓝 z]
      fun y => (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m (bandMap n m y)) :
    (corrected x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (corrected x l j).amplitude m (bandMap n m z) := by
  let d := ActualParticularStageControls.directions (B := B)
  let s := CorrectionStep.ParticularParameters.nativeStrip
      ActualParticularStageControls.associatedStrip
  have h1 := ParticularWaveAssembly.realizedCoefficient_germ ha
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
  have h2 := ActualParticularRealization.realizedCoefficient_phase_germ hp
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (fun y => velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
      (ActualReferenceRebase.actualCoefficients x l j).amplitude m (bandMap n m y))
  change CurlClassBounds.realizedCoefficient ((j : ℝ) * (x.coefficients.blocks l).frequency n)
    (fun y : WaveSpace => y.1.1.1) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude n) z = _
  rw [(h1.trans h2).eq_of_nhds]
  exact ActualPrimaryCoherence.realizedCoefficient_equiv (bandMap n m)
    (L := (j : ℝ) * (x.coefficients.blocks l).frequency m)
    (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne'
    (div_ne_zero hKm hKn) hKn (by field_simp [hKn, (mul_ne_zero_iff.mp hKn).2])
    (fun y => y.1.1.1) (fun y => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.radialField m) (fun _ => d.angular) (d.axialField s m)
    (bandMap_radius n m) (bandMap_radial B n m) (bandMap_angular B n m) (bandMap_axial B n m)
    (velocityWeight h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualReferenceRebase.actualCoefficients x l j).phase m)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude m) z

theorem corrected_amplitude_on (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ waveDomain V) :
    (corrected x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (corrected x l j).amplitude m (bandMap n m z) := by
  have hf (a : ℕ) : (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h a)).ne'
  apply corrected_amplitude_of_germs x l j n m
    (mul_ne_zero (by exact_mod_cast hj) (hf n)) (mul_ne_zero (by exact_mod_cast hj) (hf m)) z
  · filter_upwards [(waveDomain_open hV).mem_nhds hz] with y hy
    exact (raw_outputs x l I hfrequency hV htime n m k hi HS HB j hj y hy
      (by rw [parameterChange_slow]; exact hmap hy)).1
  · filter_upwards [(waveDomain_open hV).mem_nhds hz] with y hy
    exact phase_band x l n m k hi HB j hj (hf n) (hf m) y hy

end NavierStokes.ActualParticularCoherence
