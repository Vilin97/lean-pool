/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopySolveCompatibility
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling

/-!
# Normal and clock transport of the actual tangent inverse

The native clock, its zero-entry anchor, the normal and the source are
transported together.  Velocity and pressure below are outputs of the
actual copy-path Volterra inverse, with no output compatibility hypothesis.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ScaledTangentTransport

open Set Function CommonCoverSolve TorusInverse ParticularWaveBounds HarmonicCalculus
open scoped Topology ContDiff InnerProductSpace


section Geometry

theorem coordinates_transport (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) (copy : Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap shift rate
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y) =
        g.coordinates copy (coverPower gap Y) := by
  rw [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.coordinates_refine,
      CopySolveCompatibility.coordinates_timeGeometry]

theorem path_transport (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) (copy : Frequency) (Y : Plane) (t : ℝ) :
    coverPower gap ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).path copy Y
        t) =
      g.path copy (coverPower gap Y) (shift + rate * t) := by
  rw [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.path_refine,
      CopySolveCompatibility.path_timeGeometry]

theorem slotDirection_transport (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) :
    coverPower gap (slotDirection (CopySolveCompatibility.transportGeometry g gap shift rate
        hrate)) =
      rate • slotDirection g := by
  apply (coverPower g.gap).injective
  change coverPower g.gap
      (coverPower gap ((coverPower (g.gap + gap)).symm
        ((CommonCoverClass.scaledBasis g.basis rate hrate) (0, 1)))) = _
  rw [← CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply,
    CommonCoverClass.scaledBasis_transverse]
  simp only [slotDirection, map_smul, ContinuousLinearEquiv.apply_symm_apply]

theorem current_slot_iff (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : 0 < rate) (copy : Frequency) (Y : Plane) (a b : ℝ) :
    ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈
        Icc a b ↔
      (g.coordinates copy (coverPower gap Y)).2 ∈
        Icc (shift + rate * a) (shift + rate * b) := by
  have he := congrArg Prod.snd (coordinates_transport g gap shift rate hrate.ne' copy Y)
  change shift + rate * _ = _ at he
  rw [← he]
  constructor
  · intro h
    exact ⟨CopySolveCompatibility.time_interval_mono shift hrate h.1,
      CopySolveCompatibility.time_interval_mono shift hrate h.2⟩
  · intro h
    constructor <;> nlinarith [h.1, h.2]

/-- A compact reference cutoff still has only finitely many active
transported copies, uniformly on each common-coordinate ball. -/
theorem finite_transported_copy_cutoffs (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) {cutoff : Plane → ℝ} (hcutoff : HasCompactSupport cutoff) (R : ℝ) :
    ∃ I : Finset Frequency, ∀ Y : Plane, ‖Y‖ ≤ R → ∀ copy : Frequency, copy ∉ I →
      (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate)
        ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y) = 0
            := by
  obtain ⟨I, hI⟩ := g.finite_copy_cutoffs hcutoff ((6 : ℝ) ^ gap * R)
  refine ⟨I, ?_⟩
  intro Y hY copy hcopy
  simp only [Function.comp_apply, coordinates_transport]
  exact hI (coverPower gap Y) ((norm_coverPower_le gap Y).trans
    (mul_le_mul_of_nonneg_left hY (by positivity))) copy hcopy

end Geometry

section Inputs

variable {P Q H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The velocity scale is `amplitude`.  The actual source scale is
`rate * amplitude`, and the moving normal acquires both normal and clock
scales in its slot derivative. -/
noncomputable def transportTangent (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) : TangentData Q H where
  normal z := normalScale • t.normal (parameter z.1, CopySolveCompatibility.nativeTimeMap shift
      rate z.2)
  normalDot z := (normalScale * rate) •
    t.normalDot (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  action z := rate • t.action (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  damping z := rate * t.damping (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  source z := (rate * amplitude) • t.source (parameter z.1, coverPower gap z.2)

/-- The ambient complex source undergoes the same rate and velocity
scalings as the real tangent source. -/
noncomputable def transportSource (f : P × Plane → ComplexVector) (parameter : Q → P)
    (gap : ℕ) (rate amplitude : ℝ) : Q × Plane → ComplexVector :=
  fun z => (rate * amplitude) • f (parameter z.1, coverPower gap z.2)

theorem normal_slot_derivative (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) (q : Q) (xi eta : ℝ)
    (hn : HasDerivAt (fun s : ℝ => t.normal (parameter q, (xi, s)))
      (t.normalDot (parameter q, (xi, shift + rate * eta)))
      (shift + rate * eta)) :
    HasDerivAt
      (fun s : ℝ => (transportTangent t parameter gap shift rate amplitude normalScale).normal
        (q, (xi, s)))
      ((transportTangent t parameter gap shift rate amplitude normalScale).normalDot
        (q, (xi, eta))) eta := by
  have hc : HasDerivAt (fun s : ℝ => shift + rate * s) rate eta := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id eta).const_mul rate).const_add shift
  have h := (hn.scomp eta hc).const_smul normalScale
  simp only [smul_smul] at h
  exact h

end Inputs

section CopyInputCompatibility

variable {P Q V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Copy-level counterpart of `CopySolveCompatibility.commonSolve_of_compatibleInputs`.
The condition compares only native coefficients and converted sources. -/
theorem copySolve_of_compatibleInputs (d : LinearData P V H) (e : LinearData Q V H)
    (parameter : Q → P) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (gap : ℕ) (shift rate amplitude : ℝ) (hrate : 0 < rate)
    {U : Set P} (hA : ContinuousOn d.coefficient (U ×ˢ univ))
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (hi : CopySolveCompatibility.SameInputsAt e (CopySolveCompatibility.transportData d parameter
        gap shift rate amplitude) q)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
        copy Y).2 ∈
      Icc a b) :
    e.copySolve (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q,
        Y) =
      amplitude • d.copySolve g (CopySolveCompatibility.time_interval_mono shift hrate hab) copy
        (parameter q, coverPower gap Y) := by
  have he : e.copySolve (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab
      copy (q, Y) =
      (CopySolveCompatibility.transportData d parameter gap shift rate amplitude).copySolve
        (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) := by
    exact CopySolveCompatibility.anchoredSolve_eq_of_sameInputs _ _ _ hab q hi copy Y _
  rw [he]
  unfold CopySolveCompatibility.transportData CopySolveCompatibility.transportGeometry
  rw [CopySolveCompatibility.copySolve_scaleSource, CopySolveCompatibility.copySolve_transform]
  congr 1
  apply CopySolveCompatibility.copySolve_timeData d g shift rate hrate hab hA hB hf copy hq
  simpa only [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.coordinates_refine]
      using hslot

end CopyInputCompatibility

section TangentTransport

variable {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
/-- Normal scaling changes neither tangent projection nor the resulting
ODE.  Moving the clock factor from the forcing map into the source
preserves its actual converted forcing. -/
theorem transportTangent_sameInputs (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) (hnormal : normalScale ≠ 0) (q : Q) :
    CopySolveCompatibility.SameInputsAt
      (transportTangent t parameter gap shift rate amplitude normalScale).linearData
      (CopySolveCompatibility.transportData t.linearData parameter gap shift rate amplitude) q := by
  constructor
  · intro z
    exact NormalScaling.projectedOperator_rescale _ _ _ rate _ hnormal
  · intro z Y
    change negativeTangentProjection (normalScale • t.normal
        (parameter q, CopySolveCompatibility.nativeTimeMap shift rate z))
        ((rate * amplitude) • t.source (parameter q, coverPower gap Y)) =
      (rate • negativeTangentProjection (t.normal
        (parameter q, CopySolveCompatibility.nativeTimeMap shift rate z)))
        (amplitude • t.source (parameter q, coverPower gap Y))
    rw [NormalScaling.negativeTangentProjection_smul _ hnormal]
    simp only [_root_.smul_apply, map_smul, smul_smul, mul_comm rate amplitude]

theorem copySolve_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    (transportTangent t parameter gap shift rate amplitude normalScale).linearData.copySolve
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
        amplitude • t.linearData.copySolve g
          (CopySolveCompatibility.time_interval_mono shift hrate hab) copy
          (parameter q, coverPower gap Y) :=
  copySolve_of_compatibleInputs t.linearData _ parameter g hab gap shift rate amplitude hrate
    hA hB hf q hq (transportTangent_sameInputs t parameter gap shift rate amplitude normalScale
      hnormal q) copy Y hslot

/-- The common output uses the transported cutoff, so the clock identity
is needed only at points inside the reference integration interval. -/
theorem commonSolve_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ))
    (cutoff : Plane → ℝ)
    (hcutoff : support cutoff ⊆ univ ×ˢ Icc (shift + rate * a) (shift + rate * b))
    (q : Q) (hq : parameter q ∈ U) (Y : Plane) :
    (transportTangent t parameter gap shift rate amplitude normalScale).linearData.commonSolve
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab
      (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate) (q, Y) =
        amplitude • t.linearData.commonSolve g
          (CopySolveCompatibility.time_interval_mono shift hrate hab) cutoff
          (parameter q, coverPower gap Y) :=
  CopySolveCompatibility.commonSolve_of_compatibleInputs t.linearData _ parameter g hab gap
    shift rate amplitude hrate hA hB hf cutoff hcutoff q hq
    (transportTangent_sameInputs t parameter gap shift rate amplitude normalScale hnormal q) Y

theorem copyPressureReal_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    copyPressureReal (transportTangent t parameter gap shift rate amplitude normalScale)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
        (rate * amplitude / normalScale) * copyPressureReal t g
          (CopySolveCompatibility.time_interval_mono shift hrate hab) copy
          (parameter q, coverPower gap Y) := by
  simp only [copyPressureReal]
  rw [copySolve_transport t parameter g hab gap shift rate amplitude normalScale hrate hnormal
    hA hB hf q hq copy Y hslot]
  simp only [transportTangent, nativePoint, coordinates_transport,
    _root_.smul_apply, map_smul, smul_smul]
  rw [mul_comm amplitude rate]
  exact NormalScaling.pressureCoefficient_rescale (H := H) _ _ _ _ _ rate amplitude hnormal

/-- Pressure includes the inverse frequency of the band in which it is
realized, in addition to the derived clock/normal factor. -/
theorem copyPressure_transport (t : TangentData P H) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    copyPressure (transportTangent t parameter gap shift rate amplitude normalScale)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy frequency
      (q, Y) =
        ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
          copyPressure t g (CopySolveCompatibility.time_interval_mono shift hrate hab)
            copy referenceFrequency (parameter q, coverPower gap Y) := by
  have hr : (referenceFrequency : ℂ) ≠ 0 := by exact_mod_cast hreference
  have hk : (frequency : ℂ) ≠ 0 := by exact_mod_cast hfrequency
  have hs : (normalScale : ℂ) ≠ 0 := by exact_mod_cast hnormal
  simp only [copyPressure, copyPressureReal_transport t parameter g hab gap shift rate amplitude
    normalScale hrate hnormal hA hB hf q hq copy Y hslot,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.real_smul]
  field_simp

end TangentTransport

section LocalizedTransport

variable {P Q E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual transported series is finite when the reference cutoff is
compact; the transport identities do not rely on a divergent-series value. -/
theorem transported_periodization_finite (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) {cutoff : Plane → ℝ} (hcutoff : HasCompactSupport cutoff)
    (F : Frequency → Q × Plane → E) (q : Q) (Y : Plane) :
    ∃ I : Finset Frequency,
      periodizedCopies (CopySolveCompatibility.transportGeometry g gap shift rate hrate)
        (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate) F (q, Y) =
      ∑ copy ∈ I,
        (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate)
          ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y) •
        F copy (q, Y) := by
  obtain ⟨I, hI⟩ := finite_transported_copy_cutoffs g gap shift rate hrate hcutoff ‖Y‖
  refine ⟨I, tsum_eq_sum (fun copy hcopy => ?_)⟩
  rw [hI Y le_rfl copy hcopy, zero_smul]

omit [CompleteSpace E] in
/-- A transported periodization only uses copy identities on the active
native interval.  In particular no equality of extended solves outside
that interval is required. -/
theorem periodizedCopies_transport_of_active (g : Geometry) (parameter : Q → P)
    {a b : ℝ} (gap : ℕ) (shift rate scale : ℝ) (hrate : 0 < rate)
    (cutoff : Plane → ℝ)
    (hcutoff : support cutoff ⊆ univ ×ˢ Icc (shift + rate * a) (shift + rate * b))
    (F : Frequency → Q × Plane → E) (G : Frequency → P × Plane → E)
    (q : Q) (Y : Plane)
    (hcopy : ∀ copy,
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
        copy Y).2 ∈ Icc a b →
      F copy (q, Y) = scale • G copy (parameter q, coverPower gap Y)) :
    periodizedCopies (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne')
      (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate) F (q, Y) =
        scale • periodizedCopies g cutoff G (parameter q, coverPower gap Y) := by
  unfold periodizedCopies
  calc
    _ = ∑' copy : Frequency, scale •
        (cutoff (g.coordinates copy (coverPower gap Y)) •
          G copy (parameter q, coverPower gap Y)) := by
      apply tsum_congr
      intro copy
      simp only [Function.comp_apply, coordinates_transport]
      by_cases hz : cutoff (g.coordinates copy (coverPower gap Y)) = 0
      · simp only [hz, zero_smul, smul_zero]
      · have hs : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
            copy Y).2 ∈ Icc a b :=
          (current_slot_iff g gap shift rate hrate copy Y a b).mpr (hcutoff hz).2
        rw [hcopy copy hs, smul_comm]
    _ = _ := tsum_const_smul'' scale

end LocalizedTransport

section ComplexTransport

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem realData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) :
    realData (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude) =
        transportTangent (realData t f) parameter gap shift rate amplitude normalScale := by
  unfold realData transportTangent transportSource
  congr 1
  funext z
  exact map_smul realPart (rate * amplitude) _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem imagData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) :
    imagData (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude) =
        transportTangent (imagData t f) parameter gap shift rate amplitude normalScale := by
  unfold imagData transportTangent transportSource
  congr 1
  funext z
  exact map_smul imagPart (rate * amplitude) _

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyVelocity_transport (t : TangentData P ProblemStatement.Space)
    (parameter : Q → P) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    copyVelocity (transportTangent t parameter gap shift rate amplitude normalScale)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
        amplitude • copyVelocity t g (CopySolveCompatibility.time_interval_mono shift hrate hab)
          copy (parameter q, coverPower gap Y) := by
  unfold copyVelocity
  rw [copySolve_transport t parameter g hab gap shift rate amplitude normalScale hrate hnormal
    hA hB hf q hq copy Y hslot, map_smul]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem complexCopyVelocity_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    complexCopyVelocity (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy (q, Y) =
        amplitude • complexCopyVelocity t f g
          (CopySolveCompatibility.time_interval_mono shift hrate hab)
          copy (parameter q, coverPower gap Y) := by
  have hr : ContinuousOn (realData t f).source (U ×ˢ univ) :=
    realPart.continuous.comp_continuousOn hf
  have hi : ContinuousOn (imagData t f).source (U ×ˢ univ) :=
    imagPart.continuous.comp_continuousOn hf
  simp only [complexCopyVelocity, realData_transport, imagData_transport]
  rw [copyVelocity_transport (realData t f) parameter g hab gap shift rate amplitude normalScale
    hrate hnormal hA hB hr q hq copy Y hslot,
    copyVelocity_transport (imagData t f) parameter g hab gap shift rate amplitude normalScale
    hrate hnormal hA hB hi q hq copy Y hslot]
  simp only [smul_add, smul_comm Complex.I amplitude]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem complexCopyPressure_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ)) (q : Q) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates
      copy Y).2 ∈ Icc a b) :
    complexCopyPressure (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab copy frequency
      (q, Y) =
        ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
          complexCopyPressure t f g (CopySolveCompatibility.time_interval_mono shift hrate hab)
            copy referenceFrequency (parameter q, coverPower gap Y) := by
  have hr : ContinuousOn (realData t f).source (U ×ˢ univ) :=
    realPart.continuous.comp_continuousOn hf
  have hi : ContinuousOn (imagData t f).source (U ×ˢ univ) :=
    imagPart.continuous.comp_continuousOn hf
  simp only [complexCopyPressure, realData_transport, imagData_transport]
  rw [copyPressure_transport (realData t f) parameter g hab gap shift rate amplitude normalScale
    referenceFrequency frequency hrate hnormal hreference hfrequency hA hB hr q hq copy Y hslot,
    copyPressure_transport (imagData t f) parameter g hab gap shift rate amplitude normalScale
    referenceFrequency frequency hrate hnormal hreference hfrequency hA hB hi q hq copy Y hslot]
  simp only [smul_add, Complex.real_smul]
  ring

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- One actual reference velocity supplies every transported band view. -/
theorem commonVelocity_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ))
    (cutoff : Plane → ℝ)
    (hcutoff : support cutoff ⊆ univ ×ˢ Icc (shift + rate * a) (shift + rate * b))
    (q : Q) (hq : parameter q ∈ U) (Y : Plane) :
    commonVelocity (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab
      (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate) (q, Y) =
        amplitude • commonVelocity t f g (CopySolveCompatibility.time_interval_mono shift hrate hab)
          cutoff (parameter q, coverPower gap Y) := by
  unfold commonVelocity
  apply periodizedCopies_transport_of_active g parameter gap shift rate amplitude hrate
    cutoff hcutoff
  intro copy hslot
  exact complexCopyVelocity_transport t f parameter g hab gap shift rate amplitude normalScale
    hrate hnormal hA hB hf q hq copy Y hslot

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- The actual common pressure has the derived clock, normal and carrier
frequency factors.  It is not assigned the velocity's scaling weight. -/
theorem commonPressure_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (gap : ℕ)
    (shift rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ))
    (cutoff : Plane → ℝ)
    (hcutoff : support cutoff ⊆ univ ×ˢ Icc (shift + rate * a) (shift + rate * b))
    (q : Q) (hq : parameter q ∈ U) (Y : Plane) :
    commonPressure (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne') hab
      (cutoff ∘ CopySolveCompatibility.nativeTimeMap shift rate) frequency (q, Y) =
        ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
          commonPressure t f g (CopySolveCompatibility.time_interval_mono shift hrate hab)
            cutoff referenceFrequency (parameter q, coverPower gap Y) := by
  unfold commonPressure
  apply periodizedCopies_transport_of_active g parameter gap shift rate
    ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) hrate cutoff hcutoff
  intro copy hslot
  exact complexCopyPressure_transport t f parameter g hab gap shift rate amplitude normalScale
    referenceFrequency frequency hrate hnormal hreference hfrequency hA hB hf q hq copy Y hslot

end ComplexTransport

section ZeroEntry

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

private theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst c
  subst d
  rfl

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- A reference interval `[0,L]` corresponds to the band interval
`[0,L/rate]`.  Keeping the same numerical length would change the anchor
problem; this specialization retains the actual common reference solve. -/
theorem commonVelocity_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ))
    (cutoff : Plane → ℝ) (hcutoff : support cutoff ⊆ univ ×ˢ Icc 0 L)
    (q : Q) (hq : parameter q ∈ U) (Y : Plane) :
    commonVelocity (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne')
      (div_pos hL hrate).le (cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 rate) (q, Y) =
        amplitude • commonVelocity t f g hL.le cutoff (parameter q, coverPower gap Y) := by
  have hlen : rate * (L / rate) = L := by field_simp
  have hs : support cutoff ⊆ univ ×ˢ Icc (0 + rate * 0) (0 + rate * (L / rate)) := by
    simpa only [mul_zero, zero_add, hlen] using hcutoff
  have h := commonVelocity_transport t f parameter g (div_pos hL hrate).le gap 0 rate
    amplitude normalScale hrate hnormal hA hB hf cutoff hs q hq Y
  refine h.trans (congrArg (fun z : ComplexVector => amplitude • z) ?_)
  exact interval_congr (fun a b hh => commonVelocity t f g (a := a) (b := b) hh cutoff
    (parameter q, coverPower gap Y)) _ _ (by ring) (by simpa only [zero_add] using hlen)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonPressure_zeroEntry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P)
    (g : Geometry) (gap : ℕ) (L rate amplitude normalScale referenceFrequency frequency : ℝ)
    (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    (hreference : referenceFrequency ≠ 0) (hfrequency : frequency ≠ 0)
    {U : Set P} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ))
    (cutoff : Plane → ℝ) (hcutoff : support cutoff ⊆ univ ×ˢ Icc 0 L)
    (q : Q) (hq : parameter q ∈ U) (Y : Plane) :
    commonPressure (transportTangent t parameter gap 0 rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne')
      (div_pos hL hrate).le (cutoff ∘ CopySolveCompatibility.nativeTimeMap 0 rate) frequency
      (q, Y) =
        ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) •
          commonPressure t f g hL.le cutoff referenceFrequency (parameter q, coverPower gap Y) := by
  have hlen : rate * (L / rate) = L := by field_simp
  have hs : support cutoff ⊆ univ ×ˢ Icc (0 + rate * 0) (0 + rate * (L / rate)) := by
    simpa only [mul_zero, zero_add, hlen] using hcutoff
  have h := commonPressure_transport t f parameter g (div_pos hL hrate).le gap 0 rate
    amplitude normalScale referenceFrequency frequency hrate hnormal hreference hfrequency
    hA hB hf cutoff hs q hq Y
  refine h.trans (congrArg (fun z : ℂ =>
    ((rate * amplitude / normalScale) * (referenceFrequency / frequency)) • z) ?_)
  exact interval_congr (fun a b hh => commonPressure t f g (a := a) (b := b) hh cutoff
    referenceFrequency (parameter q, coverPower gap Y)) _ _ (by ring)
    (by simpa only [zero_add] using hlen)

end ZeroEntry

end NavierStokes.ScaledTangentTransport
