/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEdgeExtension

/-!
# Qualitative regularity of the actual finite wave updates

All regularity statements below use the full open slow domain.  The
quantitative strip is used only for its fixed differential operators.
Native smoothness and genuine zero germs, rather than estimates on a
smaller strip, supply the continuation away from the active phase patches.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualWaveRegularity

open Set Function Filter WeightedClasses HarmonicCalculus LinearWaveBounds
open PeriodizedWaveBounds CorrectionState
open CurlClassBounds hiding ComplexVector
open scoped Topology ContDiff BigOperators


variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A qualitative domain for the same operators.  No quantitative bound is
extended from the original strip. -/
noncomputable def onDomain (s : StripData D) (Ω : Set D) (hΩ : IsOpen Ω) : StripData D where
  domain := Ω
  isOpen_domain := hΩ
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun _ => 1
  delta_pos := fun _ _ => zero_lt_one
  zeta := fun _ => 0
  zeta_smooth := contDiffOn_const
  zeta_nonneg := fun _ _ => le_rfl

theorem commonCorrected_onDomain (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) (Ω : Set D) (hΩ : IsOpen Ω) :
    a.commonCorrected (onDomain s Ω hΩ) d = a.commonCorrected s d := rfl

/-- These are native, uncorrected data.  In particular the smoothness of
the common corrected velocity is a conclusion, not a field of this record. -/
structure NativeData (a : CopyData D I) (s : StripData D) (d : GraphDirections D)
    (Ω : Set D) (hΩ : IsOpen Ω) where
  /-- Cells of `NativeData`, of type `Cells D I`. -/
  cells : Cells D I
  /-- Patch of `NativeData`, of type `ℕ → I → Set D`. -/
  patch : ℕ → I → Set D
  raw : LocalizedCurlRealization.RawData a (onDomain s Ω hΩ) d patch
  cutoff_support : ∀ n i, support (a.cutoff n i) ⊆ cells.carrier n i
  cover : ∀ n i x, x ∈ Ω → x ∈ cells.carrier n i → x ∈ patch n i ∨
    (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0

namespace NativeData

variable {a : CopyData D I} {s : StripData D} {d : GraphDirections D}
  {Ω : Set D} {hΩ : IsOpen Ω} (h : NativeData a s d Ω hΩ)

include h

theorem common_velocity_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n)) Ω :=
  LocalizedCurlRealization.RawData.common_velocity_smooth h.raw h.cells h.cutoff_support h.cover n

theorem common_potential_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (a.common.curlPotential s d n) Ω :=
  LocalizedCurlRealization.RawData.common_potential_smooth h.raw h.cells h.cutoff_support h.cover n

theorem glue_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → D → E) (f : ℕ → I → D → E)
    (hg : ∀ n i x, x ∈ h.cells.carrier n i → F n =ᶠ[𝓝 x] f n i)
    (hz : ∀ n x, (∀ i, x ∉ h.cells.carrier n i) → F n =ᶠ[𝓝 x] fun _ => 0)
    (hs : ∀ n i, ContDiffOn ℝ ∞ (f n i) (Ω ∩ h.patch n i))
    (hflat : ∀ n i x, ((a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) →
      f n i =ᶠ[𝓝 x] fun _ => 0) (n : ℕ) : ContDiffOn ℝ ∞ (F n) Ω := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  classical
  by_cases hi : ∃ i, x ∈ h.cells.carrier n i
  · obtain ⟨i, hi⟩ := hi
    rcases h.cover n i x hx hi with hC | h0
    · exact ((hs n i).contDiffAt ((h.raw.geometry n i).isOpen.mem_nhds ⟨hx,
        hC⟩)).congr_of_eventuallyEq
        (hg n i x hi)
    · exact contDiffAt_const.congr_of_eventuallyEq ((hg n i x hi).trans (hflat n i x h0))
  · exact contDiffAt_const.congr_of_eventuallyEq (hz n x (not_exists.mp hi))

theorem common_raw_smooth (n : ℕ) : ContDiffOn ℝ ∞ (a.common.amplitude n) Ω := by
  apply h.glue_smooth a.common.amplitude (fun n i => (a.localized i).amplitude n)
  · exact fun n _ _ hi => a.common_amplitude_germ h.cells h.cutoff_support n hi
  · exact fun _ _ hi => (a.common_zero_germs h.cells h.cutoff_support hi).1
  · exact h.raw.localized_smooth
  · exact fun _ _ _ hz => hz

theorem native_normal_smooth (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ (coefficient (a.background.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n) (a.background.phase n)
      ((a.localized i).amplitude n)) (Ω ∩ h.patch n i) :=
  normalCoefficient_contDiffOn (phaseNormal_contDiffOn (h.raw.geometry n i) (h.raw.phase n i))
    (h.raw.localized_smooth n i) (h.raw.normal n i)

/-- The actual normalized vector-potential coefficient has a smooth zero
extension too; smoothness of the bare phase normal off support is not used. -/
theorem common_normal_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (coefficient (a.background.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n) (a.background.phase n) (a.common.amplitude n)) Ω := by
  let B := fun n (f : D → ComplexVector) => coefficient (a.background.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (a.background.phase n) f
  have hmap {n : ℕ} {f g : D → ComplexVector} {x : D} (he : f =ᶠ[𝓝 x] g) :
      B n f =ᶠ[𝓝 x] B n g := by
    filter_upwards [he] with y hy
    simp only [B, coefficient, hy]
  change ContDiffOn ℝ ∞ (B n (a.common.amplitude n)) Ω
  apply h.glue_smooth (fun n => B n (a.common.amplitude n))
    (fun n i => B n ((a.localized i).amplitude n))
  · exact fun n _ _ hi => hmap (a.common_amplitude_germ h.cells h.cutoff_support n hi)
  · intro m x hi
    simpa only [B, coefficient_zero] using hmap (n := m) (a.common_zero_germs h.cells
        h.cutoff_support hi).1
  · exact h.native_normal_smooth
  · intro m i x hz
    simpa only [B, coefficient_zero] using hmap (n := m) hz

theorem native_corrected_smooth (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ ((a.corrected s d i).amplitude n) (Ω ∩ h.patch n i) := by
  have G := h.raw.geometry n i
  have hc := cylindricalCurl_contDiffOn G.isOpen (G.radius_smooth.inv G.radius_ne)
    G.radial_smooth G.angular_smooth G.axial_smooth (h.native_normal_smooth n i)
  exact (h.raw.localized_smooth n i).add
    ((hc.const_smul Complex.I).const_smul (1 / a.background.frequency n))

theorem common_corrected_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ ((a.commonCorrected s d).amplitude n) Ω := by
  apply h.glue_smooth (a.commonCorrected s d).amplitude (fun n i => (a.corrected s d i).amplitude n)
  · exact fun n _ _ hi => a.commonCorrected_amplitude_germ h.cells h.cutoff_support s d n hi
  · exact fun _ _ hi => a.commonCorrected_zero_germ h.cells h.cutoff_support s d hi
  · exact h.native_corrected_smooth
  · exact fun _ _ _ hz => (LocalizedCurlRealization.native_zero_germs a s d hz).2.1

/-- Locally finite native zero germs give a zero germ for the common
corrected amplitude, even if the phase or normal is singular at this point. -/
theorem common_zero_germ {n : ℕ} {x : D}
    (hz : ∀ i, x ∈ h.cells.carrier n i →
      (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) :
    (a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  by_cases hi : ∃ i, x ∈ h.cells.carrier n i
  · obtain ⟨i, hi⟩ := hi
    exact (a.commonCorrected_amplitude_germ h.cells h.cutoff_support s d n hi).trans
      (LocalizedCurlRealization.native_zero_germs a s d (hz i hi)).2.1
  · exact a.commonCorrected_zero_germ h.cells h.cutoff_support s d (not_exists.mp hi)

theorem common_velocity_zero_germ {n : ℕ} {x : D}
    (hz : ∀ i, x ∈ h.cells.carrier n i →
      (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) :
    vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.common_zero_germ hz] with y hy
  ext j
  simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]

end NativeData

/-! ## Discrete translations on an open domain

Unlike global translation identities, these statements only require the
actual fields on the physical slow domain.  Derivatives are genuine
Fréchet derivatives, transferred through an open neighborhood.
-/

/-- Translation on, given by `∀ x ∈ Ω, f (x + z) = f x`. -/
noncomputable def TranslationOn {E : Type} (Ω : Set D) (z : D) (f : D → E) : Prop :=
  ∀ x ∈ Ω, f (x + z) = f x

namespace TranslationOn

variable {E F G : Type} {Ω : Set D} {z : D} {f : D → E} {g : D → F}

omit [NormedSpace ℝ D] in
theorem const (c : E) : TranslationOn Ω z (fun _ : D => c) := fun _ _ => rfl

omit [NormedSpace ℝ D] in
theorem map (hf : TranslationOn Ω z f) (T : E → F) :
    TranslationOn Ω z (fun x => T (f x)) :=
  fun x hx => congrArg T (hf x hx)

omit [NormedSpace ℝ D] in
theorem map₂ (hf : TranslationOn Ω z f) (hg : TranslationOn Ω z g) (T : E → F → G) :
    TranslationOn Ω z (fun x => T (f x) (g x)) :=
  fun x hx => congrArg₂ T (hf x hx) (hg x hx)

omit [NormedSpace ℝ D] in
theorem component {ι : Type} {F : ι → Type} {f : D → ∀ i, F i}
    (hf : TranslationOn Ω z f) (i : ι) : TranslationOn Ω z (fun x => f x i) :=
  hf.map (fun v => v i)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv (hf : TranslationOn Ω z f) (hΩ : IsOpen Ω) :
    TranslationOn Ω z (fderiv ℝ f) := by
  intro x hx
  have he : (fun y => f (y + z)) =ᶠ[𝓝 x] f := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hf y hy
  simpa only [fderiv_comp_add_right] using he.fderiv_eq (𝕜 := ℝ)

theorem along {V : D → D} (hf : TranslationOn Ω z f)
    (hV : TranslationOn Ω z V) (hΩ : IsOpen Ω) :
    TranslationOn Ω z (HarmonicCalculus.along V f) := by
  intro x hx
  simp only [HarmonicCalculus.along, hf.fderiv hΩ x hx, hV x hx]

end TranslationOn

theorem phaseNormal_translation {Ω : Set D} {z : D} (hΩ : IsOpen Ω)
    {R Φ : D → ℝ} {Vr Vθ Vz : D → D}
    (hR : TranslationOn Ω z R) (hr : TranslationOn Ω z Vr)
    (hθ : TranslationOn Ω z Vθ) (hz : TranslationOn Ω z Vz)
    (hΦ : TranslationOn Ω z Φ) :
    TranslationOn Ω z (phaseNormal R Vr Vθ Vz Φ) := by
  intro x hx
  simp only [phaseNormal, hΦ.along hr hΩ x hx, hΦ.along hθ hΩ x hx,
    hΦ.along hz hΩ x hx, hR x hx]

theorem cylindricalCurl_translation {Ω : Set D} {z : D} (hΩ : IsOpen Ω)
    {R : D → ℝ} {Vr Vθ Vz : D → D} {a : D → ComplexVector}
    (hR : TranslationOn Ω z R) (hr : TranslationOn Ω z Vr)
    (hθ : TranslationOn Ω z Vθ) (hz : TranslationOn Ω z Vz)
    (ha : TranslationOn Ω z a) :
    TranslationOn Ω z (cylindricalCurl R Vr Vθ Vz a) := by
  intro x hx
  simp only [cylindricalCurl, hR x hx,
    (ha.component 2).along hθ hΩ x hx, (ha.component 1).along hz hΩ x hx,
    (ha.component 0).along hz hΩ x hx, (ha.component 2).along hr hΩ x hx,
    (ha.component 1).along hr hΩ x hx, (ha.component 0).along hθ hΩ x hx, ha x hx]

omit [NormedSpace ℝ D] in
theorem common_amplitude_translation (a : CopyData D I) {Ω : Set D} {z : D}
    (n : ℕ) (e : I ≃ I)
    (hψ : ∀ i x, x ∈ Ω → a.cutoff n (e i) (x + z) = a.cutoff n i x)
    (ha : ∀ i x, x ∈ Ω → a.amplitude n (e i) (x + z) = a.amplitude n i x) :
    TranslationOn Ω z (a.common.amplitude n) := by
  intro x hx
  change (∑' i, a.cutoff n i (x + z) • a.amplitude n i (x + z)) =
    ∑' i, a.cutoff n i x • a.amplitude n i x
  rw [← e.tsum_eq]
  apply tsum_congr
  intro i
  rw [hψ i x hx, ha i x hx]

theorem commonCorrected_translation (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) {Ω : Set D} {z : D} (hΩ : IsOpen Ω) (n : ℕ)
    (hR : TranslationOn Ω z (a.background.radius n))
    (hr : TranslationOn Ω z (d.radialField n))
    (hΦ : TranslationOn Ω z (a.background.phase n))
    (ha : TranslationOn Ω z (a.common.amplitude n)) :
    TranslationOn Ω z ((a.commonCorrected s d).amplitude n) := by
  have hn := phaseNormal_translation hΩ hR hr (TranslationOn.const d.angular)
    (TranslationOn.const (s.epsilon n • d.axial)) hΦ
  have hB := hn.map₂ ha normalCoefficient
  have hc := cylindricalCurl_translation hΩ hR hr (TranslationOn.const d.angular)
    (TranslationOn.const (s.epsilon n • d.axial)) hB
  exact ha.map₂ (hc.map (fun v => (1 / a.background.frequency n) • (Complex.I • v)))
    (fun u v => u + v)

theorem common_velocity_translation (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) {Ω : Set D} {z : D} (hΩ : IsOpen Ω) (n : ℕ)
    (hR : TranslationOn Ω z (a.background.radius n))
    (hr : TranslationOn Ω z (d.radialField n))
    (hΦ : TranslationOn Ω z (a.background.phase n))
    (ha : TranslationOn Ω z (a.common.amplitude n)) :
    TranslationOn Ω z (vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n)) := by
  intro x hx
  have hv := commonCorrected_translation a s d hΩ n hR hr hΦ ha x hx
  ext i
  simp only [vectorMode, mode, carrier, hΦ x hx, hv]

/-! ## Qualitative regularity of the literal native solves -/

section Modal

open CommonCoverSolve TorusInverse ParticularWaveBounds
open PrimaryCopyBridge hiding Plane Frequency
open PrimaryPulseBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Primitive smooth coefficient, forcing, and synthesis columns on a
neighborhood of each entire Volterra path. No solved field occurs here. -/
structure ModalSmooth (t : ℕ → TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : ℕ → Geometry) (L : ℕ → ℝ)
    (Ω : Set (P × Plane)) (C : ℕ → Frequency → Set (P × Plane)) where
  /-- Frame of `ModalSmooth`, of type `ℕ → PrimaryODE.FrameData (P × ℝ)`. -/
  frame : ℕ → PrimaryODE.FrameData (P × ℝ)
  /-- Neighborhood of `ModalSmooth`, of type `ℕ → Frequency → Set (P × Plane)`. -/
  neighborhood : ℕ → Frequency → Set (P × Plane)
  open_neighborhood : ∀ n k, IsOpen (neighborhood n k)
  contains : ∀ n k, Ω ∩ C n k ⊆ neighborhood n k
  /-- Interval of `ModalSmooth`, of type `ℕ → Set ℝ`. -/
  interval : ℕ → Set ℝ
  open_interval : ∀ n, IsOpen (interval n)
  contains_interval : ∀ n, Icc 0 (L n) ⊆ interval n
  bridge : ∀ n k, Inputs (frame n) (t n) harmonic (g n) k (neighborhood n k) 0 (L n)
  coefficient : ∀ n k, ContDiffOn ℝ ∞
    ((copyFrame (frame n) (g n) k).coefficient harmonic) (neighborhood n k ×ˢ interval n)
  forcing : ∀ n k, ContDiffOn ℝ ∞
    ((copyFrame (frame n) (g n) k).forcing (copySource (t n).source (g n) k))
      (neighborhood n k ×ˢ interval n)
  columns : ∀ n k (i : Fin 2), ContDiffOn ℝ ∞
    (synthesisColumn (copyFrame (frame n) (g n) k) i) (neighborhood n k ×ˢ interval n)
  current_slot : ∀ n k x, x ∈ neighborhood n k → ((g n).coordinates k x.2).2 ∈ Ioo 0 (L n)

theorem ModalSmooth.copySolve_smooth
    {t : ℕ → TangentData P ProblemStatement.Space} {harmonic : ℤ}
    {g : ℕ → Geometry} {L : ℕ → ℝ} {Ω : Set (P × Plane)}
    {C : ℕ → Frequency → Set (P × Plane)} (h : ModalSmooth t harmonic g L Ω C)
    (hL : ∀ n, 0 < L n) (n : ℕ) (k : Frequency) :
    ContDiffOn ℝ ∞ ((t n).linearData.copySolve (g n) (hL n).le k) (Ω ∩ C n k) :=
  (copySolve_contDiffOn_from_modal (h.frame n) (t n) harmonic (g n) k (hL n)
    (h.open_neighborhood n k) (h.open_interval n) (h.contains_interval n) (h.bridge n k)
    (h.coefficient n k) (h.forcing n k) (h.columns n k) (h.current_slot n k)).mono
      (h.contains n k)

theorem complexCopy_smooth
    {t : ℕ → TangentData P ProblemStatement.Space} {source : ℕ → P × Plane → ComplexVector}
    {harmonic : ℤ} {g : ℕ → Geometry} {L : ℕ → ℝ} {Ω : Set (P × Plane)}
    {C : ℕ → Frequency → Set (P × Plane)}
    (hr : ModalSmooth (fun n => realData (t n) (source n)) harmonic g L Ω C)
    (hi : ModalSmooth (fun n => imagData (t n) (source n)) harmonic g L Ω C)
    (hL : ∀ n, 0 < L n) (n : ℕ) (k : Frequency) :
    ContDiffOn ℝ ∞ (complexCopyVelocity (t n) (source n) (g n) (hL n).le k) (Ω ∩ C n k) := by
  have hreal := complexify.contDiff.comp_contDiffOn (hr.copySolve_smooth hL n k)
  have himag := complexify.contDiff.comp_contDiffOn (hi.copySolve_smooth hL n k)
  have hc := hreal.add (himag.const_smul Complex.I)
  simp only [Function.comp_def] at hc ⊢
  exact hc

end Modal

/-- The actual signed quotient is smooth from its matrix, target, request,
mask and homogeneous fundamental, on the strict covariance cone. -/
theorem signed_coefficients_smooth (s : StripData D) (d : GraphDirections D)
    (a : WaveCoefficients D) (H : ℕ → D → SignedWaveUpdate.Mat2)
    (T R : ℕ → D → SignedWaveUpdate.Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → ProblemStatement.Space)
    (A : ℕ → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space)
    (j : Fin 2) (n : ℕ) {Ω : Set D}
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H n x i j) Ω)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T n x i) Ω)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R n x i) Ω)
    (hm : ContDiffOn ℝ ∞ (mask n) Ω) (hv : ContDiffOn ℝ ∞ (v n) Ω)
    (hc : ∀ x ∈ Ω, SmoothCovariance.StrictCone (H n x) (T n x)) :
    ContDiffOn ℝ ∞ ((SignedWaveUpdate.coefficients a s d H T R mask v Ndot A j).amplitude n) Ω := by
  have hnum := SmoothCovariance.contDiffOn_inverse_solution hH hR
    (fun x hx => (hc x hx).det_ne_zero) j
  have hden := SmoothCovariance.contDiffOn_amplitudes hH hT hc j
  have hinc : ContDiffOn ℝ ∞ (fun x => SignedCovariance.increment (H n x) (T n x) (R n x) j) Ω :=
    hnum.div (contDiffOn_const.mul hden)
      (fun x hx => mul_ne_zero (by norm_num) ((hc x hx).amplitudes_pos j).ne')
  exact complexify.contDiff.comp_contDiffOn ((contDiffOn_const.mul hinc |>.mul hm).smul hv)

/-! ## One actual mode on the full physical slow domain -/

/-- Point: an abbreviation for `CorrectionStep.CyclePoint`. -/
abbrev Point := CorrectionStep.CyclePoint
/-- Cylinder: an abbreviation for `Point × ℝ`. -/
abbrev Cylinder := Point × ℝ

/-- Full domain, given by `HarmonicResidual.liftDomain (PhysicalMeanDomain.slowDomain
U.carrier)`. -/
noncomputable def fullDomain {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord) : Set Cylinder :=
  HarmonicResidual.liftDomain (PhysicalMeanDomain.slowDomain U.carrier)

theorem fullDomain_open {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord) :
    IsOpen (fullDomain U) :=
  (PhysicalMeanDomain.slowDomain_open U.isOpen).prod isOpen_univ

/-- Native domain, given by `e.symm ⁻¹' fullDomain U`. -/
noncomputable def nativeDomain {coord : ℝ} (e : Cylinder ≃ₗᵢ[ℝ] D)
    (U : LocalSignedRequest.SlowRegion coord) : Set D := e.symm ⁻¹' fullDomain U

theorem nativeDomain_open {coord : ℝ} (e : Cylinder ≃ₗᵢ[ℝ] D)
    (U : LocalSignedRequest.SlowRegion coord) : IsOpen (nativeDomain e U) :=
  (fullDomain_open U).preimage e.symm.continuous

/-- Deck shift, given by `((0, (0, ((k.1 : ℝ), (k.2 : ℝ)))), 0)`. -/
noncomputable def deckShift (k : TorusInverse.Frequency) : Cylinder :=
  ((0, (0, ((k.1 : ℝ), (k.2 : ℝ)))), 0)

/-- Mode oscillation, defined pointwise by `(vectorMode (a.background.frequency n)
(a.background.phase n) ((a.commonCorrected s d).amplitude n) (e x) i).re`. -/
noncomputable def modeOscillation (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) (e : Cylinder ≃ₗᵢ[ℝ] D) : Oscillation Point :=
  fun n x i => (vectorMode (a.background.frequency n) (a.background.phase n)
    ((a.commonCorrected s d).amplitude n) (e x) i).re

/-- Primitive continuation and deck identities for one mode. All spatial
smoothness is confined to the genuine native patches. Radial support is
proved using localized raw-amplitude zero germs. -/
structure ModeData (a : CopyData D I) (s : StripData D) (d : GraphDirections D)
    (e : Cylinder ≃ₗᵢ[ℝ] D) {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (r₀ r₁ : ℝ) where
  /-- Native of `ModeData`, of type `NativeData a s d (nativeDomain e U) (nativeDomain_open e
  U)`. -/
  native : NativeData a s d (nativeDomain e U) (nativeDomain_open e U)
  /-- Reindex of `ModeData`, of type `ℕ → TorusInverse.Frequency → I ≃ I`. -/
  reindex : ℕ → TorusInverse.Frequency → I ≃ I
  cutoff_deck : ∀ n k i x, x ∈ nativeDomain e U →
    a.cutoff n (reindex n k i) (x + e (deckShift k)) = a.cutoff n i x
  amplitude_deck : ∀ n k i x, x ∈ nativeDomain e U →
    a.amplitude n (reindex n k i) (x + e (deckShift k)) = a.amplitude n i x
  radius_deck : ∀ n k, TranslationOn (nativeDomain e U) (e (deckShift k)) (a.background.radius n)
  radial_deck : ∀ n k, TranslationOn (nativeDomain e U) (e (deckShift k)) (d.radialField n)
  phase_deck : ∀ n k, TranslationOn (nativeDomain e U) (e (deckShift k)) (a.background.phase n)
  radial_zero : ∀ n (x : Cylinder), x.1.2.1 ∈ U.carrier →
    x.1.1 ∉ Icc (VariableGaugeMean.qLength coord x.1.2.1 * r₀)
      (VariableGaugeMean.qLength coord x.1.2.1 * r₁) →
    ∀ i, e x ∈ native.cells.carrier n i →
      (a.localized i).amplitude n =ᶠ[𝓝 (e x)] fun _ => 0

namespace ModeData

variable {a : CopyData D I} {s : StripData D} {d : GraphDirections D}
    {e : Cylinder ≃ₗᵢ[ℝ] D} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : ModeData a s d e U r₀ r₁)

include h

theorem smooth : WaveStateRegularity.AngularSmooth
    (PhysicalMeanDomain.slowDomain U.carrier) (modeOscillation a s d e) := by
  intro n i
  have hs := (h.native.common_velocity_smooth n).comp e.contDiff.contDiffOn
    (show MapsTo e (fullDomain U) (nativeDomain e U) from fun x hx => by
      simpa only [nativeDomain, mem_preimage, e.symm_apply_apply] using hx)
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn hs)

theorem periodic : CorrectionStep.OscillationPeriodic U.carrier (modeOscillation a s d e) := by
  intro n R t ht θ Y k
  have hx : e ((R, (t, Y)), θ) ∈ nativeDomain e U := by
    simpa only [nativeDomain, mem_preimage, e.symm_apply_apply, fullDomain,
      HarmonicResidual.liftDomain, mem_prod, mem_univ, and_true,
      PhysicalMeanDomain.slowDomain, Set.mem_ofPred_eq] using ht
  have hp := common_velocity_translation a s d (nativeDomain_open e U) n
    (h.radius_deck n k) (h.radial_deck n k) (h.phase_deck n k)
    (common_amplitude_translation a n (h.reindex n k)
      (h.cutoff_deck n k) (h.amplitude_deck n k)) (e ((R, (t, Y)), θ)) hx
  have he : e ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) =
      e ((R, (t, Y)), θ) + e (deckShift k) := by
    rw [← map_add]
    congr 1
    simp only [deckShift, Prod.add_def, add_zero]
  funext i
  change (vectorMode _ _ _ (e ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ)) i).re = _
  rw [he, hp]
  rfl

theorem support : WaveStateRegularity.WaveSupport U r₀ r₁ (modeOscillation a s d e) := by
  intro n θ i x hx hn
  by_contra hout
  have hz := (h.native.common_velocity_zero_germ (h.radial_zero n (x, θ) hx hout)).self_of_nhds
  apply hn
  change (vectorMode _ _ _ (e (x, θ)) i).re = 0
  rw [hz]
  rfl

theorem regular :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (modeOscillation a s d e) ∧
    CorrectionStep.OscillationPeriodic U.carrier (modeOscillation a s d e) ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (modeOscillation a s d e) :=
  ⟨h.smooth, h.periodic, h.support⟩

end ModeData

/-! ## Finite sums retain the whole-domain conclusions -/

theorem finite_smooth {ι : Type} {Ω : Set Point} (labels : ℕ → Finset ι)
    (u : ι → Oscillation Point) (hs : ∀ l, WaveStateRegularity.AngularSmooth Ω (u l)) :
    WaveStateRegularity.AngularSmooth Ω (LabelSumBounds.fieldSum labels u) := by
  intro n i
  exact ContDiffOn.sum (fun l _ => hs l n i)

theorem finite_periodic {ι : Type} {U : Set TorusInverse.Plane} (labels : ℕ → Finset ι)
    (u : ι → Oscillation Point) (hp : ∀ l, CorrectionStep.OscillationPeriodic U (u l)) :
    CorrectionStep.OscillationPeriodic U (LabelSumBounds.fieldSum labels u) := by
  intro n R t ht θ Y k
  funext i
  apply Finset.sum_congr rfl
  intro l _
  exact congrFun (hp l n R t ht θ Y k) i

theorem finite_support {ι : Type} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (labels : ℕ → Finset ι)
    (u : ι → Oscillation Point) (hs : ∀ l, WaveStateRegularity.WaveSupport U r₀ r₁ (u l)) :
    WaveStateRegularity.WaveSupport U r₀ r₁ (LabelSumBounds.fieldSum labels u) :=
  WaveStateRegularity.fieldSum_support (fun n l _ θ i => hs l n θ i)

theorem finset_regular {ι : Type} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (t : Finset ι) (u : ι → Oscillation Point)
    (h : ∀ l ∈ t,
      WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) (u l) ∧
      CorrectionStep.OscillationPeriodic U.carrier (u l) ∧
      WaveStateRegularity.WaveSupport U r₀ r₁ (u l)) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (LabelSumBounds.fieldSum (fun _ => t) u) ∧
    CorrectionStep.OscillationPeriodic U.carrier (LabelSumBounds.fieldSum (fun _ => t) u) ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (LabelSumBounds.fieldSum (fun _ => t) u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n i
    exact ContDiffOn.sum (fun l hl => (h l hl).1 n i)
  · intro n R q hq θ Y k
    funext i
    exact Finset.sum_congr rfl (fun l hl => congrFun ((h l hl).2.1 n R q hq θ Y k) i)
  · exact WaveStateRegularity.fieldSum_support (fun n l hl θ i => (h l hl).2.2 n θ i)

/-! ## The literal particular update of the cycle -/

section ParticularCycle

open CorrectionStep ParticularWaveAssembly ParticularWaveBounds CopyAngularInvariance

/-- Particular space: an abbreviation for `(CycleSlow × ℝ) × TorusInverse.Plane`. -/
abbrev ParticularSpace := (CycleSlow × ℝ) × TorusInverse.Plane

/-- Particular chart, given by `(StateReindex.cylinder cycleAssoc).trans angleShuffle`. -/
noncomputable def particularChart : Cylinder ≃ₗᵢ[ℝ] ParticularSpace :=
  (StateReindex.cylinder cycleAssoc).trans angleShuffle

/-- Particular strip, given by `ParticularParameters.nativeStrip (reindexStrip cycleAssoc.symm
p.strip)`. -/
noncomputable def particularStrip {ι : Type} (p : CycleParameters ι) : StripData ParticularSpace :=
  ParticularParameters.nativeStrip (reindexStrip cycleAssoc.symm p.strip)

/-- Particular copy data as an element of `CopyData ParticularSpace TorusInverse.Frequency`. -/
noncomputable def particularCopyData {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι) (j : ℤ) :
    CopyData ParticularSpace TorusInverse.Frequency :=
  (p.particular l).copyData (StateReindex.context cycleAssoc.symm c)
    (StateReindex.state cycleAssoc.symm u) (StateReindex.block cycleAssoc.symm (v.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.aliasCoefficients l)) j

/-- Deck covariance of the actual Volterra coefficient follows from
periodicity of its incoming residual coefficient, with the same anchor. -/
theorem particular_amplitude_deck {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι) (j : ℤ)
    (n : ℕ) (k m : TorusInverse.Frequency) (x : ParticularSpace)
    (hp : CommonCoverSolve.PeriodicAt ((particularCopyData p v c u l j).source n) x.1) :
    (particularCopyData p v c u l j).amplitude n
      (k + CommonCoverSolve.coverIndex ((p.particular l).geometry n).gap m)
      (x.1, x.2 + TorusAverages.latticePoint m) =
        (particularCopyData p v c u l j).amplitude n k x := by
  exact complexCopyVelocity_deck _ _ _ ((p.particular l).length_pos n).le k m x.1 hp x.2

theorem particular_cutoff_deck {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι) (j : ℤ)
    (n : ℕ) (k m : TorusInverse.Frequency) (x : ParticularSpace) :
    (particularCopyData p v c u l j).cutoff n
      (k + CommonCoverSolve.coverIndex ((p.particular l).geometry n).gap m)
      (x.1, x.2 + TorusAverages.latticePoint m) =
        (particularCopyData p v c u l j).cutoff n k x := by
  change (p.particular l).cutoff n
    (((p.particular l).geometry n).coordinates
      (k + CommonCoverSolve.coverIndex ((p.particular l).geometry n).gap m)
        (x.2 + TorusAverages.latticePoint m)) = _
  rw [CommonCoverSolve.Geometry.coordinates_deck]
  rfl

/-- This representation is derived from the actual angle-lifted Volterra
solve and the original carrier. No equality of completed output fields is
an assumption. -/
theorem particularBlock_eq_modes {ι : Type} (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point) (l : ι)
    (hR : ∀ n, Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
      ((p.particular l).background.radius n))
    (hr : ∀ n, Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
      ((p.particular l).directions.radialField n))
    (hf : ∀ n, (v.blocks l).frequency n ≠ 0) :
    (p.particularBlock v c u l).oscillation =
      LabelSumBounds.fieldSum (fun _ => modes v.residualBand)
        (fun j => modeOscillation (particularCopyData p v c u l j)
          (particularStrip p) (p.particular l).directions particularChart) := by
  have ha (j : ℤ) (n : ℕ) :
      Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
        (((particularCopyData p v c u l j).commonCorrected (particularStrip p)
          (p.particular l).directions).amplitude n) := by
    apply CopyData.commonCorrected_invariant
    · intro m k
      exact nativeCutoff_invariant ((0 : CycleSlow), (1 : ℝ)) _ _ k
    · intro m k
      exact complexCopyVelocity_invariant (angleTangent_invariant _) (angleLift_invariant _)
        _ ((p.particular l).length_pos m).le k
    · exact hR
    · exact hr
    · intro m
      exact Invariant.const _
    · intro m
      exact ⟨_, actualCarrier_affine _ _ j m⟩
  funext n x i
  unfold CycleParameters.particularBlock
  rw [StateReindex.block_oscillation]
  change ((p.particular l).updateBlock _ _ _ _ _ _ _).oscillation n
    (cycleAssoc x.1, x.2) i = _
  rw [ParticularParameters.updateBlock, assembledBlock_value]
  apply Finset.sum_congr rfl
  intro j _hj
  have hi := invariant_angleShuffle (ha j n) (cycleAssoc x.1) x.2
  have hc := actualCarrier_character (p.particular l).background
    (StateReindex.block cycleAssoc.symm (v.blocks l)) j hf n (cycleAssoc x.1, x.2)
  change Complex.re (_ * _) = Complex.re
    ((((particularCopyData p v c u l j).commonCorrected (particularStrip p)
      (p.particular l).directions).amplitude n (angleShuffle (cycleAssoc x.1, x.2)) i) *
      carrier ((actualCarrier (p.particular l).background
        (StateReindex.block cycleAssoc.symm (v.blocks l)) j).frequency n)
        ((actualCarrier (p.particular l).background
          (StateReindex.block cycleAssoc.symm (v.blocks l)) j).phase n)
          (angleShuffle (cycleAssoc x.1, x.2)))
  rw [hc, hi]
  rfl

/-- Full-domain native inputs for the same particular copies and the same
incoming residual data used by `CycleParameters.particularBlock`. -/
structure ParticularData {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (r₀ r₁ : ℝ) where
  /-- Mode supplied by `ParticularData`. -/
  mode : ∀ l j, j ∈ modes v.residualBand →
    ModeData (particularCopyData p v c u l j) (particularStrip p)
      (p.particular l).directions particularChart U r₀ r₁
  radius_angular : ∀ l n, Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
    ((p.particular l).background.radius n)
  radial_angular : ∀ l n, Invariant (((0 : CycleSlow), 1), (0 : TorusInverse.Plane))
    ((p.particular l).directions.radialField n)
  frequency : ∀ l n, (v.blocks l).frequency n ≠ 0

theorem ParticularData.block_regular {ι : Type} {p : CycleParameters ι} {v : CycleCoefficients ι}
    {c : Context Point} {u : State Point} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : ParticularData p v c u U r₀ r₁) (l : ι) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.particularBlock v c u l).oscillation ∧
    OscillationPeriodic U.carrier (p.particularBlock v c u l).oscillation ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.particularBlock v c u l).oscillation := by
  rw [particularBlock_eq_modes p v c u l (h.radius_angular l) (h.radial_angular l) (h.frequency l)]
  exact finset_regular _ _ (fun j hj => (h.mode l j hj).regular)

theorem ParticularData.regular {ι : Type} {p : CycleParameters ι} {v : CycleCoefficients ι}
    {c : Context Point} {u : State Point} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : ParticularData p v c u U r₀ r₁) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.particularVelocity v c u) ∧
    OscillationPeriodic U.carrier (p.particularVelocity v c u) ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.particularVelocity v c u) :=
  ⟨finite_smooth _ _ (fun l => (h.block_regular l).1),
    finite_periodic _ _ (fun l => (h.block_regular l).2.1),
    finite_support _ _ (fun l => (h.block_regular l).2.2)⟩

end ParticularCycle

/-! ## The literal signed update, using the post-particular request -/

section SignedCycle

open CorrectionStep CopyAngularInvariance

/-- The native signed coefficient inherits a deck identity from the
literal matrix, targets, mask, and homogeneous fundamental. -/
theorem signed_amplitude_deck (p : PeriodizedSignedParameters Point I) (s : StripData Point)
    (request : ℕ → Cylinder → SignedWaveUpdate.Vec2) (n : ℕ) (i j : I) (x z : Cylinder)
    (hH : p.matrix j n (x + z) = p.matrix i n x)
    (hT : p.target j n (x + z) = p.target i n x)
    (hR : request n (x + z) = request n x)
    (hm : p.mask j n (x + z) = p.mask i n x)
    (hv : p.fundamental j n (x + z) = p.fundamental i n x) :
    (p.copyData s request).amplitude n j (x + z) = (p.copyData s request).amplitude n i x := by
  change complexify (SignedWaveUpdate.signedVector (HarmonicWaveInteraction.productStrip s)
    (p.matrix j) (p.target j) request (p.mask j) (p.fundamental j) p.column n (x + z)) =
    complexify (SignedWaveUpdate.signedVector (HarmonicWaveInteraction.productStrip s)
      (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i) p.column n x)
  simp only [SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar, hH, hT, hR, hm, hv]

/-- Angular identities of the primitive signed inputs. No identity of the
corrected field, and no regularity away from the native support, is assumed. -/
structure SignedAngles (p : PeriodizedSignedParameters Point I) (s : StripData Point)
    (request : ℕ → Cylinder → SignedWaveUpdate.Vec2) where
  /-- Slope of `SignedAngles`, of type `ℕ → ℝ`. -/
  slope : ℕ → ℝ
  radius : ∀ n, Invariant ((0 : Point), 1) (p.base.radius n)
  radial : ∀ n, Invariant ((0 : Point), 1) (p.directions.radialField n)
  phase : ∀ n, AffinePhase ((0 : Point), 1) (slope n) (p.base.phase n)
  frequency_slope : ∀ n, p.base.frequency n * slope n = (p.angularFrequency n : ℝ)
  matrix : ∀ i n, Invariant ((0 : Point), 1) (p.matrix i n)
  target : ∀ i n, Invariant ((0 : Point), 1) (p.target i n)
  request : ∀ n, Invariant ((0 : Point), 1) (request n)
  mask : ∀ i n, Invariant ((0 : Point), 1) (p.mask i n)
  fundamental : ∀ i n, Invariant ((0 : Point), 1) (p.fundamental i n)
  cutoff : ∀ i n, Invariant ((0 : Point), 1) (p.cutoff i n)

namespace SignedAngles

variable {p : PeriodizedSignedParameters Point I} {s : StripData Point}
  {request : ℕ → Cylinder → SignedWaveUpdate.Vec2} (h : SignedAngles p s request)

include h

theorem raw_invariant (n : ℕ) (i : I) :
    Invariant ((0 : Point), 1) ((p.copyData s request).amplitude n i) := by
  intro x t
  change complexify (SignedWaveUpdate.signedVector (HarmonicWaveInteraction.productStrip s)
    (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i) p.column n
      (x + t • ((0 : Point), 1))) =
    complexify (SignedWaveUpdate.signedVector (HarmonicWaveInteraction.productStrip s)
      (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i) p.column n x)
  simp only [SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    h.matrix i n x t, h.target i n x t, h.request n x t, h.mask i n x t,
    h.fundamental i n x t]

theorem corrected_invariant (n : ℕ) :
    Invariant ((0 : Point), 1)
      (((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
        p.directions).amplitude n) :=
  (p.copyData s request).commonCorrected_invariant _ _ _
    (fun n i => h.cutoff i n) h.raw_invariant h.radius h.radial
    (fun _ => Invariant.const _) (fun n => ⟨h.slope n, h.phase n⟩) n

theorem block_eq_mode :
    (p.exactBlock s request).oscillation =
      modeOscillation (p.copyData s request) (HarmonicWaveInteraction.productStrip s)
        p.directions (LinearIsometryEquiv.refl ℝ Cylinder) := by
  funext n x i
  rw [PeriodizedSignedParameters.exactBlock, SignedWaveUpdate.blockOfCoefficients,
    SignedWaveUpdate.coefficientBlock_velocity]
  have hphase : p.base.frequency n * p.base.phase n x =
      p.base.frequency n * p.base.phase n (x.1, 0) + (p.angularFrequency n : ℝ) * x.2 := by
    rw [affinePhase_eq_zeroSlice (h.phase n) x.1 x.2, mul_add, ← mul_assoc, h.frequency_slope]
  have hc := HarmonicFields.character_eq_carrier 1 (p.base.frequency n) (p.base.phase n) x
  simp only [Int.cast_one, mul_one] at hc
  change Complex.re (_ * HarmonicFields.character 1
    (p.base.frequency n * p.base.phase n (x.1, 0) + (p.angularFrequency n : ℝ) * x.2)) =
    Complex.re (_ * carrier (p.base.frequency n) (p.base.phase n) x)
  rw [← hphase, hc]
  have hi := invariant_eq_zeroSlice (h.corrected_invariant n) x.1 x.2
  have he := congrArg (fun v : ComplexVector =>
    (v i * carrier (p.base.frequency n) (p.base.phase n) x).re) hi.symm
  simp only [Prod.mk.eta] at he
  exact he

end SignedAngles

/-- The existing native angular inputs imply the smaller qualitative
record. Their quantitative-domain smoothness field is not extended or used. -/
noncomputable def signedAnglesOfInputs (p : PeriodizedSignedParameters Point I) (s : StripData
    Point)
    (request : ℕ → Cylinder → SignedWaveUpdate.Vec2) (m : ℕ → ℝ) (i₀ : I)
    (hθ : p.directions.angular = ((0 : Point), 1))
    (hf : ∀ n, p.base.frequency n * m n = (p.angularFrequency n : ℝ))
    (h : ∀ i, SignedWaveUpdate.AngularInputs (HarmonicWaveInteraction.productStrip s)
      p.directions p.base (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i)
        (p.normalMotion i) (p.action i) (p.cutoff i) m) : SignedAngles p s request := by
  refine ⟨m, ?_, ?_, ?_, hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have he := (h i₀).radius n
    simp only [hθ] at he
    exact he
  · intro n; simpa only [hθ] using (h i₀).radialField n
  · intro n; simpa only [hθ] using (h i₀).phase n
  · intro i n
    have he := (h i).matrix n
    simp only [hθ] at he
    exact he
  · intro i n
    have he := (h i).primary_target n
    simp only [hθ] at he
    exact he
  · intro n
    have he := (h i₀).signed_target n
    simp only [hθ] at he
    exact he
  · intro i n
    have he := (h i).mask n
    simp only [hθ] at he
    exact he
  · intro i n
    have he := (h i).fundamental n
    simp only [hθ] at he
    exact he
  · intro i n
    have he := (h i).cutoff n
    simp only [hθ] at he
    exact he

/-- All fields use the literal post-particular request.  The old state,
profile, and native data are not reselected. -/
structure SignedData {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (r₀ r₁ : ℝ) where
  /-- Mode supplied by `SignedData`. -/
  mode : ∀ l, ModeData ((p.signed l).copyData p.strip (p.signedRequest v c u))
    (HarmonicWaveInteraction.productStrip p.strip) (p.signed l).directions
      (LinearIsometryEquiv.refl ℝ Cylinder) U r₀ r₁
  /-- Angles of `SignedData`, of type `∀ l, SignedAngles (p.signed l) p.strip (p.signedRequest v
  c u)`. -/
  angles : ∀ l, SignedAngles (p.signed l) p.strip (p.signedRequest v c u)

theorem SignedData.block_regular {ι : Type} {p : CycleParameters ι} {v : CycleCoefficients ι}
    {c : Context Point} {u : State Point} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : SignedData p v c u U r₀ r₁) (l : ι) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.signedBlock v c u l).oscillation ∧
    OscillationPeriodic U.carrier (p.signedBlock v c u l).oscillation ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.signedBlock v c u l).oscillation := by
  unfold CycleParameters.signedBlock
  rw [(h.angles l).block_eq_mode]
  exact (h.mode l).regular

theorem SignedData.regular {ι : Type} {p : CycleParameters ι} {v : CycleCoefficients ι}
    {c : Context Point} {u : State Point} {coord r₀ r₁ : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} (h : SignedData p v c u U r₀ r₁) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.signedVelocity v c u) ∧
    OscillationPeriodic U.carrier (p.signedVelocity v c u) ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.signedVelocity v c u) :=
  ⟨finite_smooth _ _ (fun l => (h.block_regular l).1),
    finite_periodic _ _ (fun l => (h.block_regular l).2.1),
    finite_support _ _ (fun l => (h.block_regular l).2.2)⟩

end SignedCycle

/-- The qualitative oscillation fields of the actual next cycle state.
The intervening temporal, rank, and pressure-refresh operations preserve the
same oscillation by the literal recurrence. -/
theorem next_regular {ι : Type} {p : CorrectionStep.CycleParameters ι}
    {v : CorrectionStep.CycleCoefficients ι} {c : Context Point} {u : State Point}
    {coord r₀ r₁ : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    (hp : ParticularData p v c u U r₀ r₁) (hs : SignedData p v c u U r₀ r₁)
    (hu : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u.oscillation)
    (hper : CorrectionStep.OscillationPeriodic U.carrier u.oscillation)
    (hsup : WaveStateRegularity.WaveSupport U r₀ r₁ u.oscillation) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier)
      (p.next v c u).oscillation ∧
    CorrectionStep.OscillationPeriodic U.carrier (p.next v c u).oscillation ∧
    WaveStateRegularity.WaveSupport U r₀ r₁ (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact ⟨(hu.add hp.regular.1).add hs.regular.1,
    (hper.add hp.regular.2.1).add hs.regular.2.1,
    (hsup.add hp.regular.2.2).add hs.regular.2.2⟩

/-! ## Moving radial edges of the literal coefficients

At a flat radial boundary the coefficient need not have a zero germ.
Instead, its actual interior tensor bounds prove smoothness across that
boundary. The conclusions concern the original coefficient, whose exterior
zero values identify it with the constructed extension.
-/

section RadialEdges

open WaveEdgeExtension

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem literal_extension_eqOn {Ω : Set D} {ρ : D → ℝ} {a b : ℝ} {f : D → E}
    (hz : ∀ x ∈ Ω, x ∉ window ρ a b → f x = 0) :
    EqOn (extension ρ a b f) f Ω := by
  intro x hx
  by_cases hi : x ∈ window ρ a b
  · exact extension_inside ρ a b f hi
  · rw [extension_outside ρ a b f hi, hz x hx hi]

/-- The original, totalized coefficient has all zero edge tensors, from
its actual interior derivatives and its actual exterior values. -/
theorem literal_moving_regular {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f)
    (hz : ∀ x ∈ Ω, x ∉ window ρ a b → f x = 0) :
    ContDiffOn ℝ ∞ f Ω ∧
      ∀ n x, x ∈ Ω → (ρ x = a ∨ ρ x = b) → iteratedFDeriv ℝ n f x = 0 := by
  have he := literal_extension_eqOn hz
  refine ⟨(extension_contDiffOn hΩ hρ ha hab hcL hcR hf hB).congr (fun x hx => (he hx).symm), ?_⟩
  intro n x hx hedge
  have hg : extension ρ a b f =ᶠ[𝓝 x] f := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact he hy
  rw [← jets_eq_of_germ hg n]
  exact iteratedFDeriv_extension_edge hΩ hρ ha hab hcL hcR hf hB n hx hedge

/-- Apply the already proved native Gaussian derivative estimates to the
same literal coefficient. The constants are those in the native estimates;
no full-domain estimate or output smoothness is assumed. -/
theorem literal_native_regular {J : Type} {V : PrimaryCopyBounds.JetDomain J D}
    {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ} (hρ : ContDiffOn ℝ ∞ ρ Ω)
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    {A S : J → ℝ} {P : J → D → ℝ} {f : J → D → E}
    (hf : PrimaryCopyBounds.NativeJets V
      (fun i x => A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x) f)
    (hA : ∀ i, 0 ≤ A i) (hS : ∀ i, 1 ≤ S i)
    (hP : ∀ i, ContinuousOn (P i) Ω) (hP0 : ∀ i x, x ∈ Ω → 0 ≤ P i x)
    (hdom : ∀ i, windowDomain Ω ρ a b ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain Ω ρ a b →
      V.growth i x ≤ S i * edgeGrowth ρ a b x ^ q)
    (hz : ∀ i x, x ∈ Ω → x ∉ window ρ a b → f i x = 0) :
    ∀ i, ContDiffOn ℝ ∞ (f i) Ω ∧
      ∀ n x, x ∈ Ω → (ρ x = a ∨ ρ x = b) → iteratedFDeriv ℝ n (f i) x = 0 := by
  intro i
  have hB := boundaryControls_of_majorants hΩ hρ (hP i) ha hab hcL hcR
    (native_jet_majorant hf hA hS hP0 hdom q hG i)
  exact literal_moving_regular hΩ hρ ha hab (half_pos hcL) (half_pos hcR)
    ((hf.smooth i).mono (hdom i)) hB (hz i)

end RadialEdges

end NavierStokes.ActualWaveRegularity
