/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSupportPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEdgeExtension

/-!
# Concrete qualitative data for the actual correction waves

All native data below use the initializer's existing choice. A common-band
translation is interpreted on a native cover only when the common index is
at most the native index. The inactive bands are handled using actual zero
germs; no periodicity of an unused unmasked phase is imposed on those bands.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualWaveRegularityData

open Set Function Filter WeightedClasses HarmonicCalculus
open CorrectionInitialization CommonCoverSolve TorusInverse
open scoped Topology ContDiff BigOperators

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Full point: an abbreviation for `Point × ℝ`. -/
abbrev FullPoint := Point × ℝ
/-- Index: an abbreviation for `ActualSignedStageControls.SignedLabel B N0`. -/
abbrev Index (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0

variable {B N0 : ℕ}

/-- Ordered, given by `CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex
ActualPrimary.h (BaseChartJets.cellBand l.1)`. -/
noncomputable def Ordered (l : Index B N0) (n : ℕ) : Prop :=
  CommonWindow.index ActualPrimary.h n ≤
    ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1)

/-- Deck index, given by `coverIndex ((ActualPrimary.chartGeometry n l.2 l.1).gap) m`. -/
noncomputable def deckIndex (l : Index B N0) (n : ℕ) (m : Frequency) : Frequency :=
  coverIndex ((ActualPrimary.chartGeometry n l.2 l.1).gap) m

/-- Deck permutation, given by `Equiv.addRight (deckIndex l n m)`. -/
noncomputable def deckPermutation (l : Index B N0) (n : ℕ) (m : Frequency) : Frequency ≃ Frequency
    :=
  Equiv.addRight (deckIndex l n m)

theorem nativePoint_ordered (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (k : Frequency) (x : FullPoint) :
    ActualSignedStageControls.nativePoint l n k x =
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1),
        (ActualPrimary.chartGeometry n l.2 l.1).coordinates k x.1.2.2) := by
  apply Prod.ext
  · rfl
  · exact ActualPrimary.chartGeometry_coordinates n l.2 l.1 hn k x.1.2.2

theorem nativePoint_deck (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (k m : Frequency) (x : FullPoint) :
    ActualSignedStageControls.nativePoint l n (deckPermutation l n m k)
      (x + ActualWaveRegularity.deckShift m) =
        ActualSignedStageControls.nativePoint l n k x := by
  rw [nativePoint_ordered l n hn, nativePoint_ordered l n hn]
  apply Prod.ext
  · simp only [ActualPrimary.nativeSlow, ActualPrimary.toAbsolute,
      ActualWaveRegularity.deckShift, Prod.add_def, add_zero]
  · change (ActualPrimary.chartGeometry n l.2 l.1).coordinates
      (k + coverIndex (ActualPrimary.chartGeometry n l.2 l.1).gap m)
      (x.1.2.2 + TorusAverages.latticePoint m) = _
    exact Geometry.coordinates_deck _ k m x.1.2.2

theorem cutoff_deck (l : Index B N0) (n : ℕ) (hn : Ordered l n)
    (k m : Frequency) (x : FullPoint) :
    ActualSignedStageControls.cutoff l (deckPermutation l n m k) n
      (x + ActualWaveRegularity.deckShift m) = ActualSignedStageControls.cutoff l k n x := by
  simp only [ActualSignedStageControls.cutoff, nativePoint_deck l n hn]

theorem signed_amplitude_deck (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (hn : Ordered l n)
    (k m : Frequency) (x : FullPoint)
    (hR : request n (x + ActualWaveRegularity.deckShift m) = request n x) :
    ((ActualSignedStageControls.parameters l).copyData s request).amplitude n
      (deckPermutation l n m k) (x + ActualWaveRegularity.deckShift m) =
        ((ActualSignedStageControls.parameters l).copyData s request).amplitude n k x := by
  apply ActualWaveRegularity.signed_amplitude_deck
  · simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.matrix,
      nativePoint_deck l n hn]
  · simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.target,
      nativePoint_deck l n hn]
  · exact hR
  · simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.mask,
      nativePoint_deck l n hn]
  · simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.fundamental,
      nativePoint_deck l n hn]

theorem fullRequest_deck (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) (m : Frequency) (x : FullPoint) :
    LocalSignedRequest.fullRequest s P coord c u n (x + ActualWaveRegularity.deckShift m) =
      LocalSignedRequest.fullRequest s P coord c u n x := by
  have he := LocalSignedRequest.fullRequest_torus_frozen s P coord c u
    (TorusAverages.latticePoint m) n x (1 : ℝ)
  simp only [one_smul] at he
  exact he

theorem signed_request_amplitude_deck (l : Index B N0) (s : StripData Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (n : ℕ) (hn : Ordered l n)
    (k m : Frequency) (x : FullPoint) :
    ((ActualSignedStageControls.parameters l).copyData s
      (LocalSignedRequest.fullRequest s P coord c u)).amplitude n
      (deckPermutation l n m k) (x + ActualWaveRegularity.deckShift m) =
        ((ActualSignedStageControls.parameters l).copyData s
          (LocalSignedRequest.fullRequest s P coord c u)).amplitude n k x :=
  signed_amplitude_deck l s _ n hn k m x (fullRequest_deck s P coord c u n m x)

theorem clock_deck (l : Index B N0) (n : ℕ) (hn : Ordered l n) (Y : Plane) (m : Frequency) :
    PeriodicPhaseAssembly.periodicClock (ActualPrimary.geometry l.2 l.1)
      (ActualPrimary.clockWindow l.1).cutoff
      ((coverPower (CommonWindow.index ActualPrimary.h n)).symm (Y + TorusAverages.latticePoint m))
          =
    PeriodicPhaseAssembly.periodicClock (ActualPrimary.geometry l.2 l.1)
      (ActualPrimary.clockWindow l.1).cutoff
      ((coverPower (CommonWindow.index ActualPrimary.h n)).symm Y) := by
  rw [ActualPrimary.periodicClock_toAbsolute l.2 l.1 n hn,
    ActualPrimary.periodicClock_toAbsolute l.2 l.1 n hn,
    map_add, coverPower_lattice, PeriodicPhaseAssembly.periodicClock_periodic]

theorem phase_deck (l : Index B N0) (n : ℕ) (hn : Ordered l n) (m : Frequency) :
    ActualWaveRegularity.TranslationOn Set.univ (ActualWaveRegularity.deckShift m)
      ((ActualSignedStageControls.parameters l).base.phase n) := by
  intro x _
  simp only [ActualSignedStageControls.parameters, ActualPrimary.chartCoefficients,
    ActualPrimary.absolutePhase, ActualPrimary.periodicPhase,
    ActualPrimary.nativeSlow, ActualPrimary.toAbsolute, ActualWaveRegularity.deckShift,
    Prod.add_def, add_zero]
  have hc := clock_deck l n hn x.1.2.2 m
  simp only [Prod.add_def, TorusAverages.latticePoint] at hc
  rw [hc]

theorem radius_deck (l : Index B N0) (n : ℕ) (m : Frequency) :
    ActualWaveRegularity.TranslationOn Set.univ (ActualWaveRegularity.deckShift m)
      ((ActualSignedStageControls.parameters l).base.radius n) := by
  intro x _
  change x.1.1 + 0 = x.1.1
  exact add_zero _

theorem radial_deck (l : Index B N0) (n : ℕ) (m : Frequency) :
    ActualWaveRegularity.TranslationOn Set.univ (ActualWaveRegularity.deckShift m)
      ((ActualSignedStageControls.parameters l).directions.radialField n) := by
  intro x _
  change _ + _ • (RadialPullback.radialJacobian _ (x.1.1 + 0) • _) =
    _ + _ • (RadialPullback.radialJacobian _ x.1.1 • _)
  rw [add_zero]

/-- Signed angles, bundling `slope`, `radius`, `radial`, `phase` and the required compatibility
proofs. -/
noncomputable def signedAngles (l : Index B N0) (s : StripData Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) :
    ActualWaveRegularity.SignedAngles (ActualSignedStageControls.parameters l) s
      (LocalSignedRequest.fullRequest s P coord c u) where
  slope n := (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1 : ℝ) / ChartScales.carrier ActualPrimary.h n
  radius n := by
    intro x t
    change x.1.1 + t * 0 = x.1.1
    ring
  radial n := by
    intro x t
    change _ + _ • (RadialPullback.radialJacobian _ (x.1.1 + t * 0) • _) =
      _ + _ • (RadialPullback.radialJacobian _ x.1.1 • _)
    rw [mul_zero, add_zero]
  phase n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualPrimary.chartCoefficients,
      ActualPrimary.absolutePhase, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero,
      Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one]
    ring
  frequency_slope n := by
    exact mul_div_cancel₀ _ (ActualPrimary.chartCoefficients_frequency_pos l.2 l.1 n).ne'
  matrix i n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.matrix,
      ActualSignedStageControls.nativePoint_angle]
  target i n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.target,
      ActualSignedStageControls.nativePoint_angle]
  request n := LocalSignedRequest.fullRequest_angle_frozen s P coord c u n
  mask i n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.mask,
      ActualSignedStageControls.nativePoint_angle]
  fundamental i n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.fundamental,
      ActualSignedStageControls.nativePoint_angle]
  cutoff i n := by
    intro x t
    simp only [ActualSignedStageControls.parameters, ActualSignedStageControls.cutoff,
      ActualSignedStageControls.nativePoint_angle]

/-! ## The actual slow mask selects an ordered native cover -/

theorem near_of_native_band (l : Index B N0) (n : ℕ) {p : PhaseCalculus.Slow}
    (ht : 0 < p.2.2)
    (hq0 : SimilarityHomogeneity.chartQ ActualPrimary.h p ∈ Ioo (1 / 2 : ℝ) 2)
    (hq : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.1)) p) ∈ Icc (1 / 2 : ℝ) 2) :
    ActualPrimaryBounds.near (l.2, l.1) n := by
  let q := ChartScales.Q n * SimilarityHomogeneity.chartQ ActualPrimary.h p
  have hqpos : 0 < q := mul_pos (ChartScales.Q_pos _) (by linarith [hq0.1])
  have he : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.1)) p) =
      q / ChartScales.Q (BaseChartJets.cellBand l.1) := by
    rw [ActualSignedGeometry.slowChange_eq_transition (ChartScales.Q_pos _) (ChartScales.Q_pos _),
      SimilarityHomogeneity.chartQ_transition ActualPrimary.outgoing.data.h_pos
        ActualPrimary.outgoing.data.h_lt_half (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht]
    dsimp [q]
    ring
  rw [he] at hq
  have hn := PhysicalWaveSum.logCoordinate_in_band hqpos
    (show ChartScales.Q n / 2 ≤ q by dsimp [q]; nlinarith [ChartScales.Q_pos n, hq0.1])
    (show q ≤ 2 * ChartScales.Q n by dsimp [q]; nlinarith [ChartScales.Q_pos n, hq0.2])
  have hL := PhysicalWaveSum.logCoordinate_in_band hqpos
    (show ChartScales.Q (BaseChartJets.cellBand l.1) / 2 ≤ q by
      have hh := (le_div_iff₀ (ChartScales.Q_pos _)).mp hq.1
      linarith)
    ((div_le_iff₀ (ChartScales.Q_pos _)).mp hq.2)
  have hnm : n ≤ BaseChartJets.cellBand l.1 + 2 := by
    have hh : (n : ℝ) ≤ (BaseChartJets.cellBand l.1 : ℝ) + 2 := by linarith [hn.1, hL.2]
    exact_mod_cast hh
  have hmn : BaseChartJets.cellBand l.1 ≤ n + 2 := by
    have hh : (BaseChartJets.cellBand l.1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [hL.1, hn.2]
    exact_mod_cast hh
  have hm4 : 4 ≤ BaseChartJets.cellBand l.1 :=
    ((ActualPrimary.choice B N0).prepared.large _ l.1.property).four_le
  change 1 ≤ n ∧ BaseChartJets.cellBand l.1 ∈ CommonWindow.levels n
  refine ⟨by omega, ?_⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_Icc.mpr ⟨max_le (by omega) (by omega), hmn⟩

theorem ordered_of_native_band (l : Index B N0) (n : ℕ) {p : PhaseCalculus.Slow}
    (ht : 0 < p.2.2)
    (hq0 : SimilarityHomogeneity.chartQ ActualPrimary.h p ∈ Ioo (1 / 2 : ℝ) 2)
    (hq : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.1)) p) ∈ Icc (1 / 2 : ℝ) 2) :
    Ordered l n := CommonWindow.index_le (near_of_native_band l n ht hq0 hq).2

theorem ordered_of_mask (l : Index B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hm : ActualSignedStageControls.mask l k n x ≠ 0) : Ordered l n := by
  have hx0 : 0 < x.1.2.1.1 ∧
      SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) x.1.2.1 ∈ Ioo (1 / 2 : ℝ) 2 := hx.1
  have hq := ActualPrimary.spatialMask_q_range l.1
    (ActualSignedStageControls.nativePoint l n k x).1 hm
  change SimilarityHomogeneity.chartQ ActualPrimary.h
    (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1)) ∈ _ at hq
  rw [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange] at hq
  exact ordered_of_native_band l n (p := BaseContextAssembly.slowCoordinates x.1)
    hx0.1 hx0.2 ⟨hq.1.le, hq.2.le⟩

theorem mask_zero_of_not_ordered (l : Index B N0) (n : ℕ) (hn : ¬Ordered l n)
    (k : Frequency) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    ActualSignedStageControls.mask l k n x = 0 :=
  Classical.not_not.mp (fun hm => hn (ordered_of_mask l n k hx hm))

theorem mask_zero_germ_of_not_ordered (l : Index B N0) (n : ℕ) (hn : ¬Ordered l n)
    (k : Frequency) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    ActualSignedStageControls.mask l k n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion).mem_nhds hx]
    with y hy
  exact mask_zero_of_not_ordered l n hn k hy

/-- The actual three assembled fields vanish on inactive common bands.
The proof uses raw zero germs before applying the curl and copy sum. -/
theorem signed_zero_germs_of_not_ordered (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (n : ℕ) (hn : ¬Ordered l n) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    let a := (ActualSignedStageControls.parameters l).copyData s request
    ((a.commonCorrected (HarmonicWaveInteraction.productStrip s)
      (ActualSignedStageControls.parameters l).directions).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGaussian (ActualSignedStageControls.parameters l).directions n =ᶠ[𝓝 x] fun _ => 0) :=
        by
  dsimp only
  apply LabelSupportPreservation.common_zero_germs_of_native _ (ActualSignedStageControls.cells l)
    (ActualSignedStageControls.cutoff_support l) _ _
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro k _
    right
    constructor
    · filter_upwards [mask_zero_germ_of_not_ordered l n hn k hx] with y hy
      exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).1
    · filter_upwards [mask_zero_germ_of_not_ordered l n hn k hx] with y hy
      exact ((ActualSignedStageControls.parameters l).raw_zero_of_mask request n k y hy).2

theorem signed_block_periodic (l : Index B N0) (s : StripData Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) :
    CorrectionStep.OscillationPeriodic ActualPrimary.standardRegion.carrier
      ((ActualSignedStageControls.parameters l).exactBlock s
        (LocalSignedRequest.fullRequest s P coord c u)).oscillation := by
  rw [(signedAngles l s P coord c u).block_eq_mode]
  intro n R t ht θ Y k
  let x : FullPoint := ((R, (t, Y)), θ)
  have hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨ht, mem_univ _⟩
  have hy : x + ActualWaveRegularity.deckShift k ∈
      ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := by
    change (t + 0) ∈ ActualPrimary.standardRegion.carrier ∧ _
    exact ⟨by simpa only [add_zero] using ht, mem_univ _⟩
  by_cases hn : Ordered l n
  · have hp := ActualWaveRegularity.common_velocity_translation
      ((ActualSignedStageControls.parameters l).copyData s (LocalSignedRequest.fullRequest s P
          coord c u))
      (HarmonicWaveInteraction.productStrip s) (ActualSignedStageControls.parameters l).directions
      (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion) n
      (fun z _ => radius_deck l n k z (mem_univ _))
      (fun z _ => radial_deck l n k z (mem_univ _))
      (fun z _ => phase_deck l n hn k z (mem_univ _))
      (ActualWaveRegularity.common_amplitude_translation _ n (deckPermutation l n k)
        (fun i z _ => cutoff_deck l n hn i k z)
        (fun i z _ => signed_request_amplitude_deck l s P coord c u n hn i k z)) x hx
    funext i
    change (vectorMode _ _ _ (((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ)) i).re = _
    have he : ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) =
        x + ActualWaveRegularity.deckShift k := by
      simp only [x, ActualWaveRegularity.deckShift, Prod.add_def, add_zero]
    rw [he, hp]
    rfl
  · have h0 := (signed_zero_germs_of_not_ordered l s
      (LocalSignedRequest.fullRequest s P coord c u) n hn hx).1.eq_of_nhds
    have h1 := (signed_zero_germs_of_not_ordered l s
      (LocalSignedRequest.fullRequest s P coord c u) n hn hy).1.eq_of_nhds
    have he : ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) =
        x + ActualWaveRegularity.deckShift k := by
      simp only [x, ActualWaveRegularity.deckShift, Prod.add_def, add_zero]
    funext i
    change (vectorMode _ _ _ (((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ)) i).re =
      (vectorMode _ _ _ x i).re
    simp only [he, vectorMode, HarmonicCalculus.mode, h0, h1, Pi.zero_apply, zero_mul]

/-! ## The actual full-domain phase patches -/

/-- Signed phase patch as an element of `Set FullPoint`. -/
noncomputable def signedPhasePatch (l : Index B N0) (n : ℕ) (k : Frequency) : Set FullPoint :=
  {x | (ActualSignedStageControls.nativePoint l n k x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal
        (ActualPrimary.choice B N0).prepared.N).carrier l.1 ∧
    ActualSignedStageControls.nativeTime l n k x ∈ Ioo (0 : ℝ) 1}

theorem signedPhasePatch_open (l : Index B N0) (n : ℕ) (k : Frequency) :
    IsOpen (signedPhasePatch l n k) :=
  (((PrimaryGeometryAssembly.domain ActualPrimary.nominal
    (ActualPrimary.choice B N0).prepared.N).isOpen l.1).preimage
      (ActualSignedStageControls.nativePoint_smooth l n k).continuous.fst).inter
    (isOpen_Ioo.preimage (ActualSignedStageControls.nativeTime_smooth l n k).continuous)

theorem native_time_pos (l : Index B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    0 < (ActualSignedStageControls.nativePoint l n k x).1.2.2 := by
  change 0 < ChartScales.Q n * x.1.2.1.1 / ChartScales.Q (BaseChartJets.cellBand l.1)
  exact div_pos (mul_pos (ChartScales.Q_pos n) (ActualPrimary.standardRegion.time_pos _ hx.1))
    (ChartScales.Q_pos _)

theorem mask_zero_germ_outside_carrier (l : Index B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hc : (ActualSignedStageControls.nativePoint l n k x).1 ∉
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal
        (ActualPrimary.choice B N0).prepared.N).carrier l.1) :
    ActualSignedStageControls.mask l k n =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : (ActualSignedStageControls.nativePoint l n k x).1 ∉
      tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.1)
        (PrimaryGeometryAssembly.label ActualPrimary.nominal l.1).2) := by
    intro hs
    exact hc (PrimaryGeometryAssembly.native_support_in_carrier ActualPrimary.nominal l.1
      ⟨hs, native_time_pos l n k hx⟩)
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (ActualSignedStageControls.nativePoint_smooth l n k).continuous.fst.continuousAt
  filter_upwards [hz] with y hy
  change PrimaryRepresentatives.nativeMask _ _ (ActualSignedStageControls.nativePoint l n k y).1 =
      0 at hy
  change ActualPrimary.spatialMask l.1 (ActualSignedStageControls.nativePoint l n k y).1 = 0
  rw [ActualPrimary.spatialMask_eq, hy, mul_zero]

/-- Every point of the full slow domain either lies in the genuine
positive-radius, interior-clock patch, or has a zero localized raw germ. -/
theorem signed_patch_cover (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    x ∈ signedPhasePatch l n k ∨
      ((((ActualSignedStageControls.parameters l).copyData s request).localized k).amplitude n
        =ᶠ[𝓝 x] fun _ => 0) := by
  by_cases hc : (ActualSignedStageControls.nativePoint l n k x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal
        (ActualPrimary.choice B N0).prepared.N).carrier l.1
  · by_cases ht : ActualSignedStageControls.nativeTime l n k x ∈ Ioo (0 : ℝ) 1
    · exact Or.inl ⟨hc, ht⟩
    · right
      apply (((ActualSignedStageControls.parameters l).copyData s request).localized_zero_germs
          ?_).1
      apply ActualSignedStageControls.cutoff_zero_germ_outside_time l n k
      intro htime
      exact ht ⟨by linarith [htime.1], by linarith [htime.2]⟩
  · exact Or.inr (((ActualSignedStageControls.parameters l).localized_zero_of_mask request
      (mask_zero_germ_outside_carrier l n k hx hc)).1)

theorem signedPhasePatch_positive (l : Index B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩
      signedPhasePatch l n k) : x ∈ ActualPrimaryCoherence.positiveRadialChart := by
  have hp := (ActualPrimary.choice B N0).prepared.radius_pos l.1
    (ActualSignedStageControls.nativePoint l n k x).1 hx.2.1
  have hq := Real.sqrt_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand l.1))
  have hn := Real.sqrt_pos.mpr (ChartScales.Q_pos n)
  change 0 < Real.sqrt (ChartScales.Q n) * x.1.1 /
    Real.sqrt (ChartScales.Q (BaseChartJets.cellBand l.1)) at hp
  have hmul := (div_pos_iff_of_pos_right hq).mp hp
  exact ⟨(mul_pos_iff_of_pos_left hn).mp hmul, ActualPrimary.standardRegion.time_pos _ hx.1.1⟩

theorem signed_phase_smooth (l : Index B N0) (n : ℕ) (k : Frequency) :
    ContDiffOn ℝ ∞ ((ActualSignedStageControls.parameters l).base.phase n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩ signedPhasePatch l n k) :=
  (ActualPrimaryDynamics.phase_smooth l.2 l.1 n).mono (fun _ hx => signedPhasePatch_positive l n k
      hx)

theorem signed_geometry (l : Index B N0) (n : ℕ) (k : Frequency) :
    CurlClassBounds.CylindricalGeometry
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩ signedPhasePatch l n k)
      ((ActualSignedStageControls.parameters l).base.radius n)
      ((ActualSignedStageControls.parameters l).directions.radialField n)
      (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
      ((ActualSignedStageControls.parameters l).directions.axialField
        (HarmonicWaveInteraction.productStrip ActualPrimaryBounds.strip) n) :=
  LocalizedCurlRealization.geometry_restrict
    (ActualPrimaryCoherence.piece_geometry ActualPrimary.standardRegion B n)
    ((ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion).inter
      (signedPhasePatch_open l n k)) (fun _ hx => signedPhasePatch_positive l n k hx)

theorem signed_normal_ne (l : Index B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩
      signedPhasePatch l n k) :
    (ActualSignedStageControls.parameters l).base.normal
      (HarmonicWaveInteraction.productStrip ActualPrimaryBounds.strip)
      (ActualSignedStageControls.parameters l).directions n x ≠ 0 :=
  ActualPrimaryCoherence.piece_normal_ne ActualPrimary.standardRegion l.2 l.1 n
    (signedPhasePatch_positive l n k hx)

/-! ## Literal exterior values of the signed quotient -/

theorem raw_zero_of_target (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (k : Frequency)
    (x : FullPoint) (ht : ActualSignedStageControls.target l k n x = 0) :
    ((ActualSignedStageControls.parameters l).copyData s request).amplitude n k x = 0 ∧
    ((ActualSignedStageControls.parameters l).copyData s request).pressure n k x = 0 := by
  have hamp (H : SignedWaveUpdate.Mat2) : SmoothCovariance.amplitudes H 0 = 0 := by
    ext j
    fin_cases j <;> simp [SmoothCovariance.amplitudes, SmoothCovariance.weights,
      SmoothCovariance.cramerNumerator]
  simp [CorrectionStep.PeriodizedSignedParameters.copyData,
    CorrectionStep.PeriodizedSignedParameters.native, CorrectionStep.SignedParameters.coefficients,
    SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    ActualSignedStageControls.parameters, ht, SignedCovariance.increment, hamp,
    ParticularWaveBounds.projectedPressure, TangentProjection.pressureCoefficient]

theorem target_zero_outside {p : PhaseCalculus.Slow}
    (ht : 0 < p.2.2) (hr : 0 < p.1)
    (hout : PrimaryTargetBounds.profileRadius ActualPrimary.h p ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    PrimaryTargetBounds.actualTarget ActualPrimary.modulation p = 0 := by
  have hp := PrimaryTargetBounds.profileRadius_pos (F := ActualPrimary.outgoing) ht hr
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hasq : (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)^2 =
      2 * NominalConeAssembly.activeLeft ActualPrimary.nominal := by
    exact Real.sq_sqrt (mul_pos (by norm_num) (NominalConeAssembly.activeLeft_pos _)).le
  have hbsq : (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)^2 =
      2 * NominalConeAssembly.activeRight ActualPrimary.nominal := by
    exact Real.sq_sqrt (mul_pos (by norm_num) (LeadingStressWeights.activeRight_pos _)).le
  have hn : (BaseChartJets.normalizedCoordinates ActualPrimary.h p).2.1 ∉
      Ioo (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal) := by
    intro h
    rw [← PrimaryTargetBounds.profileRadius_sq (F := ActualPrimary.outgoing) ht] at h
    exact hout ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
  have hz := PrimaryTargetBounds.stress_zero_of_not_active ActualPrimary.modulation
    (ProfileSpectralCone.normalized_X_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half ht hr)
    (abs_le.mp (BaseChartJets.normalizedCoordinates_eta ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half ht).le) hn
  simp only [PrimaryTargetBounds.actualTarget, hz, smul_zero]

/-- Radius, given by `x.1.1 / VariableGaugeMean.qLength (2 * ActualPrimary.h) x.1.2.1`. -/
noncomputable def radius (x : FullPoint) : ℝ :=
  x.1.1 / VariableGaugeMean.qLength (2 * ActualPrimary.h) x.1.2.1

theorem radius_smooth : ContDiffOn ℝ ∞ radius
    (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :=
  (LocalSignedRequest.profileMap_smooth ActualPrimary.standardRegion).fst.comp
    contDiffOn_fst (fun _ hx => hx.1)

theorem native_radius (l : Index B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hr : 0 < x.1.1) :
    PrimaryTargetBounds.profileRadius ActualPrimary.h
      (ActualSignedStageControls.nativePoint l n k x).1 = radius x :=
  ActualPrimaryCoherence.amplitudeRadius_chart l.1 n
    (ActualPrimary.standardRegion.time_pos _ hx.1) hr

theorem signed_raw_zero_outside (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    ((ActualSignedStageControls.parameters l).copyData s request).amplitude n k x = 0 ∧
    ((ActualSignedStageControls.parameters l).copyData s request).pressure n k x = 0 := by
  by_cases hm : ActualSignedStageControls.mask l k n x = 0
  · exact (ActualSignedStageControls.parameters l).raw_zero_of_mask request n k x hm
  have hc := ActualPrimary.spatialMask_carrier l.1 (native_time_pos l n k hx) hm
  have hp := (ActualPrimary.choice B N0).prepared.radius_pos l.1 _ hc
  have hq := Real.sqrt_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand l.1))
  have hn := Real.sqrt_pos.mpr (ChartScales.Q_pos n)
  have hr : 0 < x.1.1 := by
    change 0 < Real.sqrt (ChartScales.Q n) * x.1.1 /
      Real.sqrt (ChartScales.Q (BaseChartJets.cellBand l.1)) at hp
    exact (mul_pos_iff_of_pos_left hn).mp ((div_pos_iff_of_pos_right hq).mp hp)
  have hnp := (ActualPrimary.choice B N0).prepared.radius_pos l.1 _ hc
  have hzero := target_zero_outside (native_time_pos l n k hx) hnp
    (by rwa [native_radius l n k hx hr])
  apply raw_zero_of_target l s request n k x
  simp only [ActualSignedStageControls.target, hzero, PiLp.zero_apply]
  funext q
  simp

theorem strip_subset_fullDomain : ActualSignedStageControls.fullStrip.domain ⊆
    ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := by
  intro x hx
  exact ⟨((BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
      x.1).mp hx).1,
    mem_univ _⟩

theorem mask_zero_germ_outside_band (l : Index B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hq : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedStageControls.nativePoint l n k x).1 ∉ Icc (1 / 2 : ℝ) 2) :
    ActualSignedStageControls.mask l k n =ᶠ[𝓝 x] fun _ => 0 := by
  have hs := (ActualSignedStageControls.nativePoint_smooth l n k).continuous.fst
  have hc : ContinuousAt (fun y : FullPoint => SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedStageControls.nativePoint l n k y).1) x :=
    (SimilarityCoordinates.coordinateQ_smooth
      (by linarith [ActualPrimary.outgoing.data.h_pos] : 0 < 2 * ActualPrimary.h)
      (by linarith [ActualPrimary.outgoing.data.h_lt_half] : 2 * ActualPrimary.h < 1)
      (native_time_pos l n k hx)).continuousAt.comp
        (hs.snd.snd.prodMk hs.snd.fst).continuousAt
  have hqg := hc (isClosed_Icc.isOpen_compl.mem_nhds hq)
  filter_upwards [hqg] with y hy
  have hz : SquaredPartition.dyadicProfile (SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedStageControls.nativePoint l n k y).1) = 0 := by
    by_contra hm
    have hm' : SimilarityHomogeneity.chartQ ActualPrimary.h
        (ActualSignedStageControls.nativePoint l n k y).1 ∈ support SquaredPartition.dyadicProfile
            := hm
    rw [SquaredPartition.dyadicProfile_support] at hm'
    exact hy ⟨hm'.1.le, hm'.2.le⟩
  change ActualPrimary.spatialMask l.1 (ActualSignedStageControls.nativePoint l n k y).1 = 0
  rw [ActualPrimary.spatialMask_eq]
  change SquaredPartition.dyadicProfile (SimilarityHomogeneity.chartQ ActualPrimary.h
    (ActualSignedStageControls.nativePoint l n k y).1) * _ = 0
  rw [hz, zero_mul]

/-- Actual quantitative cells cover every nonzero localized copy on the
whole open strip. Closed dyadic, transverse and temporal endpoints remain
in the cell; only genuine zero neighborhoods are used in the alternatives. -/
theorem signed_phaseCell_or_zero (l : Index B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hx : x ∈ ActualSignedStageControls.fullStrip.domain) :
    x ∈ ActualSignedStageControls.phaseCell l n k ∨
      (ActualSignedStageControls.cutoff l k n =ᶠ[𝓝 x] fun _ => 0) ∨
      (ActualSignedStageControls.mask l k n =ᶠ[𝓝 x] fun _ => 0) := by
  have hfull := strip_subset_fullDomain hx
  by_cases hq : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedStageControls.nativePoint l n k x).1 ∈ Icc (1 / 2 : ℝ) 2
  · have hq' := hq
    change SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n x.1)) ∈ _ at hq'
    rw [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange] at hq'
    have hbase : 0 < x.1.2.1.1 ∧
        SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) x.1.2.1 ∈ Ioo (1 / 2 : ℝ) 2 :=
            hfull.1
    have hn := near_of_native_band l n (p := BaseContextAssembly.slowCoordinates x.1)
      hbase.1 hbase.2 hq'
    by_cases hc : (ActualSignedStageControls.nativePoint l n k x).1 ∈
        (PrimaryGeometryAssembly.domain ActualPrimary.nominal
          (ActualPrimary.choice B N0).prepared.N).carrier l.1
    · by_cases hk : x ∈ (ActualSignedStageControls.cells l).carrier n k
      · by_cases ht : ActualSignedStageControls.nativeTime l n k x ∈ Icc (1 / 10 : ℝ) (9 / 10)
        · left
          have he := congrFun (ActualSignedStageControls.nativePoint_eq_fullCopy l n k hn) x
          refine ⟨⟨hn, ?_, ?_, ?_⟩, ht⟩
          · simpa only [← he] using hc
          · simpa only [← he] using (ActualSignedStageControls.cells_mem l n k x).mp hk
          · simpa only [← he] using hq
        · exact Or.inr (Or.inl (ActualSignedStageControls.cutoff_zero_germ_outside_time l n k ht))
      · exact Or.inr (Or.inl (PeriodizedWaveBounds.zero_germ_of_support
          ((ActualSignedStageControls.cells l).closed n k)
          (ActualSignedStageControls.cutoff_support l n k) hk))
    · exact Or.inr (Or.inr (mask_zero_germ_outside_carrier l n k hfull hc))
  · exact Or.inr (Or.inr (mask_zero_germ_outside_band l n k hfull hq))

/-! ## The actual strip weight gives all zero edge tensors -/

theorem strip_domain_eq : ActualSignedStageControls.fullStrip.domain =
    WaveEdgeExtension.windowDomain (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
      radius (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  ext x
  rw [show x ∈ ActualSignedStageControls.fullStrip.domain ↔
      x.1 ∈ (BaseContextAssembly.nativeStrip ActualPrimary.nominal
          ActualPrimary.standardRegion).domain from Iff.rfl,
    BaseContextAssembly.nativeStrip_mem]
  have hr : PrimaryTargetBounds.profileRadius ActualPrimary.h
      (BaseContextAssembly.slowCoordinates x.1) = radius x := by
    unfold PrimaryTargetBounds.profileRadius radius VariableGaugeMean.qLength
    rw [BaseChartJets.normalizedCoordinates_eq]
    rfl
  rw [hr]
  change (x.1.2.1 ∈ ActualPrimary.standardRegion.carrier ∧
      radius x ∈ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) ↔
    ((x.1.2.1 ∈ ActualPrimary.standardRegion.carrier ∧ True) ∧
      radius x ∈ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))
  tauto

theorem strip_zeta (x : FullPoint) : ActualSignedStageControls.fullStrip.zeta x =
    WaveEdgeExtension.flatWeight radius (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      (FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) 1 x := rfl

theorem strip_growth (n : ℕ) (x : FullPoint) :
    ActualSignedStageControls.fullStrip.growth n x =
      ActualSignedStageControls.fullStrip.slow n *
        WaveEdgeExtension.edgeGrowth radius (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x := rfl

/-- This uses the actual product weight and actual strip growth. There
is no boundary-continuity premise and no change to the given function. -/
theorem full_regular_of_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (f n) (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) ∧
      ∀ m x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
        (radius x = PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
          radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        iteratedFDeriv ℝ m (f n) x = 0 := by
  have hb : WaveEdgeExtension.BoundaryControls
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) radius
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      ((FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) / 2) (1 / 2) (f n) := by
    apply WaveEdgeExtension.boundaryControls_of_majorants
      (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion) radius_smooth
      (continuousOn_const (c := (1 : ℝ)))
      (PrimaryTargetBounds.leftRadius_pos _) (PrimaryTargetBounds.radii_ordered _)
      (div_pos (FinalSlowBase.edgeExponent_pos _) (by norm_num)) zero_lt_one
    intro m
    obtain ⟨C, hC, p, hbound⟩ := hf.bounds m
    refine ⟨C * ActualSignedStageControls.fullStrip.epsilon n ^ α *
      ActualSignedStageControls.fullStrip.slow n ^ p,
      mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos
        (ActualSignedStageControls.fullStrip.epsilon_pos n) α).le)
        (pow_nonneg (zero_le_one.trans (ActualSignedStageControls.fullStrip.one_le_slow n)) p), p,
            ?_⟩
    intro x hx
    have hh := hbound n x (by rwa [strip_domain_eq]) m le_rfl
    simp only [majorant, strip_growth, strip_zeta, mul_pow] at hh
    convert! hh using 1
    ring
  exact ActualWaveRegularity.literal_moving_regular
    (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion) radius_smooth
    (PrimaryTargetBounds.leftRadius_pos _) (PrimaryTargetBounds.radii_ordered _)
    (half_pos (div_pos (FinalSlowBase.edgeExponent_pos _) (by norm_num))) (by norm_num)
    (by simpa only [← strip_domain_eq] using hf.smooth n) hb (hz n)

theorem full_regular_of_envelope_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : Index B N0) {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (f n) (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) ∧
      ∀ m x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
        (radius x = PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
          radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        iteratedFDeriv ℝ m (f n) x = 0 := by
  apply full_regular_of_class
    (hf.mono_weight (fun _ _ _ => Real.sqrt_nonneg _) (fun m x _ => ?_)) hz n
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
    (ActualPrimaryBounds.fullEnvelope_le_one (l.2, l.1) m x)

/-! ## Whole-domain regularity of the literal signed fields -/

/-- Signed copies, given by `(ActualSignedStageControls.parameters l).copyData
ActualPrimaryBounds.strip request`. -/
noncomputable def signedCopies (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) :
    PeriodizedWaveBounds.CopyData FullPoint Frequency :=
  (ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip request

theorem signed_common_raw_zero_outside (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (signedCopies l request).common.amplitude n x = 0 ∧
      (signedCopies l request).common.pressure n x = 0 := by
  have hz := fun k => signed_raw_zero_outside l ActualPrimaryBounds.strip request n k hx hout
  constructor
  · change (∑' k, ((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip
      request).cutoff n k x •
      ((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip
          request).amplitude n k x) = 0
    simp only [fun k => (hz k).1, smul_zero, tsum_zero]
  · change (∑' k, (((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip
      request).cutoff n k x : ℂ) *
      ((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip
          request).pressure n k x) = 0
    simp only [fun k => (hz k).2, mul_zero, tsum_zero]

theorem signed_common_raw_zero_germ (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    ((signedCopies l request).common.amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      ((signedCopies l request).common.pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  have hΩ := ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion
  have hc := (radius_smooth.contDiffAt (hΩ.mem_nhds hx)).continuousAt
  have hz : ∀ᶠ y in 𝓝 x,
      (signedCopies l request).common.amplitude n y = 0 ∧
        (signedCopies l request).common.pressure n y = 0 := by
    filter_upwards [hΩ.mem_nhds hx, hc (isClosed_Icc.isOpen_compl.mem_nhds hout)] with y hy hr
    exact signed_common_raw_zero_outside l request n hy
      (fun hi => hr ⟨hi.1.le, hi.2.le⟩)
  exact ⟨hz.mono (fun _ h => h.1), hz.mono (fun _ h => h.2)⟩

theorem radius_nonpos {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) (hr : x.1.1 ≤ 0) :
    radius x ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg hr (VariableGaugeMean.qLength_pos
    ActualPrimary.standardRegion.coord_pos ActualPrimary.standardRegion.coord_lt_one
      (ActualPrimary.standardRegion.time_pos _ hx.1)).le

theorem signed_common_zero_germ_nonpositive (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hr : x.1.1 ≤ 0) :
    ((signedCopies l request).common.amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      ((signedCopies l request).common.pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  apply signed_common_raw_zero_germ l request n hx
  intro hi
  exact (not_lt_of_ge (radius_nonpos hx hr))
    ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)

theorem signed_raw_full_regular (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.amplitude)
    (n : ℕ) :
    ContDiffOn ℝ ∞ ((signedCopies l request).common.amplitude n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) ∧
      ∀ m x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
        (radius x = PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
          radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        iteratedFDeriv ℝ m ((signedCopies l request).common.amplitude n) x = 0 :=
  full_regular_of_envelope_class l ha
    (fun n _ hx ho => (signed_common_raw_zero_outside l request n hx ho).1) n

theorem signed_pressure_full_regular (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (hp : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.pressure)
    (n : ℕ) :
    ContDiffOn ℝ ∞ ((signedCopies l request).common.pressure n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) ∧
      ∀ m x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
        (radius x = PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
          radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        iteratedFDeriv ℝ m ((signedCopies l request).common.pressure n) x = 0 :=
  full_regular_of_envelope_class l hp
    (fun n _ hx ho => (signed_common_raw_zero_outside l request n hx ho).2) n

/-- Positive domain, given by `ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩
ActualPrimaryCoherence.positiveRadialChart`. -/
noncomputable def positiveDomain : Set FullPoint :=
  ActualWaveRegularity.fullDomain ActualPrimary.standardRegion ∩
      ActualPrimaryCoherence.positiveRadialChart

theorem positiveDomain_open : IsOpen positiveDomain :=
  (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion).inter
    ActualPrimaryCoherence.positiveRadialChart_open

theorem smooth_of_positive_or_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : FullPoint → E} (hf : ContDiffOn ℝ ∞ f positiveDomain)
    (hz : ∀ x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      x.1.1 ≤ 0 → f =ᶠ[𝓝 x] fun _ => 0) :
    ContDiffOn ℝ ∞ f (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hr : 0 < x.1.1
  · exact hf.contDiffAt (positiveDomain_open.mem_nhds
      ⟨hx, hr, ActualPrimary.standardRegion.time_pos _ hx.1⟩)
  · exact contDiffAt_const.congr_of_eventuallyEq (hz x hx (le_of_not_gt hr))

/-- Signed normal, constructed using `CurlClassBounds.coefficient`. -/
noncomputable def signedNormal (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) : FullPoint →
        HarmonicCalculus.ComplexVector :=
  CurlClassBounds.coefficient ((ActualSignedStageControls.parameters l).base.radius n)
    ((ActualSignedStageControls.parameters l).directions.radialField n)
    (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
    ((ActualSignedStageControls.parameters l).directions.axialField
        ActualSignedStageControls.fullStrip n)
    ((ActualSignedStageControls.parameters l).base.phase n) ((signedCopies l
        request).common.amplitude n)

/-- Signed corrected, given by `(signedCopies l request).commonCorrected
ActualSignedStageControls.fullStrip (ActualSignedStageControls.parameters l).directions`. -/
noncomputable def signedCorrected (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) : LinearWaveBounds.WaveCoefficients FullPoint
        :=
  (signedCopies l request).commonCorrected ActualSignedStageControls.fullStrip
    (ActualSignedStageControls.parameters l).directions

theorem positive_geometry (l : Index B N0) (n : ℕ) :
    CurlClassBounds.CylindricalGeometry positiveDomain
      ((ActualSignedStageControls.parameters l).base.radius n)
      ((ActualSignedStageControls.parameters l).directions.radialField n)
      (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
      ((ActualSignedStageControls.parameters l).directions.axialField
          ActualSignedStageControls.fullStrip n) :=
  LocalizedCurlRealization.geometry_restrict
    (ActualPrimaryCoherence.piece_geometry ActualPrimary.standardRegion B n)
    positiveDomain_open inter_subset_right

theorem positive_phase (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((ActualSignedStageControls.parameters l).base.phase n) positiveDomain :=
  (ActualPrimaryDynamics.phase_smooth l.2 l.1 n).mono inter_subset_right

theorem signed_normal_zero_germ (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    signedNormal l request n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(signed_common_raw_zero_germ l request n hx hout).1] with y hy
  simp only [signedNormal, CurlClassBounds.coefficient, hy,
      PeriodizedWaveBounds.normalCoefficient_zero]

theorem signed_corrected_zero_germ (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (signedCorrected l request).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have hh := ParticularWaveAssembly.realizedCoefficient_germ
    (signed_common_raw_zero_germ l request n hx hout).1
    ((ActualSignedStageControls.parameters l).base.frequency n)
    ((ActualSignedStageControls.parameters l).base.radius n)
    ((ActualSignedStageControls.parameters l).directions.radialField n)
    (fun _ => (ActualSignedStageControls.parameters l).directions.angular)
    ((ActualSignedStageControls.parameters l).directions.axialField
        ActualSignedStageControls.fullStrip n)
    ((ActualSignedStageControls.parameters l).base.phase n)
  simp only [PeriodizedWaveBounds.realizedCoefficient_zero] at hh ⊢
  exact hh

theorem signed_normal_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.amplitude)
    (n : ℕ) : ContDiffOn ℝ ∞ (signedNormal l request n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  apply smooth_of_positive_or_zero
  · exact CurlClassBounds.normalCoefficient_contDiffOn
      (CurlClassBounds.phaseNormal_contDiffOn (positive_geometry l n) (positive_phase l n))
      ((signed_raw_full_regular l request ha n).1.mono inter_subset_left)
      (fun _ hx => ActualPrimaryCoherence.piece_normal_ne ActualPrimary.standardRegion l.2 l.1 n
          hx.2)
  · intro x hx hr
    apply signed_normal_zero_germ l request n hx
    intro hi
    exact (not_lt_of_ge (radius_nonpos hx hr))
      ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)

theorem signed_corrected_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.amplitude)
    (n : ℕ) : ContDiffOn ℝ ∞ ((signedCorrected l request).amplitude n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  apply smooth_of_positive_or_zero
  · have G := positive_geometry l n
    have hc := CurlClassBounds.cylindricalCurl_contDiffOn G.isOpen (G.radius_smooth.inv G.radius_ne)
      G.radial_smooth G.angular_smooth G.axial_smooth
      ((signed_normal_smooth l request ha n).mono inter_subset_left)
    exact ((signed_raw_full_regular l request ha n).1.mono inter_subset_left).add
      ((hc.const_smul Complex.I).const_smul (1 / (ActualSignedStageControls.parameters
          l).base.frequency n))
  · intro x hx hr
    apply signed_corrected_zero_germ l request n hx
    intro hi
    exact (not_lt_of_ge (radius_nonpos hx hr))
      ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)

/-- Signed field as an element of `CorrectionState.Oscillation Point`. -/
noncomputable def signedField (l : Index B N0) (a : ℕ → FullPoint → HarmonicCalculus.ComplexVector)
    :
    CorrectionState.Oscillation Point := fun n x i =>
  (vectorMode ((ActualSignedStageControls.parameters l).base.frequency n)
    ((ActualSignedStageControls.parameters l).base.phase n) (a n) x i).re

theorem signedField_smooth (l : Index B N0) (a : ℕ → FullPoint → HarmonicCalculus.ComplexVector)
    (ha : ∀ n, ContDiffOn ℝ ∞ (a n) (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion))
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      x.1.1 ≤ 0 → a n =ᶠ[𝓝 x] fun _ => 0) :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) (signedField l a) := by
  intro n i
  apply smooth_of_positive_or_zero
  · exact Complex.reCLM.contDiff.comp_contDiffOn
      (HarmonicCalculus.contDiffOn_mode _ (positive_phase l n)
        ((ContinuousLinearMap.proj i : HarmonicCalculus.ComplexVector →L[ℝ]
            ℂ).contDiff.comp_contDiffOn
          ((ha n).mono inter_subset_left)))
  · intro x hx hr
    filter_upwards [hz n x hx hr] with y hy
    simp only [signedField, vectorMode, HarmonicCalculus.mode, hy, Pi.zero_apply, zero_mul]
    rfl

theorem signedField_support (l : Index B N0) (a : ℕ → FullPoint → HarmonicCalculus.ComplexVector)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      radius x ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → a n =ᶠ[𝓝 x] fun _ => 0) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) (signedField l a) := by
  intro n θ i x hx hn
  by_contra hout
  have hq := VariableGaugeMean.qLength_pos ActualPrimary.standardRegion.coord_pos
    ActualPrimary.standardRegion.coord_lt_one (ActualPrimary.standardRegion.time_pos _ hx)
  have hr : radius (x, θ) ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
    intro h
    apply hout
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hq).mp h.1,
      by simpa only [mul_comm] using (div_le_iff₀ hq).mp h.2⟩
  have he := (hz n (x, θ) ⟨hx, mem_univ _⟩ hr).eq_of_nhds
  apply hn
  simp only [signedField, vectorMode, HarmonicCalculus.mode, he, Pi.zero_apply, zero_mul]
  rfl

theorem signed_exact_smooth (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α
      (signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c
          u)).common.amplitude) :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      ((ActualSignedStageControls.parameters l).exactBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation := by
  rw [(signedAngles l ActualPrimaryBounds.strip P coord c u).block_eq_mode]
  apply signedField_smooth l
  · exact signed_corrected_smooth l _ ha
  · intro n x hx hr
    apply signed_corrected_zero_germ l _ n hx
    intro hi
    exact (not_lt_of_ge (radius_nonpos hx hr))
      ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)

theorem signed_exact_support (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      ((ActualSignedStageControls.parameters l).exactBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation := by
  rw [(signedAngles l ActualPrimaryBounds.strip P coord c u).block_eq_mode]
  exact signedField_support l _ (fun n _ hx hr => signed_corrected_zero_germ l _ n hx hr)

theorem signed_gaussian_zero_outside (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (hout : radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    (signedCopies l request).globalGaussian (ActualSignedStageControls.parameters l).directions n x
        = 0 := by
  have hz := fun k => (signed_raw_zero_outside l ActualPrimaryBounds.strip request n k hx hout).1
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, PeriodizedWaveBounds.CopyData.globalTail,
    PeriodizedWaveBounds.copySum, PeriodizedWaveBounds.CopyData.localTail, signedCopies,
    CorrectionStep.PeriodizedSignedParameters.copyData] at *
  simp only [hz, smul_zero, tsum_zero, add_zero]

theorem signed_gaussian_full_regular (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (hg : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α
      ((signedCopies l request).globalGaussian (ActualSignedStageControls.parameters l).directions))
    (n : ℕ) :
    ContDiffOn ℝ ∞ ((signedCopies l request).globalGaussian (ActualSignedStageControls.parameters
        l).directions n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) ∧
      ∀ m x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
        (radius x = PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
          radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        iteratedFDeriv ℝ m
          ((signedCopies l request).globalGaussian (ActualSignedStageControls.parameters
              l).directions n) x = 0 :=
  full_regular_of_class hg (fun n _ hx ho => signed_gaussian_zero_outside l request n hx ho) n

theorem signed_tangent_eq_field (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ((ActualSignedStageControls.parameters l).tangentBlock ActualPrimaryBounds.strip
      (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation =
    signedField l (signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord
        c u)).common.amplitude := by
  let h := signedAngles l ActualPrimaryBounds.strip P coord c u
  have ha (n : ℕ) := (signedCopies l
    (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c
        u)).common_amplitude_invariant
      ((0 : Point), 1) (fun n i => h.cutoff i n) h.raw_invariant n
  funext n x i
  rw [CorrectionStep.PeriodizedSignedParameters.tangentBlock, SignedWaveUpdate.blockOfCoefficients,
    SignedWaveUpdate.coefficientBlock_velocity]
  have hphase : (ActualSignedStageControls.parameters l).base.frequency n *
      (ActualSignedStageControls.parameters l).base.phase n x =
      (ActualSignedStageControls.parameters l).base.frequency n *
      (ActualSignedStageControls.parameters l).base.phase n (x.1, 0) +
      ((ActualSignedStageControls.parameters l).angularFrequency n : ℝ) * x.2 := by
    rw [CopyAngularInvariance.affinePhase_eq_zeroSlice (h.phase n) x.1 x.2,
      mul_add, ← mul_assoc, h.frequency_slope]
  have hc := HarmonicFields.character_eq_carrier 1
    ((ActualSignedStageControls.parameters l).base.frequency n)
    ((ActualSignedStageControls.parameters l).base.phase n) x
  simp only [Int.cast_one, mul_one] at hc
  change Complex.re (_ * HarmonicFields.character 1
    ((ActualSignedStageControls.parameters l).base.frequency n *
      (ActualSignedStageControls.parameters l).base.phase n (x.1, 0) +
      ((ActualSignedStageControls.parameters l).angularFrequency n : ℝ) * x.2)) =
      Complex.re (_ * HarmonicCalculus.carrier _ _ x)
  rw [← hphase, hc]
  have hi := CopyAngularInvariance.invariant_eq_zeroSlice (ha n) x.1 x.2
  exact congrArg (fun a : HarmonicCalculus.ComplexVector =>
    (a i * HarmonicCalculus.carrier _ _ x).re) hi.symm

theorem signed_tangent_smooth (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α
      (signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c
          u)).common.amplitude) :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      ((ActualSignedStageControls.parameters l).tangentBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation := by
  rw [signed_tangent_eq_field]
  exact signedField_smooth l _ (fun n => (signed_raw_full_regular l _ ha n).1)
    (fun n _ hx hr => (signed_common_zero_germ_nonpositive l _ n hx hr).1)

theorem signed_tangent_support (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      ((ActualSignedStageControls.parameters l).tangentBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation := by
  rw [signed_tangent_eq_field]
  exact signedField_support l _ (fun n _ hx hr => (signed_common_raw_zero_germ l _ n hx hr).1)

theorem signed_common_raw_zero_germ_of_not_ordered (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (hn : ¬Ordered l n)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    (signedCopies l request).common.amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion).mem_nhds hx]
      with y hy
  have hz (k : Frequency) := ((ActualSignedStageControls.parameters l).raw_zero_of_mask
    (s := ActualPrimaryBounds.strip) request n k y (mask_zero_of_not_ordered l n hn k hy)).1
  change (∑' k, ((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip
      request).cutoff n k y •
    ((ActualSignedStageControls.parameters l).copyData ActualPrimaryBounds.strip request).amplitude
        n k y) = 0
  simp only [hz, smul_zero, tsum_zero]

theorem signed_tangent_periodic (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    CorrectionStep.OscillationPeriodic ActualPrimary.standardRegion.carrier
      ((ActualSignedStageControls.parameters l).tangentBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillation := by
  rw [signed_tangent_eq_field]
  intro n R t ht θ Y k
  let x : FullPoint := ((R, (t, Y)), θ)
  have hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨ht, mem_univ _⟩
  have hy : x + ActualWaveRegularity.deckShift k ∈
      ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := by
    change (t + 0) ∈ ActualPrimary.standardRegion.carrier ∧ _
    exact ⟨by simpa only [add_zero] using ht, mem_univ _⟩
  have he : ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) = x + ActualWaveRegularity.deckShift k := by
    simp only [x, ActualWaveRegularity.deckShift, Prod.add_def, add_zero]
  by_cases hn : Ordered l n
  · have ha := ActualWaveRegularity.common_amplitude_translation
      (signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)) n
      (deckPermutation l n k)
      (fun i y _ => cutoff_deck l n hn i k y)
      (fun i y _ => signed_request_amplitude_deck l ActualPrimaryBounds.strip P coord c u n hn i k
          y)
      x hx
    have hp := phase_deck l n hn k x (mem_univ _)
    funext i
    change (vectorMode _ _ _ ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) i).re =
      (vectorMode _ _ _ x i).re
    simp only [he, vectorMode, HarmonicCalculus.mode, ha, HarmonicCalculus.carrier, hp]
  · have h0 := (signed_common_raw_zero_germ_of_not_ordered l
      (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u) n hn hx).eq_of_nhds
    have h1 := (signed_common_raw_zero_germ_of_not_ordered l
      (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u) n hn hy).eq_of_nhds
    funext i
    change (vectorMode _ _ _ ((R, (t, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) i).re =
      (vectorMode _ _ _ x i).re
    simp only [he, vectorMode, HarmonicCalculus.mode, h0, h1, Pi.zero_apply, zero_mul]

theorem smooth_conjugatePair {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} {f : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (ErrorHarmonics.conjugatePair j f) := by
  have hs := HarmonicWaveInteraction.smoothCoefficients_single (hf.div_const 2) j
  exact hs.add hs.conjugateReverse

theorem signed_exact_coefficients_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.amplitude)
    (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (((ActualSignedStageControls.parameters l).exactBlock ActualPrimaryBounds.strip
          request).velocity n i) := by
  apply smooth_conjugatePair
  exact ((contDiffOn_pi.mp (signed_corrected_smooth l request ha n)) i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, mem_univ
        _⟩)

theorem signed_tangent_coefficients_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (ha : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.amplitude)
    (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (((ActualSignedStageControls.parameters l).tangentBlock ActualPrimaryBounds.strip
          request).velocity n i) := by
  apply smooth_conjugatePair
  exact ((contDiffOn_pi.mp (signed_raw_full_regular l request ha n).1) i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, mem_univ
        _⟩)

theorem signed_pressure_coefficients_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (hp : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α (signedCopies l request).common.pressure)
    (n : ℕ) :
    HarmonicResidual.SmoothCoefficients (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (((ActualSignedStageControls.parameters l).exactBlock ActualPrimaryBounds.strip
          request).pressure n) := by
  apply smooth_conjugatePair
  exact (signed_pressure_full_regular l request hp n).1.comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, mem_univ
        _⟩)

theorem signed_gaussian_coefficients_smooth (l : Index B N0)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) {α : ℝ}
    (hg : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α
      ((signedCopies l request).globalGaussian (ActualSignedStageControls.parameters l).directions))
    (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (((ActualSignedStageControls.parameters l).gaussianBlock ActualPrimaryBounds.strip
          request).velocity n i) := by
  apply smooth_conjugatePair
  exact ((contDiffOn_pi.mp (signed_gaussian_full_regular l request hg n).1) i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, mem_univ
        _⟩)

/-- Zero angle, given by `(ContinuousLinearMap.fst ℝ Point ℝ).prod 0`. -/
noncomputable def zeroAngle : FullPoint →L[ℝ] FullPoint :=
  (ContinuousLinearMap.fst ℝ Point ℝ).prod 0

theorem zeroAngle_mem {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :
    zeroAngle x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨hx.1, mem_univ _⟩

theorem signed_pressure_smooth (l : Index B N0) (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) {α : ℝ}
    (hp : MemClass ActualSignedStageControls.fullStrip
      (fun n x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) *
        ActualSignedStageControls.envelope l n x) α
      (signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c
          u)).common.pressure)
    (n : ℕ) : ContDiffOn ℝ ∞
      (((ActualSignedStageControls.parameters l).exactBlock ActualPrimaryBounds.strip
        (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillatoryPressure
            n)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  let h := signedAngles l ActualPrimaryBounds.strip P coord c u
  let a := signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)
  have he (x : FullPoint) : ((ActualSignedStageControls.parameters l).exactBlock
      ActualPrimaryBounds.strip
      (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)).oscillatoryPressure n
          x =
      (HarmonicCalculus.mode ((ActualSignedStageControls.parameters l).base.frequency n)
        ((ActualSignedStageControls.parameters l).base.phase n)
        (fun y => a.common.pressure n (zeroAngle y)) x).re := by
    rw [CorrectionStep.PeriodizedSignedParameters.exactBlock, SignedWaveUpdate.blockOfCoefficients,
      SignedWaveUpdate.coefficientBlock_pressure]
    have hphase : (ActualSignedStageControls.parameters l).base.frequency n *
        (ActualSignedStageControls.parameters l).base.phase n x =
        (ActualSignedStageControls.parameters l).base.frequency n *
          (ActualSignedStageControls.parameters l).base.phase n (x.1, 0) +
        ((ActualSignedStageControls.parameters l).angularFrequency n : ℝ) * x.2 := by
      rw [CopyAngularInvariance.affinePhase_eq_zeroSlice (h.phase n) x.1 x.2,
        mul_add, ← mul_assoc, h.frequency_slope]
    have hc := HarmonicFields.character_eq_carrier 1
      ((ActualSignedStageControls.parameters l).base.frequency n)
      ((ActualSignedStageControls.parameters l).base.phase n) x
    simp only [Int.cast_one, mul_one] at hc
    change Complex.re (a.common.pressure n (x.1, 0) * HarmonicFields.character 1
      ((ActualSignedStageControls.parameters l).base.frequency n *
        (ActualSignedStageControls.parameters l).base.phase n (x.1, 0) +
        ((ActualSignedStageControls.parameters l).angularFrequency n : ℝ) * x.2)) =
      Complex.re (a.common.pressure n (zeroAngle x) * HarmonicCalculus.carrier _ _ x)
    rw [← hphase, hc]
    rfl
  apply (smooth_of_positive_or_zero (f := fun x =>
    (HarmonicCalculus.mode ((ActualSignedStageControls.parameters l).base.frequency n)
      ((ActualSignedStageControls.parameters l).base.phase n)
      (fun y => a.common.pressure n (zeroAngle y)) x).re) ?_ ?_).congr (fun x _ => he x)
  · exact Complex.reCLM.contDiff.comp_contDiffOn
      (HarmonicCalculus.contDiffOn_mode _ (positive_phase l n)
        (((signed_pressure_full_regular l _ hp n).1.comp zeroAngle.contDiff.contDiffOn
          (fun _ hx => zeroAngle_mem hx)).mono inter_subset_left))
  · intro x hx hr
    have hz := ((signed_common_zero_germ_nonpositive l
      (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u) n (zeroAngle_mem hx)
          hr).2).comp_tendsto
      zeroAngle.continuous.continuousAt
    filter_upwards [hz] with y hy
    change a.common.pressure n (zeroAngle y) = 0 at hy
    simp only [HarmonicCalculus.mode, hy, zero_mul]
    rfl

/-! ## The same edge continuation in the particular solver's coordinates -/

/-- Particular full strip, given by `ParticularWaveBounds.reindexStrip
ActualWaveRegularity.particularChart.symm ActualSignedStageControls.fullStrip`. -/
noncomputable def particularFullStrip : StripData ActualWaveRegularity.ParticularSpace :=
  ParticularWaveBounds.reindexStrip ActualWaveRegularity.particularChart.symm
    ActualSignedStageControls.fullStrip

theorem particularFullStrip_eq : particularFullStrip =
    CorrectionStep.ParticularParameters.nativeStrip
      ActualParticularStageControls.associatedStrip := rfl

theorem particular_pull_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → ActualWaveRegularity.ParticularSpace → E} {α : ℝ}
    (hf : MemClass particularFullStrip (fun _ x => Real.sqrt (particularFullStrip.zeta x)) α f) :
    MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α
      (fun n x => f n (ActualWaveRegularity.particularChart x)) := by
  refine ⟨fun _ _ _ => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro n
    exact (hf.smooth n).comp ActualWaveRegularity.particularChart.contDiff.contDiffOn
      (fun x hx => by
        change ActualWaveRegularity.particularChart.symm (ActualWaveRegularity.particularChart x) ∈
          ActualSignedStageControls.fullStrip.domain
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hx)
  · intro m
    obtain ⟨C, hC, p, hbound⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro n x hx j hj
    rw [StateReindex.norm_iteratedFDeriv_pull]
    have hmem : ActualWaveRegularity.particularChart x ∈ particularFullStrip.domain := by
      change ActualWaveRegularity.particularChart.symm (ActualWaveRegularity.particularChart x) ∈
        ActualSignedStageControls.fullStrip.domain
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hx
    have hh := hbound n (ActualWaveRegularity.particularChart x) hmem j hj
    simpa only [majorant, particularFullStrip, ParticularWaveBounds.reindexStrip,
      StripData.growth, LinearIsometryEquiv.symm_apply_apply] using hh

/-- No new radial coordinate or flat weight is chosen for the particular
solver. Reassociation preserves the actual derivative norms. -/
theorem particular_full_regular_of_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → ActualWaveRegularity.ParticularSpace → E} {α : ℝ}
    (hf : MemClass particularFullStrip (fun _ x => Real.sqrt (particularFullStrip.zeta x)) α f)
    (hz : ∀ n z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion →
      radius (ActualWaveRegularity.particularChart.symm z) ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n z = 0)
    (n : ℕ) :
    ContDiffOn ℝ ∞ (f n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) ∧
      ∀ m z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion →
        (radius (ActualWaveRegularity.particularChart.symm z) = PrimaryTargetBounds.leftRadius
            ActualPrimary.nominal ∨
         radius (ActualWaveRegularity.particularChart.symm z) = PrimaryTargetBounds.rightRadius
             ActualPrimary.nominal) →
        iteratedFDeriv ℝ m (f n) z = 0 := by
  have hs := full_regular_of_class (particular_pull_class hf)
    (fun m x hx ho => hz m (ActualWaveRegularity.particularChart x)
      (by simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
        LinearIsometryEquiv.symm_apply_apply] using hx)
      (by simpa only [LinearIsometryEquiv.symm_apply_apply] using ho)) n
  constructor
  · have hh := hs.1.comp ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn
      (fun _ hz => hz)
    simp only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] at hh ⊢
    exact hh
  · intro m z hz he
    have hj := hs.2 m (ActualWaveRegularity.particularChart.symm z) hz he
    have hn := StateReindex.norm_iteratedFDeriv_pull ActualWaveRegularity.particularChart
      (f n) m (ActualWaveRegularity.particularChart.symm z)
    rw [LinearIsometryEquiv.apply_symm_apply, hj, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm

/-! The particular phase below is the literal carrier of its incoming
block. Its equality with the selected primary phase is a carrier invariant,
not a smoothness assumption on an output. -/

/-- Particular copies, given by `(ActualParticularStageControls.canonicalParameters l).copyData
c u b G A j`. -/
noncomputable def particularCopies (l : ActualParticularStageControls.Label B N0)
    (c : CorrectionState.Context (CorrectionStep.CycleSlow × Plane))
    (u : CorrectionState.State (CorrectionStep.CycleSlow × Plane))
    (b : CorrectionState.HarmonicBlock (CorrectionStep.CycleSlow × Plane))
    (G A : HarmonicResidual.BlockCoefficients (CorrectionStep.CycleSlow × Plane)) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters l).copyData c u b G A j

/-- Particular positive, given by `ActualWaveRegularity.particularChart.symm ⁻¹'
positiveDomain`. -/
noncomputable def particularPositive : Set ActualWaveRegularity.ParticularSpace :=
  ActualWaveRegularity.particularChart.symm ⁻¹' positiveDomain

theorem nativeToFull_eq : ActualParticularStageControls.nativeToFull =
    ActualWaveRegularity.particularChart.symm := rfl

theorem particularPositive_open : IsOpen particularPositive :=
  positiveDomain_open.preimage ActualWaveRegularity.particularChart.symm.continuous

theorem particular_native_normal (l : ActualParticularStageControls.Label B N0) (n : ℕ)
    {z : ActualWaveRegularity.ParticularSpace} (hz : z ∈ particularPositive) :
    (ActualParticularStageControls.background l).normal particularFullStrip
      (ActualParticularStageControls.directions (B := B)) n z =
      (ActualPrimary.chartCoefficients l.1 l.2).normal ActualSignedStageControls.fullStrip
        (ActualSignedStageControls.parameters (l.2,l.1)).directions n
        (ActualWaveRegularity.particularChart.symm z) := by
  have hp := ((positive_phase (l.2,l.1) n).contDiffAt
    (positiveDomain_open.mem_nhds hz)).differentiableAt (by simp)
  have he := ParticularWaveBounds.phaseNormal_reindex ActualParticularStageControls.nativeToFull
    ((ActualPrimary.chartCoefficients l.1 l.2).radius n)
    ((ActualSignedStageControls.parameters (l.2,l.1)).directions.radialField n)
    (fun _ => (ActualSignedStageControls.parameters (l.2,l.1)).directions.angular)
    ((ActualSignedStageControls.parameters (l.2,l.1)).directions.axialField
      ActualSignedStageControls.fullStrip n) hp
  simp only [ActualParticularStageControls.background, ActualParticularStageControls.directions,
    ActualSignedStageControls.parameters, LinearWaveBounds.WaveCoefficients.normal,
    ParticularWaveBounds.reindexCoefficients, ParticularWaveBounds.reindex_radialField,
        nativeToFull_eq] at he ⊢
  exact he

theorem particular_geometry_smooth (l : ActualParticularStageControls.Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((ActualParticularStageControls.background l).radius n) particularPositive ∧
    (∀ z ∈ particularPositive, (ActualParticularStageControls.background l).radius n z ≠ 0) ∧
    ContDiffOn ℝ ∞ ((ActualParticularStageControls.directions (B := B)).radialField n)
        particularPositive ∧
    ContDiffOn ℝ ∞ (fun _ : ActualWaveRegularity.ParticularSpace =>
      (ActualParticularStageControls.directions (B := B)).angular) particularPositive ∧
    ContDiffOn ℝ ∞ ((ActualParticularStageControls.directions (B := B)).axialField
        particularFullStrip n)
      particularPositive := by
  let e := ActualParticularStageControls.nativeToFull
  have hmap : MapsTo e particularPositive positiveDomain := fun _ hz => hz
  have G := positive_geometry (l.2,l.1) n
  refine ⟨G.radius_smooth.comp e.contDiff.contDiffOn hmap, fun z hz => G.radius_ne (e z) hz, ?_,
    contDiffOn_const, ?_⟩
  · have hs := e.symm.contDiff.comp_contDiffOn (G.radial_smooth.comp e.contDiff.contDiffOn hmap)
    simp only [ActualParticularStageControls.directions, ParticularWaveBounds.reindex_radialField,
        Function.comp_def, e] at hs ⊢
    exact hs
  · have hs := e.symm.contDiff.comp_contDiffOn (G.axial_smooth.comp e.contDiff.contDiffOn hmap)
    simp only [ActualParticularStageControls.directions, Function.comp_def, e] at hs ⊢
    exact hs

theorem particular_zero_germ {E : Type} [NormedAddCommGroup E]
    (f : ℕ → ActualWaveRegularity.ParticularSpace → E)
    (hz : ∀ n z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion →
      radius (ActualWaveRegularity.particularChart.symm z) ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n z = 0)
    (n : ℕ) {z : ActualWaveRegularity.ParticularSpace}
    (hm : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    f n =ᶠ[𝓝 z] fun _ => 0 := by
  have hΩ := ActualWaveRegularity.nativeDomain_open ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion
  have hc := ((radius_smooth.comp ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn
    (fun _ hx => hx)).contDiffAt (hΩ.mem_nhds hm)).continuousAt
  filter_upwards [hΩ.mem_nhds hm, hc (isClosed_Icc.isOpen_compl.mem_nhds ho)] with y hy hout
  exact hz n y hy (fun hi => hout ⟨hi.1.le, hi.2.le⟩)

theorem particular_smooth_of_positive_or_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ActualWaveRegularity.ParticularSpace → E}
    (hp : ContDiffOn ℝ ∞ f particularPositive)
    (hz : ∀ z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion → z.1.1.1 ≤ 0 → f =ᶠ[𝓝 z] fun _ => 0) :
    ContDiffOn ℝ ∞ f (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) := by
  have hs : ContDiffOn ℝ ∞ (fun x => f (ActualWaveRegularity.particularChart x))
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
    apply smooth_of_positive_or_zero
    · exact hp.comp ActualWaveRegularity.particularChart.contDiff.contDiffOn
        (fun x hx => by simpa only [particularPositive, mem_preimage,
          LinearIsometryEquiv.symm_apply_apply] using hx)
    · intro x hx hr
      exact (hz (ActualWaveRegularity.particularChart x)
        (by simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
          LinearIsometryEquiv.symm_apply_apply] using hx) hr).comp_tendsto
        ActualWaveRegularity.particularChart.continuous.continuousAt
  have hh := hs.comp ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn
    (fun _ hx => hx)
  simp only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] at hh ⊢
  exact hh

section ParticularCoefficients

variable (l : ActualParticularStageControls.Label B N0)
  (c : CorrectionState.Context (CorrectionStep.CycleSlow × Plane))
  (u : CorrectionState.State (CorrectionStep.CycleSlow × Plane))
  (b : CorrectionState.HarmonicBlock (CorrectionStep.CycleSlow × Plane))
  (G A : HarmonicResidual.BlockCoefficients (CorrectionStep.CycleSlow × Plane)) (j : ℤ)

/-- Particular normal, constructed using `CurlClassBounds.coefficient`. -/
noncomputable def particularNormal (n : ℕ) : ActualWaveRegularity.ParticularSpace → ComplexVector :=
  CurlClassBounds.coefficient ((particularCopies l c u b G A j).background.radius n)
    ((ActualParticularStageControls.canonicalParameters l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.canonicalParameters l).directions.angular)
    ((ActualParticularStageControls.canonicalParameters l).directions.axialField
        particularFullStrip n)
    ((particularCopies l c u b G A j).background.phase n)
    ((particularCopies l c u b G A j).common.amplitude n)

variable
  (hphase : (particularCopies l c u b G A j).background.phase =
    (ActualParticularStageControls.background l).phase)
  {α : ℝ}
  (ha : MemClass particularFullStrip (fun _ z => Real.sqrt (particularFullStrip.zeta z)) α
    (particularCopies l c u b G A j).common.amplitude)
  (hz : ∀ n z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion →
    radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
      (particularCopies l c u b G A j).common.amplitude n z = 0)

include hphase ha hz in
theorem particular_normal_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (particularNormal l c u b G A j n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
  have he (z) (hm : z ∈ particularPositive) :
      (particularCopies l c u b G A j).background.normal particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions n z =
      (ActualPrimary.chartCoefficients l.1 l.2).normal ActualSignedStageControls.fullStrip
        (ActualSignedStageControls.parameters (l.2,l.1)).directions n
        (ActualWaveRegularity.particularChart.symm z) := by
    unfold LinearWaveBounds.WaveCoefficients.normal
    rw [hphase]
    exact particular_native_normal l n hm
  apply particular_smooth_of_positive_or_zero
  · have hN := (CurlClassBounds.phaseNormal_contDiffOn (positive_geometry (l.2,l.1) n)
        (positive_phase (l.2,l.1) n)).comp
      ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn (fun _ hx => hx)
    apply CurlClassBounds.normalCoefficient_contDiffOn
      (hN.congr (fun z hm => he z hm))
      (((particular_full_regular_of_class ha hz n).1).mono (fun _ hx => hx.1))
    intro z hm
    rw [he z hm]
    exact ActualPrimaryCoherence.piece_normal_ne ActualPrimary.standardRegion l.1 l.2 n hm.2
  · intro z hm hr
    have ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
      intro hi
      exact (not_lt_of_ge (radius_nonpos hm hr))
        ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)
    filter_upwards [particular_zero_germ _ hz n hm ho] with y hy
    simp only [particularNormal, CurlClassBounds.coefficient, hy,
      PeriodizedWaveBounds.normalCoefficient_zero]

include hz in
theorem particular_corrected_zero_germ (n : ℕ) {z : ActualWaveRegularity.ParticularSpace}
    (hm : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    ((particularCopies l c u b G A j).commonCorrected particularFullStrip
      (ActualParticularStageControls.canonicalParameters l).directions).amplitude n =ᶠ[𝓝 z] fun _
          => 0 := by
  have hh := ParticularWaveAssembly.realizedCoefficient_germ (particular_zero_germ _ hz n hm ho)
    ((particularCopies l c u b G A j).background.frequency n)
    ((particularCopies l c u b G A j).background.radius n)
    ((ActualParticularStageControls.canonicalParameters l).directions.radialField n)
    (fun _ => (ActualParticularStageControls.canonicalParameters l).directions.angular)
    ((ActualParticularStageControls.canonicalParameters l).directions.axialField
        particularFullStrip n)
    ((particularCopies l c u b G A j).background.phase n)
  simp only [PeriodizedWaveBounds.realizedCoefficient_zero] at hh ⊢
  exact hh

include hphase ha hz in
theorem particular_corrected_smooth (n : ℕ) :
    ContDiffOn ℝ ∞
      (((particularCopies l c u b G A j).commonCorrected particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions).amplitude n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
  apply particular_smooth_of_positive_or_zero
  · have hgeom := particular_geometry_smooth l n
    have hc := CurlClassBounds.cylindricalCurl_contDiffOn particularPositive_open
      (hgeom.1.inv hgeom.2.1) hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2
      ((particular_normal_smooth l c u b G A j hphase ha hz n).mono (fun _ hx => hx.1))
    exact ((particular_full_regular_of_class ha hz n).1.mono (fun _ hx => hx.1)).add
      ((hc.const_smul Complex.I).const_smul (1 / (particularCopies l c u b G A
          j).background.frequency n))
  · intro z hm hr
    apply particular_corrected_zero_germ l c u b G A j hz n hm
    intro hi
    exact (not_lt_of_ge (radius_nonpos hm hr))
      ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)

include hphase in
theorem particular_phase_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ ((particularCopies l c u b G A j).background.phase n) particularPositive := by
  rw [hphase]
  exact (positive_phase (l.2,l.1) n).comp
      ActualWaveRegularity.particularChart.symm.contDiff.contDiffOn
    (fun _ hx => hx)

include hphase ha hz in
theorem particular_mode_smooth :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      (ActualWaveRegularity.modeOscillation (particularCopies l c u b G A j) particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions
            ActualWaveRegularity.particularChart) := by
  intro n i
  have hs : ContDiffOn ℝ ∞ (fun z => (vectorMode
      ((particularCopies l c u b G A j).background.frequency n)
      ((particularCopies l c u b G A j).background.phase n)
      (((particularCopies l c u b G A j).commonCorrected particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions).amplitude n) z i).re)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
    apply particular_smooth_of_positive_or_zero
    · exact Complex.reCLM.contDiff.comp_contDiffOn
        (HarmonicCalculus.contDiffOn_mode _ (particular_phase_smooth l c u b G A j hphase n)
          (((contDiffOn_pi.mp (particular_corrected_smooth l c u b G A j hphase ha hz n)) i).mono
            (fun _ hx => hx.1)))
    · intro z hm hr
      have ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
          Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
            (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
        intro hi
        exact (not_lt_of_ge (radius_nonpos hm hr))
          ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)
      filter_upwards [particular_corrected_zero_germ l c u b G A j hz n hm ho] with y hy
      simp only [vectorMode, HarmonicCalculus.mode, hy, Pi.zero_apply, zero_mul]
      rfl
  exact hs.comp ActualWaveRegularity.particularChart.contDiff.contDiffOn
    (fun x hx => by simp only [ActualWaveRegularity.nativeDomain, mem_preimage,
      LinearIsometryEquiv.symm_apply_apply]; exact hx)

include hz in
theorem particular_mode_support :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      (ActualWaveRegularity.modeOscillation (particularCopies l c u b G A j) particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions
            ActualWaveRegularity.particularChart) := by
  intro n θ i x hx hn
  by_contra hout
  have hq := VariableGaugeMean.qLength_pos ActualPrimary.standardRegion.coord_pos
    ActualPrimary.standardRegion.coord_lt_one (ActualPrimary.standardRegion.time_pos _ hx)
  have hr : radius (ActualWaveRegularity.particularChart.symm (ActualWaveRegularity.particularChart
      (x, θ))) ∉
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
    rw [LinearIsometryEquiv.symm_apply_apply]
    intro h
    exact hout ⟨by simpa only [mul_comm] using (le_div_iff₀ hq).mp h.1,
      by simpa only [mul_comm] using (div_le_iff₀ hq).mp h.2⟩
  have hm : ActualWaveRegularity.particularChart (x,θ) ∈
      ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion := by
    simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
      LinearIsometryEquiv.symm_apply_apply] using (show (x,θ) ∈
        ActualWaveRegularity.fullDomain ActualPrimary.standardRegion from ⟨hx, mem_univ _⟩)
  have he := (particular_corrected_zero_germ l c u b G A j hz n hm hr).eq_of_nhds
  apply hn
  simp only [ActualWaveRegularity.modeOscillation, vectorMode, HarmonicCalculus.mode,
    he, Pi.zero_apply, zero_mul]
  rfl

include hphase in
theorem particular_mode_pressure_smooth {β : ℝ}
    (hp : MemClass particularFullStrip (fun _ z => Real.sqrt (particularFullStrip.zeta z)) β
      (particularCopies l c u b G A j).common.pressure)
    (hzp : ∀ n z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion →
      radius (ActualWaveRegularity.particularChart.symm z) ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
        (particularCopies l c u b G A j).common.pressure n z = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => (HarmonicCalculus.mode
      ((particularCopies l c u b G A j).background.frequency n)
      ((particularCopies l c u b G A j).background.phase n)
      ((particularCopies l c u b G A j).common.pressure n) (ActualWaveRegularity.particularChart
          x)).re)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  have hs : ContDiffOn ℝ ∞ (fun z => (HarmonicCalculus.mode
      ((particularCopies l c u b G A j).background.frequency n)
      ((particularCopies l c u b G A j).background.phase n)
      ((particularCopies l c u b G A j).common.pressure n) z).re)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
    apply particular_smooth_of_positive_or_zero
    · exact Complex.reCLM.contDiff.comp_contDiffOn
        (HarmonicCalculus.contDiffOn_mode _ (particular_phase_smooth l c u b G A j hphase n)
          ((particular_full_regular_of_class hp hzp n).1.mono (fun _ hx => hx.1)))
    · intro z hm hr
      have ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
          Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
            (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
        intro hi
        exact (not_lt_of_ge (radius_nonpos hm hr))
          ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hi.1)
      filter_upwards [particular_zero_germ _ hzp n hm ho] with y hy
      simp only [HarmonicCalculus.mode, hy, zero_mul]
      rfl
  exact hs.comp ActualWaveRegularity.particularChart.contDiff.contDiffOn
    (fun x hx => by simp only [ActualWaveRegularity.nativeDomain, mem_preimage,
      LinearIsometryEquiv.symm_apply_apply]; exact hx)

theorem particular_deck_point (z : ActualWaveRegularity.ParticularSpace) (m : Frequency) :
    z + ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m) =
      (z.1, z.2 + TorusAverages.latticePoint m) := by
  change ((z.1.1 + 0, z.1.2 + 0), z.2 + TorusAverages.latticePoint m) = _
  simp only [add_zero]

include hphase in
theorem particular_mode_periodic
    (hsource : ∀ n z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion →
      CommonCoverSolve.PeriodicAt ((particularCopies l c u b G A j).source n) z.1)
    (hzero : ∀ n, ¬Ordered (l.2,l.1) n → ∀ z,
      z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion →
      (particularCopies l c u b G A j).common.amplitude n =ᶠ[𝓝 z] fun _ => 0) :
    CorrectionStep.OscillationPeriodic ActualPrimary.standardRegion.carrier
      (ActualWaveRegularity.modeOscillation (particularCopies l c u b G A j) particularFullStrip
        (ActualParticularStageControls.canonicalParameters l).directions
            ActualWaveRegularity.particularChart) := by
  intro n R t ht θ Y m
  let x : FullPoint := ((R,(t,Y)),θ)
  let z := ActualWaveRegularity.particularChart x
  have hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion := ⟨ht, mem_univ _⟩
  have hz0 : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion := by
    simpa only [z, ActualWaveRegularity.nativeDomain, mem_preimage,
      LinearIsometryEquiv.symm_apply_apply] using hx
  have he : ActualWaveRegularity.particularChart ((R,(t,Y + ((m.1:ℝ),(m.2:ℝ)))),θ) =
      z + ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m) := by
    rw [← map_add]
    congr 1
    simp only [x, ActualWaveRegularity.deckShift, Prod.add_def, add_zero]
  by_cases hn : Ordered (l.2,l.1) n
  · have hR : ActualWaveRegularity.TranslationOn
        (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
            ActualPrimary.standardRegion)
        (ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m))
        ((particularCopies l c u b G A j).background.radius n) := by
      intro v _
      change v.1.1.1 + 0 = v.1.1.1
      exact add_zero _
    have hr : ActualWaveRegularity.TranslationOn
        (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
            ActualPrimary.standardRegion)
        (ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m))
        ((ActualParticularStageControls.canonicalParameters l).directions.radialField n) := by
      intro v _
      have hh := congrArg ActualWaveRegularity.particularChart
        (radial_deck (l.2,l.1) n m (ActualWaveRegularity.particularChart.symm v) (mem_univ _))
      simp only [ActualParticularStageControls.canonicalParameters,
          ActualParticularStageControls.directions,
        ParticularWaveBounds.reindex_radialField, ParticularWaveBounds.reindexVector,
        nativeToFull_eq, map_add, LinearIsometryEquiv.symm_symm,
        LinearIsometryEquiv.symm_apply_apply] at hh ⊢
      exact hh
    have hp : ActualWaveRegularity.TranslationOn
        (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
            ActualPrimary.standardRegion)
        (ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m))
        ((particularCopies l c u b G A j).background.phase n) := by
      intro v _
      rw [hphase]
      change (ActualPrimary.chartCoefficients l.1 l.2).phase n
        (ActualWaveRegularity.particularChart.symm (v + ActualWaveRegularity.particularChart
          (ActualWaveRegularity.deckShift m))) = _
      rw [map_add, LinearIsometryEquiv.symm_apply_apply]
      exact phase_deck (l.2,l.1) n hn m (ActualWaveRegularity.particularChart.symm v) (mem_univ _)
    have ha0 := ActualWaveRegularity.common_amplitude_translation
      (particularCopies l c u b G A j) n
      (Equiv.addRight (coverIndex ((ActualParticularStageControls.canonicalParameters l).geometry
          n).gap m))
      (Ω := ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion)
      (z := ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m))
      (fun k v _ => by
        rw [particular_deck_point]
        change (ActualParticularStageControls.canonicalParameters l).cutoff n
          (((ActualParticularStageControls.canonicalParameters l).geometry n).coordinates
            (k + coverIndex ((ActualParticularStageControls.canonicalParameters l).geometry n).gap
                m)
            (v.2 + TorusAverages.latticePoint m)) = _
        rw [Geometry.coordinates_deck]
        rfl)
      (fun k v hv => by
        rw [particular_deck_point]
        exact ParticularWaveBounds.complexCopyVelocity_deck
          (ParticularWaveAssembly.angleTangent ((ActualParticularStageControls.canonicalParameters
              l).tangent j n))
          ((particularCopies l c u b G A j).source n)
          ((ActualParticularStageControls.canonicalParameters l).geometry n)
          ((ActualParticularStageControls.canonicalParameters l).length_pos n).le
          k m v.1 (hsource n v hv) v.2)
    have hv := ActualWaveRegularity.common_velocity_translation (particularCopies l c u b G A j)
      particularFullStrip (ActualParticularStageControls.canonicalParameters l).directions
      (ActualWaveRegularity.nativeDomain_open ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion)
      n hR hr hp ha0 z hz0
    funext i
    change (vectorMode _ _ _ (ActualWaveRegularity.particularChart
      ((R,(t,Y + ((m.1:ℝ),(m.2:ℝ)))),θ)) i).re = _
    rw [he, hv]
    rfl
  · have hz1 : z + ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m) ∈
        ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
            ActualPrimary.standardRegion := by
      rw [← he]
      simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
        LinearIsometryEquiv.symm_apply_apply] using
        (show ((R,(t,Y + ((m.1:ℝ),(m.2:ℝ)))),θ) ∈
          ActualWaveRegularity.fullDomain ActualPrimary.standardRegion from ⟨ht, mem_univ _⟩)
    have hvzero (v) (hv : v ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion) :
        ((particularCopies l c u b G A j).commonCorrected particularFullStrip
          (ActualParticularStageControls.canonicalParameters l).directions).amplitude n v = 0 := by
      have hh := ParticularWaveAssembly.realizedCoefficient_germ (hzero n hn v hv)
        ((particularCopies l c u b G A j).background.frequency n)
        ((particularCopies l c u b G A j).background.radius n)
        ((ActualParticularStageControls.canonicalParameters l).directions.radialField n)
        (fun _ => (ActualParticularStageControls.canonicalParameters l).directions.angular)
        ((ActualParticularStageControls.canonicalParameters l).directions.axialField
            particularFullStrip n)
        ((particularCopies l c u b G A j).background.phase n)
      have he := hh.eq_of_nhds
      simp only [PeriodizedWaveBounds.realizedCoefficient_zero] at he
      exact he
    have h0 := hvzero z hz0
    have h1 := hvzero _ hz1
    funext i
    change (vectorMode _ _ _ (ActualWaveRegularity.particularChart
      ((R,(t,Y + ((m.1:ℝ),(m.2:ℝ)))),θ)) i).re = (vectorMode _ _ _ z i).re
    simp only [he, vectorMode, HarmonicCalculus.mode, h0, h1, Pi.zero_apply, zero_mul]

end ParticularCoefficients

/-! Closed support and actual source continuity, unlike an interior norm
bound alone, determine the literal values on the radial faces. -/

theorem zero_on_radial_faces {E : Type} [NormedAddCommGroup E] {f : FullPoint → E}
    (hf : ContinuousOn f (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion))
    (hz : ∀ x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      radius x ∉ Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f x = 0)
    {x : FullPoint} (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (ho : radius x ∉ Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) : f x = 0 := by
  let ell := VariableGaugeMean.qLength (2 * ActualPrimary.h) x.1.2.1
  have hell : 0 < ell := VariableGaugeMean.qLength_pos ActualPrimary.standardRegion.coord_pos
    ActualPrimary.standardRegion.coord_lt_one (ActualPrimary.standardRegion.time_pos _ hx.1)
  let line : ℝ → FullPoint := fun r => ((r,x.1.2),x.2)
  have hl : Continuous line := (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hg : Continuous (f ∘ line) := hf.comp_continuous hl (fun _ => hx)
  have hlo : Set.EqOn (f ∘ line) (fun _ => 0)
      (Iio (ell * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)) := by
    intro r hr
    apply hz (line r) hx
    intro hm
    have hR : ell * PrimaryTargetBounds.leftRadius ActualPrimary.nominal ≤ r := by
      simpa only [mul_comm, Set.mem_Ici] using (le_div_iff₀ hell).mp hm.1
    exact (not_lt_of_ge hR) hr
  have hhi : Set.EqOn (f ∘ line) (fun _ => 0)
      (Ioi (ell * PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) := by
    intro r hr
    apply hz (line r) hx
    intro hm
    have hR : r ≤ ell * PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by
      simpa only [mul_comm, Set.mem_Iic] using (div_le_iff₀ hell).mp hm.2
    exact (not_lt_of_ge hR) hr
  change (f ∘ line) x.1.1 = 0
  rcases not_and_or.mp ho with hleft | hright
  · apply hlo.closure hg continuous_const
    rw [closure_Iio]
    simpa only [mul_comm, Set.mem_Iic] using (div_le_iff₀ hell).mp (le_of_not_gt hleft)
  · apply hhi.closure hg continuous_const
    rw [closure_Ioi]
    simpa only [mul_comm, Set.mem_Ici] using (le_div_iff₀ hell).mp (le_of_not_gt hright)

theorem particular_zero_on_radial_faces {E : Type} [NormedAddCommGroup E]
    {f : ActualWaveRegularity.ParticularSpace → E}
    (hf : ContinuousOn f (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion))
    (hz : ∀ z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion →
      radius (ActualWaveRegularity.particularChart.symm z) ∉
        Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f z = 0)
    {z : ActualWaveRegularity.ParticularSpace}
    (hm : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    (ho : radius (ActualWaveRegularity.particularChart.symm z) ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) : f z = 0 := by
  have hh := zero_on_radial_faces
    (hf.comp ActualWaveRegularity.particularChart.continuous.continuousOn
      (fun x hx => by simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
        LinearIsometryEquiv.symm_apply_apply] using hx))
    (fun x hx hout => hz (ActualWaveRegularity.particularChart x)
      (by simpa only [ActualWaveRegularity.nativeDomain, mem_preimage,
        LinearIsometryEquiv.symm_apply_apply] using hx)
      (by simpa only [LinearIsometryEquiv.symm_apply_apply] using hout)) hm ho
  simpa only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using hh

section CoefficientDeck

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedSpace ℝ D] in
theorem common_pressure_translation (a : PeriodizedWaveBounds.CopyData D I)
    {Ω : Set D} {v : D} (n : ℕ) (e : I ≃ I)
    (hcut : ∀ i x, x ∈ Ω → a.cutoff n (e i) (x + v) = a.cutoff n i x)
    (hp : ∀ i x, x ∈ Ω → a.pressure n (e i) (x + v) = a.pressure n i x) :
    ActualWaveRegularity.TranslationOn Ω v (a.common.pressure n) := by
  intro x hx
  change (∑' i, (a.cutoff n i (x+v) : ℂ) * a.pressure n i (x+v)) =
    ∑' i, (a.cutoff n i x : ℂ) * a.pressure n i x
  rw [← e.tsum_eq]
  exact tsum_congr (fun i => by rw [hcut i x hx, hp i x hx])

theorem common_gaussian_translation (a : PeriodizedWaveBounds.CopyData D I)
    (d : LinearWaveBounds.GraphDirections D) {Ω : Set D} {v : D} (hΩ : IsOpen Ω)
    (n : ℕ) (e : I ≃ I)
    (hcut : ∀ i x, x ∈ Ω → a.cutoff n (e i) (x + v) = a.cutoff n i x)
    (ha : ∀ i x, x ∈ Ω → a.amplitude n (e i) (x + v) = a.amplitude n i x)
    (hf : ActualWaveRegularity.TranslationOn Ω v (a.source n)) :
    ActualWaveRegularity.TranslationOn Ω v (a.globalGaussian d n) := by
  have hd (i : I) (x : D) (hx : x ∈ Ω) :
      fderiv ℝ (a.cutoff n (e i)) (x+v) = fderiv ℝ (a.cutoff n i) x := by
    have he : (fun y => a.cutoff n (e i) (y+v)) =ᶠ[𝓝 x] a.cutoff n i := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hcut i y hy
    simpa only [fderiv_comp_add_right] using he.fderiv_eq (𝕜 := ℝ)
  intro x hx
  have hc : a.cutoffSum n (x+v) = a.cutoffSum n x := by
    change (∑' i, a.cutoff n i (x+v)) = ∑' i, a.cutoff n i x
    rw [← e.tsum_eq]
    exact tsum_congr (fun i => hcut i x hx)
  have ht : a.globalTail d n (x+v) = a.globalTail d n x := by
    change (∑' i, a.localTail d n i (x+v)) = ∑' i, a.localTail d n i x
    rw [← e.tsum_eq]
    apply tsum_congr
    intro i
    simp only [PeriodizedWaveBounds.CopyData.localTail, LinearWaveBounds.GraphDirections.Dfast,
      HarmonicCalculus.along, LinearWaveBounds.GraphDirections.fastField, hd i x hx, ha i x hx]
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, ht, hc, hf x hx]

end CoefficientDeck

theorem signed_pressure_deck (l : Index B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (n : ℕ) (hn : Ordered l n)
    (k m : Frequency) (x : FullPoint)
    (hrequest : request n (x + ActualWaveRegularity.deckShift m) = request n x) :
    ((ActualSignedStageControls.parameters l).copyData s request).pressure n
      (deckPermutation l n m k) (x + ActualWaveRegularity.deckShift m) =
      ((ActualSignedStageControls.parameters l).copyData s request).pressure n k x := by
  have hN := ActualWaveRegularity.phaseNormal_translation isOpen_univ
    (radius_deck l n m) (radial_deck l n m)
    (ActualWaveRegularity.TranslationOn.const (ActualSignedStageControls.parameters
        l).directions.angular)
    (ActualWaveRegularity.TranslationOn.const
      ((HarmonicWaveInteraction.productStrip s).epsilon n • (ActualSignedStageControls.parameters
          l).directions.axial))
    (phase_deck l n hn m) x (mem_univ _)
  change (ActualSignedStageControls.parameters l).base.normal (HarmonicWaveInteraction.productStrip
      s)
      (ActualSignedStageControls.parameters l).directions n (x + ActualWaveRegularity.deckShift m) =
    (ActualSignedStageControls.parameters l).base.normal (HarmonicWaveInteraction.productStrip s)
      (ActualSignedStageControls.parameters l).directions n x at hN
  simp only [CorrectionStep.PeriodizedSignedParameters.copyData,
      CorrectionStep.PeriodizedSignedParameters.native,
    CorrectionStep.SignedParameters.coefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, ParticularWaveBounds.projectedPressure]
  rw [hN]
  simp only [ActualSignedStageControls.parameters, SignedWaveUpdate.signedVector,
    SignedWaveUpdate.signedScalar, ActualSignedStageControls.matrix,
        ActualSignedStageControls.target,
    ActualSignedStageControls.mask, ActualSignedStageControls.fundamental,
    ActualSignedStageControls.normalMotion, ActualSignedStageControls.action,
    nativePoint_deck l n hn, hrequest]

/-- Coefficient periods for the actual signed wave, before angular or
finite-label assembly. -/
theorem signed_coefficient_translations (l : Index B N0) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) (hn : Ordered l n) (m : Frequency) :
    let a := signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)
    let Ω := ActualWaveRegularity.fullDomain ActualPrimary.standardRegion
    ActualWaveRegularity.TranslationOn Ω (ActualWaveRegularity.deckShift m) (a.common.amplitude n) ∧
    ActualWaveRegularity.TranslationOn Ω (ActualWaveRegularity.deckShift m)
      ((a.commonCorrected ActualSignedStageControls.fullStrip (ActualSignedStageControls.parameters
          l).directions).amplitude n) ∧
    ActualWaveRegularity.TranslationOn Ω (ActualWaveRegularity.deckShift m) (a.common.pressure n) ∧
    ActualWaveRegularity.TranslationOn Ω (ActualWaveRegularity.deckShift m)
      (a.globalGaussian (ActualSignedStageControls.parameters l).directions n) := by
  dsimp only
  let a := signedCopies l (LocalSignedRequest.fullRequest ActualPrimaryBounds.strip P coord c u)
  have hcut i x (_hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :=
    cutoff_deck l n hn i m x
  have hamp i x (_hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) :=
    signed_request_amplitude_deck l ActualPrimaryBounds.strip P coord c u n hn i m x
  have hr := ActualWaveRegularity.common_amplitude_translation a n (deckPermutation l n m) hcut hamp
  refine ⟨hr, ActualWaveRegularity.commonCorrected_translation a ActualSignedStageControls.fullStrip
    (ActualSignedStageControls.parameters l).directions
    (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion) n
    (fun x _ => radius_deck l n m x (mem_univ _))
    (fun x _ => radial_deck l n m x (mem_univ _))
    (fun x _ => phase_deck l n hn m x (mem_univ _)) hr, ?_, ?_⟩
  · exact common_pressure_translation a n (deckPermutation l n m) hcut
      (fun i x _ => signed_pressure_deck l ActualPrimaryBounds.strip _ n hn i m x
        (fullRequest_deck ActualPrimaryBounds.strip P coord c u n m x))
  · exact common_gaussian_translation a (ActualSignedStageControls.parameters l).directions
      (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion) n (deckPermutation l n m)
      hcut hamp (fun _ _ => rfl)

/-- The source callback is a per-label, complete-fiber statement. It is not
replaced by periodicity of the total real oscillation. -/
theorem particular_coefficient_translations (l : ActualParticularStageControls.Label B N0)
    (c : CorrectionState.Context (CorrectionStep.CycleSlow × Plane))
    (u : CorrectionState.State (CorrectionStep.CycleSlow × Plane))
    (b : CorrectionState.HarmonicBlock (CorrectionStep.CycleSlow × Plane))
    (G A : HarmonicResidual.BlockCoefficients (CorrectionStep.CycleSlow × Plane)) (j : ℤ)
    (hphase : (particularCopies l c u b G A j).background.phase =
        (ActualParticularStageControls.background l).phase)
    (n : ℕ) (hn : Ordered (l.2, l.1) n) (m : Frequency)
    (hsource : ∀ z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion → CommonCoverSolve.PeriodicAt ((particularCopies l c u b G A
            j).source n) z.1) :
    let a := particularCopies l c u b G A j
    let Ω := ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion
    let v := ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m)
    ActualWaveRegularity.TranslationOn Ω v (a.common.amplitude n) ∧
    ActualWaveRegularity.TranslationOn Ω v
      ((a.commonCorrected particularFullStrip (ActualParticularStageControls.canonicalParameters
          l).directions).amplitude n) ∧
    ActualWaveRegularity.TranslationOn Ω v (a.common.pressure n) ∧
    ActualWaveRegularity.TranslationOn Ω v
      (a.globalGaussian (ActualParticularStageControls.canonicalParameters l).directions n) := by
  dsimp only
  let a := particularCopies l c u b G A j
  let p := ActualParticularStageControls.canonicalParameters l
  let Ω := ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion
  let v := ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift m)
  let e := Equiv.addRight (coverIndex (p.geometry n).gap m)
  have hcut k z (_hz : z ∈ Ω) : a.cutoff n (e k) (z+v) = a.cutoff n k z := by
    rw [show z+v = (z.1,z.2+TorusAverages.latticePoint m) from particular_deck_point z m]
    change p.cutoff n ((p.geometry n).coordinates (k + coverIndex (p.geometry n).gap m)
      (z.2 + TorusAverages.latticePoint m)) = _
    rw [Geometry.coordinates_deck]
    rfl
  have hamp k z (hz : z ∈ Ω) : a.amplitude n (e k) (z+v) = a.amplitude n k z := by
    rw [show z+v = (z.1,z.2+TorusAverages.latticePoint m) from particular_deck_point z m]
    exact ParticularWaveBounds.complexCopyVelocity_deck (ParticularWaveAssembly.angleTangent
        (p.tangent j n))
      (a.source n) (p.geometry n) (p.length_pos n).le k m z.1 (hsource z hz) z.2
  have hpress k z (hz : z ∈ Ω) : a.pressure n (e k) (z+v) = a.pressure n k z := by
    rw [show z+v = (z.1,z.2+TorusAverages.latticePoint m) from particular_deck_point z m]
    exact ParticularWaveBounds.complexCopyPressure_deck (ParticularWaveAssembly.angleTangent
        (p.tangent j n))
      (a.source n) (p.geometry n) (p.length_pos n).le k m (a.background.frequency n) z.1 (hsource z
          hz) z.2
  have hR : ActualWaveRegularity.TranslationOn Ω v (a.background.radius n) := by
    intro z _
    change z.1.1.1 + 0 = z.1.1.1
    exact add_zero _
  have hrad : ActualWaveRegularity.TranslationOn Ω v (p.directions.radialField n) := by
    intro z _
    have hh := congrArg ActualWaveRegularity.particularChart
      (radial_deck (l.2,l.1) n m (ActualWaveRegularity.particularChart.symm z) (mem_univ _))
    simp only [p, v, ActualParticularStageControls.canonicalParameters,
        ActualParticularStageControls.directions,
      ParticularWaveBounds.reindex_radialField, ParticularWaveBounds.reindexVector,
      nativeToFull_eq, map_add, LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.symm_apply_apply] at hh ⊢
    exact hh
  have hΦ : ActualWaveRegularity.TranslationOn Ω v (a.background.phase n) := by
    intro z _
    change (particularCopies l c u b G A j).background.phase n (z+v) = _
    rw [hphase]
    change (ActualPrimary.chartCoefficients l.1 l.2).phase n
      (ActualWaveRegularity.particularChart.symm (z+v)) = _
    rw [map_add]
    change (ActualPrimary.chartCoefficients l.1 l.2).phase n
      (ActualWaveRegularity.particularChart.symm z + ActualWaveRegularity.deckShift m) = _
    exact phase_deck (l.2,l.1) n hn m (ActualWaveRegularity.particularChart.symm z) (mem_univ _)
  have hraw := ActualWaveRegularity.common_amplitude_translation a n e hcut hamp
  refine ⟨hraw, ActualWaveRegularity.commonCorrected_translation a particularFullStrip p.directions
    (ActualWaveRegularity.nativeDomain_open ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    n hR hrad hΦ hraw, common_pressure_translation a n e hcut hpress, ?_⟩
  apply common_gaussian_translation a p.directions
    (ActualWaveRegularity.nativeDomain_open ActualWaveRegularity.particularChart
        ActualPrimary.standardRegion)
    n e hcut hamp
  intro z hz
  rw [show z+v = (z.1,z.2+TorusAverages.latticePoint m) from particular_deck_point z m]
  exact hsource z hz z.2 m

end NavierStokes.ActualWaveRegularityData
