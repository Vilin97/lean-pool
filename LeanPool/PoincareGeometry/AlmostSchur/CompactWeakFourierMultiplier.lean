/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakJetFourierRepresentative

/-! # Fourier multipliers from whole-space weak derivatives

The real test identity is strengthened to complex tests by separate real and
imaginary parts. Integrability is explicit. Applying it to the bounded smooth
Fourier character proves the multiplier identity for L¹ weak derivative data.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Real smooth weak tests imply the complex test identity, when the two
complex products are integrable. No complex-valued derivative is assumed. -/
theorem complex_weak_test_of_real_tests {u du : E → ℝ} (v : E)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, du x * φ x))
    (Φ : E → ℂ) (hΦ : ContDiff ℝ ∞ Φ)
    (hi₁ : Integrable (fun x => (u x : ℂ) * fderiv ℝ Φ x v) volume)
    (hi₂ : Integrable (fun x => (du x : ℂ) * Φ x) volume) :
    (∫ x, (u x : ℂ) * fderiv ℝ Φ x v) = -(∫ x, (du x : ℂ) * Φ x) := by
  have hd (L : ℂ →L[ℝ] ℝ) (x : E) :
      fderiv ℝ (fun y => L (Φ y)) x v = L (fderiv ℝ Φ x v) := by
    have hh := (L.hasFDerivAt.comp x (hΦ.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun T : E →L[ℝ] ℝ => T v) hh
  apply Complex.ext
  · have he := hw (fun x => (Φ x).re) (Complex.reCLM.contDiff.comp hΦ)
    have hdre (x : E) : fderiv ℝ (fun y => (Φ y).re) x v = (fderiv ℝ Φ x v).re :=
      hd Complex.reCLM x
    simp_rw [hdre] at he
    have hr₁ : (∫ x, ((u x : ℂ) * fderiv ℝ Φ x v).re) =
        (∫ x, (u x : ℂ) * fderiv ℝ Φ x v).re := Complex.reCLM.integral_comp_comm hi₁
    have hr₂ : (∫ x, ((du x : ℂ) * Φ x).re) =
        (∫ x, (du x : ℂ) * Φ x).re := Complex.reCLM.integral_comp_comm hi₂
    rw [Complex.neg_re, ← hr₁, ← hr₂]
    simpa using he
  · have he := hw (fun x => (Φ x).im) (Complex.imCLM.contDiff.comp hΦ)
    have hdim (x : E) : fderiv ℝ (fun y => (Φ y).im) x v = (fderiv ℝ Φ x v).im :=
      hd Complex.imCLM x
    simp_rw [hdim] at he
    have hi₁' : (∫ x, ((u x : ℂ) * fderiv ℝ Φ x v).im) =
        (∫ x, (u x : ℂ) * fderiv ℝ Φ x v).im := Complex.imCLM.integral_comp_comm hi₁
    have hi₂' : (∫ x, ((du x : ℂ) * Φ x).im) =
        (∫ x, (du x : ℂ) * Φ x).im := Complex.imCLM.integral_comp_comm hi₂
    rw [Complex.neg_im, ← hi₁', ← hi₂']
    simpa using he
/-- A whole-space L¹ weak derivative has the exact Fourier multiplier
`2πi ⟨ξ,v⟩`. The weak identity is required for arbitrary smooth real tests,
as delivered by compact cutoff localization. -/
theorem fourier_weak_derivative_multiplier {u du : E → ℝ} (v : E)
    (hu : Integrable u volume) (hdu : Integrable du volume)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, du x * φ x)) (ξ : E) :
    𝓕 (fun x => (du x : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (inner ℝ ξ v : ℂ)) * 𝓕 (fun x => (u x : ℂ)) ξ := by
  let Φ : E → ℂ := fun x => Real.fourierChar (-inner ℝ ξ x)
  have hΦ : ContDiff ℝ ∞ Φ := by
    simp only [Φ, Real.fourierChar_apply]
    have hlin : ContDiff ℝ ∞ (fun x : E => inner ℝ ξ x) := (innerSL ℝ ξ).contDiff
    exact ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul hlin.neg)).mul
      contDiff_const).cexp
  have hd (x : E) : fderiv ℝ Φ x v =
      -(2 * Real.pi * Complex.I * (inner ℝ ξ v : ℂ)) * Φ x := by
    have hlin : HasFDerivAt (fun y : E => -inner ℝ ξ y) (-(innerSL ℝ ξ)) x :=
      (innerSL ℝ ξ).hasFDerivAt.neg
    have hh := (Real.hasDerivAt_fourierChar (-inner ℝ ξ x)).hasFDerivAt.comp x hlin
    have hh' := congrArg (fun T : E →L[ℝ] ℂ => T v) hh.fderiv
    change fderiv ℝ Φ x v = (-inner ℝ ξ v) • (2 * Real.pi * Complex.I * Φ x) at hh'
    rw [hh']
    simp only [Complex.real_smul, Complex.ofReal_neg]
    ring
  have hnorm (x : E) : ‖Φ x‖ = 1 := Circle.norm_coe _
  have hi (f : E → ℝ) (hf : Integrable f volume) :
      Integrable (fun x => (f x : ℂ) * Φ x) volume :=
    hf.ofReal.mul_bdd hΦ.continuous.aestronglyMeasurable (Eventually.of_forall (fun x => (hnorm x).le))
  have hi₁ : Integrable (fun x => (u x : ℂ) * fderiv ℝ Φ x v) volume := by
    simp_rw [hd]
    convert (hi u hu).const_mul (-(2 * Real.pi * Complex.I * (inner ℝ ξ v : ℂ))) using 1
    funext x
    ring
  have he := complex_weak_test_of_real_tests v hw Φ hΦ hi₁ (hi du hdu)
  simp_rw [hd, mul_left_comm (u _ : ℂ)] at he
  rw [integral_const_mul] at he
  have hpair (f : E → ℝ) : (∫ x, (f x : ℂ) * Φ x) = 𝓕 (fun x => (f x : ℂ)) ξ := by
    rw [Real.fourier_eq]
    congr 1
    funext x
    simp [Φ, Circle.smul_def, real_inner_comm, mul_comm]
  rw [hpair, hpair] at he
  linear_combination he

end AlmostSchur
