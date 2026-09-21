/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Assembly
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CayleySelectorBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Spectral-projection target for contour continuation

This module packages the projection-valued measure associated with a bounded
self-adjoint operator.  It identifies each measurable spectral projection with
the Mathlib orthogonal projection onto its range and records the exact
orthogonal-projection property required by the continuation assembly.

The scalar half of spectral identification is also recorded here: the
sign-correct scalar Riesz transform equals normalized winding, normalized
winding equals the selected-set indicator on the real spectrum, and the target
projection is the bounded spectral calculus of that indicator.  The operator
half transports the contour integral through Mathlib's continuous calculus and
reads the identification straight off
`boundedSelfAdjointSpectralProjection_eq_cfcL_of_selector`.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set
open MeasureTheory
open scoped InnerProductSpace
open DavisKahan.Foundation

universe v

section BoundedSpectralProjection

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Once contour spectral identification is supplied, the contour Riesz
operator inherits the exact orthogonal-projection property. -/
theorem SpectralSeparatingContour.contourRieszProjection_isOrthogonalProjection_of_eq
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s)
    (hidentify : Γ.contourRieszProjection =
      boundedSelfAdjointSpectralProjection A Γ.selfAdjoint s
        Γ.measurable_selected) :
    IsOrthogonalProjection Γ.contourRieszProjection := by
  rw [hidentify]
  exact boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    A Γ.selfAdjoint s Γ.measurable_selected

/-- A pointwise spectral-identification result turns the fixed-contour affine
path into a path of orthogonal projections. -/
theorem fixedContourRieszOperator_operatorPath_isOrthogonalProjection_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (parameterSet : Set ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ parameterSet,
      (operatorPath A V t).IsSymmetric)
    (hidentify : ∀ t (ht : t ∈ parameterSet),
      fixedContourRieszOperator Γ (operatorPath A V t) =
        boundedSelfAdjointSpectralProjection (operatorPath A V t)
          (hself t ht) s hs)
    {t : ℝ} (ht : t ∈ parameterSet) :
    IsOrthogonalProjection
      (fixedContourRieszOperator Γ (operatorPath A V t)) := by
  rw [hidentify t ht]
  exact boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (operatorPath A V t) (hself t ht) s hs



namespace PiecewiseC1ClosedContour

/-- The sign-correct scalar Riesz transform associated with the project
resolvent convention `(A - z I)⁻¹`. -/
noncomputable def scalarRieszTransform
    (Γ : PiecewiseC1ClosedContour) (lam : ℝ) : ℂ :=
  rieszNormalization *
    ∫ t in (0 : ℝ)..1,
      (((lam : ℂ) - Γ.param t)⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t

/-- The sign-correct scalar resolvent transform is exactly the normalized
winding value recorded by the contour. -/
theorem scalarRieszTransform_eq_normalizedWinding
    (Γ : PiecewiseC1ClosedContour) (lam : ℝ) :
    Γ.scalarRieszTransform lam = Γ.normalizedWinding (lam : ℂ) := by
  unfold scalarRieszTransform normalizedWinding
  have hintegral :
      (∫ t in (0 : ℝ)..1,
        (((lam : ℂ) - Γ.param t)⁻¹) *
          derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t) =
        -(∫ t in (0 : ℝ)..1,
          ((Γ.param t - (lam : ℂ))⁻¹) *
            derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change (((lam : ℂ) - Γ.param t)⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t =
      -(((Γ.param t - (lam : ℂ))⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t)
    rw [show (lam : ℂ) - Γ.param t =
      -(Γ.param t - (lam : ℂ)) by ring]
    rw [inv_neg, neg_mul]
  rw [hintegral]
  simp [rieszNormalization]

end PiecewiseC1ClosedContour

omit [CompleteSpace H] in
/-- On the real spectrum, the scalar Riesz transform is the indicator of the
selected component. -/
theorem SpectralSeparatingContour.scalarRieszTransform_eq_spectralSelector
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.geometric.scalarRieszTransform lam = spectralSelector s lam := by
  rw [Γ.geometric.scalarRieszTransform_eq_normalizedWinding]
  classical
  by_cases hmem : lam ∈ s
  · rw [Γ.normalizedWinding_eq_one hlam hmem]
    simp [spectralSelector, hmem]
  · rw [Γ.normalizedWinding_eq_zero hlam hmem]
    simp [spectralSelector, hmem]




/-- Along a separating contour, each project resolvent is represented by the
bounded continuous functional calculus of its scalar symbol. -/
theorem SpectralSeparatingContour.resolventOperator_eq_cfc
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    resolventOperator A (Γ.path t) =
      cfc (fun w : ℂ => (w - Γ.path t)⁻¹) A := by
  exact resolventOperator_eq_cfc_resolventSymbol
    A Γ.selfAdjoint (Γ.path t) Γ.spectralMargin Γ.spectralMargin_pos
      (Γ.spectrum_separated t)

/-- The contour resolvent one-form is the continuous functional calculus of
its scalar one-form symbol. -/
theorem SpectralSeparatingContour.resolventOneForm_eq_cfc
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) (v : ℂ) :
    resolventOneForm A (Γ.path t) v =
      cfc (fun w : ℂ => v * (w - Γ.path t)⁻¹) A := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hne : ∀ w ∈ spectrum ℂ A, w - Γ.path t ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := Γ.spectrum_separated t lam (by exact hlamC)
    have heq : (lam : ℂ) = Γ.path t := sub_eq_zero.mp hzero
    rw [← heq, sub_self, norm_zero] at hdist
    linarith [Γ.spectralMargin_pos]
  have hgcont : ContinuousOn (fun w : ℂ => (w - Γ.path t)⁻¹)
      (spectrum ℂ A) :=
    ((continuous_id.sub continuous_const).continuousOn).inv₀ hne
  rw [resolventOneForm_apply, Γ.resolventOperator_eq_cfc t]
  rw [← cfc_const_mul v (fun w : ℂ => (w - Γ.path t)⁻¹) A hgcont]




/-! ## The operator contour integral through the isometric CFC -/

/-- The scalar contour integrand, bundled as a continuous function on the
complex spectrum.  `mkD` keeps the definition total; spectral separation shows
that it takes the intended value on the contour parameter interval. -/
noncomputable def PiecewiseC1ClosedContour.contourResolventSymbol
    (Γ : PiecewiseC1ClosedContour) (A : H →L[ℂ] H) (t : ℝ) :
    C(spectrum ℂ A, ℂ) :=
  ContinuousMap.mkD
    ((spectrum ℂ A).domRestrict
      (fun w : ℂ =>
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.param t)⁻¹)) 0

/-- At every contour point, the scalar resolvent symbol is continuous on the
complex spectrum. -/
theorem SpectralSeparatingContour.continuousOn_resolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    ContinuousOn (fun w : ℂ => (w - Γ.path t)⁻¹) (spectrum ℂ A) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hne : ∀ w ∈ spectrum ℂ A, w - Γ.path t ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := Γ.spectrum_separated t lam (by exact hlamC)
    have heq : (lam : ℂ) = Γ.path t := sub_eq_zero.mp hzero
    rw [← heq, sub_self, norm_zero] at hdist
    linarith [Γ.spectralMargin_pos]
  exact ((continuous_id.sub continuous_const).continuousOn).inv₀ hne

/-- Applying the bounded continuous functional calculus to the bundled scalar
symbol recovers the operator-valued curve-integral integrand. -/
theorem SpectralSeparatingContour.cfcL_contourResolventSymbol_eq_curveIntegralFun
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (Γ.geometric.contourResolventSymbol A t) =
      curveIntegralFun (resolventOneForm A) Γ.path t := by
  let τ : unitInterval := ⟨t, ht⟩
  have hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      Γ.selfAdjoint).isStarNormal
  unfold PiecewiseC1ClosedContour.contourResolventSymbol
  rw [← cfc_eq_cfcL_mkD
    (f := fun w : ℂ =>
      derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
        (w - Γ.geometric.param t)⁻¹)
    (a := A) (ha := hnormal)]
  rw [curveIntegralFun_def]
  have hparam : Γ.geometric.param = Γ.path.extend := by
    unfold PiecewiseC1ClosedContour.param
    rfl
  rw [hparam, Γ.path.extend_apply ht]
  exact
    (Γ.resolventOneForm_eq_cfc τ
      (derivWithin Γ.path.extend (Set.Icc (0 : ℝ) 1) t)).symm

/-- The continuous-map-valued scalar contour integrand is interval integrable.
The proof pulls integrability back from the already established operator
integrand through the isometric complex continuous functional calculus. -/
theorem SpectralSeparatingContour.intervalIntegrable_contourResolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    IntervalIntegrable
      (Γ.geometric.contourResolventSymbol A) volume 0 1 := by
  let hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      Γ.selfAdjoint).isStarNormal
  let L : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H) :=
    cfcL (a := A) hnormal
  have hoperator :
      IntervalIntegrable
        (curveIntegralFun (resolventOneForm A) Γ.path) volume 0 1 :=
    Γ.curveIntegrable_resolventOneForm
  have hmapped :
      IntervalIntegrable
        (fun t => L (Γ.geometric.contourResolventSymbol A t))
        volume 0 1 := by
    refine hoperator.congr_uIoo ?_
    intro t ht
    rw [Set.uIoo_of_le zero_le_one] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self ht
    exact (Γ.cfcL_contourResolventSymbol_eq_curveIntegralFun htI).symm
  have hIso : Isometry L := by
    simpa [L, cfcL] using (isometry_cfcHom A hnormal)
  have hpull {μ : Measure ℝ}
      {f : ℝ → C(spectrum ℂ A, ℂ)}
      (hf : Integrable (fun t => L (f t)) μ) : Integrable f μ := by
    have hiff :
        Integrable ((fun g : C(spectrum ℂ A, ℂ) => L g) ∘ f) μ ↔
          Integrable f μ :=
      LipschitzWith.integrable_comp_iff_of_antilipschitz
        (μ := μ) (f := f) (g := fun g : C(spectrum ℂ A, ℂ) => L g)
        hIso.lipschitz hIso.antilipschitz (by simp)
    exact hiff.mp (by simpa only [Function.comp_def] using hf)
  exact ⟨hpull hmapped.1, hpull hmapped.2⟩

/-- The normalized scalar contour integral as one continuous function on the
complex spectrum. -/
noncomputable def SpectralSeparatingContour.integratedContourResolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : C(spectrum ℂ A, ℂ) :=
  rieszNormalization •
    ∫ t in (0 : ℝ)..1, Γ.geometric.contourResolventSymbol A t

/-- The unnormalized operator contour integral is the continuous functional
calculus of the integrated scalar contour symbol. -/
theorem SpectralSeparatingContour.resolventCurveIntegral_eq_cfcL
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.resolventCurveIntegral =
      cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (∫ t in (0 : ℝ)..1,
          Γ.geometric.contourResolventSymbol A t) := by
  rw [resolventCurveIntegral, curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1,
        curveIntegralFun (resolventOneForm A) Γ.path t) =
      ∫ t in (0 : ℝ)..1,
        cfcL (a := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            Γ.selfAdjoint).isStarNormal
          (Γ.geometric.contourResolventSymbol A t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact (Γ.cfcL_contourResolventSymbol_eq_curveIntegralFun ht).symm
    _ = cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (∫ t in (0 : ℝ)..1,
          Γ.geometric.contourResolventSymbol A t) :=
      cfcL_intervalIntegral A
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (Γ.geometric.contourResolventSymbol A)
        Γ.intervalIntegrable_contourResolventSymbol

/-- The normalized Riesz operator is the continuous functional calculus of the
integrated scalar contour symbol. -/
theorem SpectralSeparatingContour.contourRieszProjection_eq_cfcL
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.contourRieszProjection =
      cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        Γ.integratedContourResolventSymbol := by
  rw [contourRieszProjection, Γ.resolventCurveIntegral_eq_cfcL]
  unfold SpectralSeparatingContour.integratedContourResolventSymbol
  rw [map_smul]

/-- At a real spectral point, the integrated continuous symbol is the scalar
Riesz transform recorded by the contour. -/
theorem SpectralSeparatingContour.integratedContourResolventSymbol_apply
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.integratedContourResolventSymbol
        ⟨(lam : ℂ), by
          have hAsa : IsSelfAdjoint A :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
              Γ.selfAdjoint
          rw [← hAsa.spectrumRestricts.algebraMap_image]
          exact ⟨lam, hlam, rfl⟩⟩ =
      Γ.geometric.scalarRieszTransform lam := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
    rw [← hAsa.spectrumRestricts.algebraMap_image]
    exact ⟨lam, hlam, rfl⟩
  let x : spectrum ℂ A := ⟨(lam : ℂ), hlamC⟩
  have hint := Γ.intervalIntegrable_contourResolventSymbol
  have heval :
      (∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t) x =
      ∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t x := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      (ContinuousMap.integral_apply hint.1 x)
  change rieszNormalization *
      (∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t) x =
    Γ.geometric.scalarRieszTransform lam
  rw [heval]
  unfold PiecewiseC1ClosedContour.scalarRieszTransform
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  let τ : unitInterval := ⟨t, ht⟩
  have hparam : Γ.geometric.param t = Γ.path τ := by
    simpa only [PiecewiseC1ClosedContour.param] using Γ.path.extend_apply ht
  have hcont : ContinuousOn
      (fun w : ℂ =>
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.geometric.param t)⁻¹)
      (spectrum ℂ A) := by
    rw [hparam]
    exact continuousOn_const.mul (Γ.continuousOn_resolventSymbol τ)
  change
    (Γ.geometric.contourResolventSymbol A t) x =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  unfold PiecewiseC1ClosedContour.contourResolventSymbol
  change
    (ContinuousMap.mkD
      ((spectrum ℂ A).domRestrict fun w : ℂ =>
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.geometric.param t)⁻¹) 0) x =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  rw [ContinuousMap.mkD_apply_of_continuousOn hcont]
  change
    derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
        ((lam : ℂ) - Γ.geometric.param t)⁻¹ =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  exact mul_comm _ _

/-- On the real spectrum, the integrated continuous symbol is exactly the
selected-set indicator. -/
theorem SpectralSeparatingContour.integratedContourResolventSymbol_eq_selector
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.integratedContourResolventSymbol
        ⟨(lam : ℂ), by
          have hAsa : IsSelfAdjoint A :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
              Γ.selfAdjoint
          rw [← hAsa.spectrumRestricts.algebraMap_image]
          exact ⟨lam, hlam, rfl⟩⟩ =
      spectralSelector s lam := by
  rw [Γ.integratedContourResolventSymbol_apply hlam]
  exact Γ.scalarRieszTransform_eq_spectralSelector hlam


/-- The normalized contour Riesz operator is the genuine spectral projection
onto the selected bounded spectral subspace. -/
theorem SpectralSeparatingContour.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.contourRieszProjection =
      boundedSelfAdjointSpectralProjection
        A Γ.selfAdjoint s Γ.measurable_selected := by
  rw [Γ.contourRieszProjection_eq_cfcL]
  exact (boundedSelfAdjointSpectralProjection_eq_cfcL_of_selector A Γ.selfAdjoint s
    Γ.measurable_selected Γ.integratedContourResolventSymbol
    (fun _ hlam => Γ.integratedContourResolventSymbol_eq_selector hlam)).symm

/-- Every spectrally separating contour produces an orthogonal projection. -/
theorem SpectralSeparatingContour.contourRieszProjection_isOrthogonalProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    IsOrthogonalProjection Γ.contourRieszProjection :=
  Γ.contourRieszProjection_isOrthogonalProjection_of_eq
    Γ.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection

/-- A common geometric contour that separates every point of an affine path
produces a path of orthogonal fixed-contour Riesz projections. -/
theorem fixedContourRieszOperator_operatorPath_isOrthogonalProjection
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (s : Set ℝ)
    (hseparating : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
      SpectralSeparatingContour (operatorPath A V t) s)
    (hgeometric : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (hseparating t ht).geometric = Γ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection
        (fixedContourRieszOperator Γ (operatorPath A V t)) := by
  intro t ht
  let Γt := hseparating t ht
  have hfixed :
      fixedContourRieszOperator Γ (operatorPath A V t) =
        Γt.contourRieszProjection := by
    rw [← hgeometric t ht]
    exact fixedContourRieszOperator_eq_contourRieszProjection Γt
  rw [hfixed]
  exact Γt.contourRieszProjection_isOrthogonalProjection

end BoundedSpectralProjection

end DavisKahanExt
end TauCeti
