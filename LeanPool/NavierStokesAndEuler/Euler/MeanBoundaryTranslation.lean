/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryMixed
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation

@[expose] public section

/-! The actual translation action on homogeneous gradients and localized Newtonian operators. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest
open scoped ContDiff

def l2TranslationEquiv (a : Space) : L2 ≃ₗᵢ[ℝ] L2 :=
  LinearIsometryEquiv.ofSurjective (translation a) (fun u =>
    ⟨translation (-a) u, by rw [translation_add, add_neg_cancel, translation_zero]⟩)

theorem l2TranslationEquiv_apply (a : Space) (u : L2) : l2TranslationEquiv a u = translation a u :=
  rfl

def gradientTranslation (a : Space) : GradientTensor ≃ₗᵢ[ℝ] GradientTensor :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => l2TranslationEquiv a)

theorem gradientTranslation_apply (a : Space) (G : GradientTensor) (i : Fin 3) :
    gradientTranslation a G i = translation a (G i) := rfl

theorem gradientTranslation_add (a b : Space) (G : GradientTensor) :
    gradientTranslation a (gradientTranslation b G) = gradientTranslation (a+b) G := by
  ext i : 1
  exact translation_add a b (G i)

theorem gradientTranslation_zero (G : GradientTensor) : gradientTranslation 0 G = G := by
  ext i : 1
  exact translation_zero (G i)

def translatedTest (a : Space) (f : Test) : Test :=
  ⟨fun x => (f : Space → Space) (x+a), f.smooth.comp (contDiff_id.add contDiff_const),
    f.compact.comp_homeomorph (Homeomorph.addRight a)⟩

theorem testGradient_translated (a : Space) (f : Test) :
    EulerMeanGradientTest.testGradient (translatedTest a f) =
      gradientTranslation a (EulerMeanGradientTest.testGradient f) := by
  ext i : 1
  change derivativeColumn (translatedTest a f) i = translation a (derivativeColumn f i)
  apply Lp.ext
  filter_upwards [derivativeColumn_ae (translatedTest a f) i,
    translation_ae a (derivativeColumn f i),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (derivativeColumn_ae f i)] with x ht ha hf
  rw [ht, ha, hf]
  change fderiv ℝ (fun y => (f : Space → Space) (y+a)) x _ = _
  rw [fderiv_comp_add_right]

theorem gradientTranslation_homogeneous (a : Space) (u : homogeneousSpace) :
    gradientTranslation a (u : GradientTensor) ∈ homogeneousSpace := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact EulerMeanGradientTest.testGradient.range.isClosed_topologicalClosure.preimage
      ((gradientTranslation a).continuous.comp continuous_subtype_val)
  · intro f
    change gradientTranslation a (EulerMeanGradientTest.testGradient f) ∈ homogeneousSpace
    rw [← testGradient_translated]
    exact EulerMeanGradientTest.testGradient.range.le_topologicalClosure
      (LinearMap.mem_range_self _ _)

def homogeneousTranslation (a : Space) : homogeneousSpace →ₗᵢ[ℝ] homogeneousSpace where
  toFun u := ⟨gradientTranslation a (u : GradientTensor), gradientTranslation_homogeneous a u⟩
  map_add' u v := by apply Subtype.ext; exact map_add (gradientTranslation a) _ _
  map_smul' c u := by apply Subtype.ext; exact map_smul (gradientTranslation a) c _
  norm_map' u := (gradientTranslation a).norm_map (u : GradientTensor)

theorem homogeneousTranslation_coe (a : Space) (u : homogeneousSpace) :
    (homogeneousTranslation a u : GradientTensor) = gradientTranslation a (u : GradientTensor) :=
      rfl

theorem homogeneousTranslation_add (a b : Space) (u : homogeneousSpace) :
    homogeneousTranslation a (homogeneousTranslation b u) = homogeneousTranslation (a+b) u := by
  apply Subtype.ext
  exact gradientTranslation_add a b (u : GradientTensor)

theorem homogeneousTranslation_zero (u : homogeneousSpace) : homogeneousTranslation 0 u = u := by
  apply Subtype.ext
  exact gradientTranslation_zero (u : GradientTensor)

theorem homogeneousTranslation_test (a : Space) (f : Test) :
    homogeneousTranslation a (homogeneousGradient f) = homogeneousGradient (translatedTest a f) :=
      by
  apply Subtype.ext
  exact (testGradient_translated a f).symm

theorem homogeneousTranslation_inner_shift (a : Space) (u v : homogeneousSpace) :
    ⟪homogeneousTranslation a u, v⟫_ℝ = ⟪u, homogeneousTranslation (-a) v⟫_ℝ := by
  calc
    _ = ⟪homogeneousTranslation a u,
        homogeneousTranslation a (homogeneousTranslation (-a) v)⟫_ℝ := by
      rw [homogeneousTranslation_add, add_neg_cancel, homogeneousTranslation_zero]
    _ = _ := (homogeneousTranslation a).inner_map_map _ _

theorem vectorCurl_translated (a : Space) (f : Space → Space) (x : Space) :
    vectorCurl (fun y => f (y+a)) x = vectorCurl f (x+a) := by
  ext i
  simp only [vectorCurl, curl_apply, partialDerivative]
  have h₁ := fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => f y (i+2)) (x := x) a
  have h₂ := fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => f y (i+1)) (x := x) a
  rw [h₁, h₂]

theorem testCurl_translated (a : Space) (χ : Cutoff) (f : Test) :
    translation a (testCurl χ f) = testCurl (χ.translate a) (translatedTest a f) := by
  apply Lp.ext
  filter_upwards [translation_ae a (testCurl χ f),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (testCurl_ae χ f), testCurl_ae (χ.translate a) (translatedTest a f)] with x ha hχ ht
  rw [ha, hχ, ht]
  exact (vectorCurl_translated a (fun y => χ.field y • (f : Space → Space) y) x).symm

/-- Translating the output translates both the cutoff and the homogeneous potential. -/
theorem cutoffCurl_translation (a : Space) (χ : Cutoff) (u : homogeneousSpace) :
    translation a (cutoffCurl χ u) = cutoffCurl (χ.translate a) (homogeneousTranslation a u) := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq ((translation a).continuous.comp (cutoffCurl χ).continuous)
      ((cutoffCurl (χ.translate a)).continuous.comp (homogeneousTranslation a).continuous)
  · intro f
    rw [homogeneousTranslation_test, cutoffCurl_on_test, cutoffCurl_on_test]
    exact testCurl_translated a χ f

/-- The actual weak inverse respects spatial translation of its cutoff and forcing. -/
theorem weakPotential_translation (a : Space) (χ : Cutoff) (z : L2) :
    homogeneousTranslation a (weakPotential χ z) = weakPotential (χ.translate a) (translation a z)
      := by
  apply ext_inner_right ℝ
  intro v
  calc
    _ = ⟪weakPotential χ z, homogeneousTranslation (-a) v⟫_ℝ :=
      homogeneousTranslation_inner_shift a _ _
    _ = ⟪z, cutoffCurl χ (homogeneousTranslation (-a) v)⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left (cutoffCurl χ) _ z
    _ = ⟪translation a z, translation a (cutoffCurl χ (homogeneousTranslation (-a) v))⟫_ℝ :=
      ((translation a).inner_map_map _ _).symm
    _ = ⟪translation a z, cutoffCurl (χ.translate a) v⟫_ℝ := by
      rw [cutoffCurl_translation, homogeneousTranslation_add, add_neg_cancel,
        homogeneousTranslation_zero]
    _ = _ := (ContinuousLinearMap.adjoint_inner_left (cutoffCurl (χ.translate a)) v _).symm

theorem mixedBoundaryOperator_translation (a : Space) (χ ψ : Cutoff) (z : L2) :
    translation a (mixedBoundaryOperator χ ψ z) =
      mixedBoundaryOperator (χ.translate a) (ψ.translate a) (translation a z) := by
  change translation a (cutoffCurl χ (weakPotential ψ z)) =
    cutoffCurl (χ.translate a) (weakPotential (ψ.translate a) (translation a z))
  rw [cutoffCurl_translation, weakPotential_translation]

/-- The genuine spatial translation commutator on ordinary L². -/
def translationCommutator (a : Space) (A : L2 →L[ℝ] L2) : L2 →L[ℝ] L2 :=
  (translation a).toContinuousLinearMap.comp A - A.comp (translation a).toContinuousLinearMap

/-- Both cutoff positions, and only those positions, contribute to the spatial commutator. -/
theorem mixedBoundaryOperator_translationCommutator (a : Space) (χ ψ : Cutoff) :
    translationCommutator a (mixedBoundaryOperator χ ψ) =
      (mixedBoundaryOperator ((χ.translate a).sub χ) (ψ.translate a) +
        mixedBoundaryOperator χ ((ψ.translate a).sub ψ)).comp (translation a).toContinuousLinearMap
          := by
  apply ContinuousLinearMap.ext
  intro z
  change translation a (mixedBoundaryOperator χ ψ z) - mixedBoundaryOperator χ ψ (translation a z) =
    mixedBoundaryOperator ((χ.translate a).sub χ) (ψ.translate a) (translation a z) +
      mixedBoundaryOperator χ ((ψ.translate a).sub ψ) (translation a z)
  rw [mixedBoundaryOperator_translation]
  exact congrArg (fun A : L2 →L[ℝ] L2 => A (translation a z))
    (mixedBoundaryOperator_difference (χ.translate a) χ (ψ.translate a) ψ)

theorem mixedBoundaryOperator_translationCommutator_norm_le (a : Space) (χ ψ : Cutoff) :
    ‖translationCommutator a (mixedBoundaryOperator χ ψ)‖ ≤
      cutoffBound ((χ.translate a).sub χ) * cutoffBound (ψ.translate a) +
        cutoffBound χ * cutoffBound ((ψ.translate a).sub ψ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (mul_nonneg (cutoffBound_nonneg _) (cutoffBound_nonneg _))
      (mul_nonneg (cutoffBound_nonneg _) (cutoffBound_nonneg _)))
  intro z
  change ‖translation a (mixedBoundaryOperator χ ψ z) - mixedBoundaryOperator χ ψ (translation a
    z)‖ ≤ _
  rw [mixedBoundaryOperator_translation]
  change ‖(mixedBoundaryOperator (χ.translate a) (ψ.translate a) -
    mixedBoundaryOperator χ ψ) (translation a z)‖ ≤ _
  calc
    _ ≤ ‖mixedBoundaryOperator (χ.translate a) (ψ.translate a) -
        mixedBoundaryOperator χ ψ‖ * ‖translation a z‖ :=
      (mixedBoundaryOperator (χ.translate a) (ψ.translate a) - mixedBoundaryOperator χ ψ).le_opNorm
        _
    _ ≤ _ := by
      rw [(translation a).norm_map]
      exact mul_le_mul_of_nonneg_right
        (mixedBoundaryOperator_difference_norm_le (χ.translate a) χ (ψ.translate a) ψ) (norm_nonneg
          z)

end EulerMeanBoundary
