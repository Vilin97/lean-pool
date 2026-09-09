/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryMixed
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalReflection
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledCutoff

@[expose] public section

/-!
Reflection covariance of the actual cutoff-curl/Riesz boundary operator.
On homogeneous gradient tensors reflection is componentwise pullback.  It
is represented by the reflected vector test `-φ(-x)`, so both curl signs
cancel.  No covariance or parity of an inverse operator is assumed.
-/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest
open scoped ContDiff

def Cutoff.reflect (χ : Cutoff) : Cutoff :=
  ⟨fun x => χ.field (-x), χ.smooth.comp contDiff_id.neg,
    χ.compact.comp_homeomorph (Homeomorph.neg Space)⟩

theorem Cutoff.reflect_reflect (χ : Cutoff) : χ.reflect.reflect = χ := by
  apply Cutoff.ext
  funext x
  exact congrArg χ.field (neg_neg x)

theorem Cutoff.reflect_eq_of_even (χ : Cutoff) (hχ : ∀ x, χ.field (-x) = χ.field x) :
    χ.reflect = χ := Cutoff.ext (funext hχ)

def l2ReflectionEquiv : L2 ≃ₗᵢ[ℝ] L2 :=
  LinearIsometryEquiv.ofSurjective reflection (fun u => ⟨reflection u, reflection_involutive u⟩)

def gradientReflection : GradientTensor ≃ₗᵢ[ℝ] GradientTensor :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => l2ReflectionEquiv)

theorem gradientReflection_apply (G : GradientTensor) (i : Fin 3) :
    gradientReflection G i = reflection (G i) := rfl

theorem gradientReflection_involutive (G : GradientTensor) :
    gradientReflection (gradientReflection G) = G := by
  ext i : 1
  exact reflection_involutive (G i)

def reflectedTest (f : Test) : Test :=
  ⟨fun x => -(f : Space → Space) (-x), (f.smooth.comp contDiff_id.neg).neg,
    (f.compact.comp_homeomorph (Homeomorph.neg Space)).neg⟩

theorem testGradient_reflected (f : Test) :
    EulerMeanGradientTest.testGradient (reflectedTest f) =
      gradientReflection (EulerMeanGradientTest.testGradient f) := by
  ext i : 1
  change derivativeColumn (reflectedTest f) i = reflection (derivativeColumn f i)
  apply Lp.ext
  filter_upwards [derivativeColumn_ae (reflectedTest f) i,
    reflection_ae (derivativeColumn f i),
    measurePreserving_reflection.quasiMeasurePreserving.ae (derivativeColumn_ae f i)]
    with x ht hr hf
  rw [ht, hr, hf]
  change fderiv ℝ (fun y => -(f : Space → Space) (-y)) x _ = _
  rw [fderiv_neg_reflect _ (f.smooth.differentiable (by simp))]

theorem gradientReflection_homogeneous (u : homogeneousSpace) :
    gradientReflection (u : GradientTensor) ∈ homogeneousSpace := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact EulerMeanGradientTest.testGradient.range.isClosed_topologicalClosure.preimage
      (gradientReflection.continuous.comp continuous_subtype_val)
  · intro f
    change gradientReflection (EulerMeanGradientTest.testGradient f) ∈ homogeneousSpace
    rw [← testGradient_reflected]
    exact EulerMeanGradientTest.testGradient.range.le_topologicalClosure
      (LinearMap.mem_range_self _ _)

def homogeneousReflection : homogeneousSpace →ₗᵢ[ℝ] homogeneousSpace where
  toFun u := ⟨gradientReflection (u : GradientTensor), gradientReflection_homogeneous u⟩
  map_add' u v := by apply Subtype.ext; exact map_add gradientReflection _ _
  map_smul' c u := by apply Subtype.ext; exact map_smul gradientReflection c _
  norm_map' u := gradientReflection.norm_map (u : GradientTensor)

theorem homogeneousReflection_coe (u : homogeneousSpace) :
    (homogeneousReflection u : GradientTensor) = gradientReflection (u : GradientTensor) := rfl

theorem homogeneousReflection_involutive (u : homogeneousSpace) :
    homogeneousReflection (homogeneousReflection u) = u := by
  apply Subtype.ext
  exact gradientReflection_involutive (u : GradientTensor)

theorem homogeneousReflection_test (f : Test) :
    homogeneousReflection (homogeneousGradient f) = homogeneousGradient (reflectedTest f) := by
  apply Subtype.ext
  exact (testGradient_reflected f).symm

theorem homogeneousReflection_inner_shift (u v : homogeneousSpace) :
    ⟪homogeneousReflection u, v⟫_ℝ = ⟪u, homogeneousReflection v⟫_ℝ := by
  calc
    _ = ⟪homogeneousReflection u, homogeneousReflection (homogeneousReflection v)⟫_ℝ := by
      rw [homogeneousReflection_involutive]
    _ = _ := homogeneousReflection.inner_map_map u (homogeneousReflection v)

theorem vectorCurl_neg_reflect (f : Space → Space) (hf : Differentiable ℝ f) (x : Space) :
    vectorCurl (fun y => -f (-y)) x = vectorCurl f (-x) := by
  have hleft : Differentiable ℝ (fun y => -f (-y)) := (hf.comp differentiable_id.neg).neg
  rw [vectorCurl_eq_matrix _ x (hleft x),
    fderiv_neg_reflect f hf, ← vectorCurl_eq_matrix f (-x) (hf (-x))]

theorem testCurl_reflected (χ : Cutoff) (f : Test) :
    reflection (testCurl χ f) = testCurl χ.reflect (reflectedTest f) := by
  apply Lp.ext
  filter_upwards [reflection_ae (testCurl χ f),
    measurePreserving_reflection.quasiMeasurePreserving.ae (testCurl_ae χ f),
    testCurl_ae χ.reflect (reflectedTest f)] with x hr hχ ht
  rw [hr, hχ, ht]
  have he := vectorCurl_neg_reflect (fun y => χ.field y • (f : Space → Space) y)
    ((χ.smooth.smul f.smooth).differentiable (by simp)) x
  simpa only [Cutoff.reflect, reflectedTest, smul_neg] using he.symm

/-- Covariance is proved first on real compact tests, then by density. -/
theorem cutoffCurl_reflection (χ : Cutoff) (u : homogeneousSpace) :
    reflection (cutoffCurl χ u) = cutoffCurl χ.reflect (homogeneousReflection u) := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq (reflection.continuous.comp (cutoffCurl χ).continuous)
      ((cutoffCurl χ.reflect).continuous.comp homogeneousReflection.continuous)
  · intro f
    rw [homogeneousReflection_test, cutoffCurl_on_test, cutoffCurl_on_test]
    exact testCurl_reflected χ f

/-- The actual Riesz solution, rather than an assumed inverse, respects reflection. -/
theorem weakPotential_reflection (χ : Cutoff) (z : L2) :
    homogeneousReflection (weakPotential χ z) = weakPotential χ.reflect (reflection z) := by
  apply ext_inner_right ℝ
  intro v
  calc
    _ = ⟪weakPotential χ z, homogeneousReflection v⟫_ℝ :=
      homogeneousReflection_inner_shift _ _
    _ = ⟪z, cutoffCurl χ (homogeneousReflection v)⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left (cutoffCurl χ) _ z
    _ = ⟪reflection z, reflection (cutoffCurl χ (homogeneousReflection v))⟫_ℝ :=
      (reflection.inner_map_map _ _).symm
    _ = ⟪reflection z, cutoffCurl χ.reflect v⟫_ℝ := by
      rw [cutoffCurl_reflection, homogeneousReflection_involutive]
    _ = _ := (ContinuousLinearMap.adjoint_inner_left (cutoffCurl χ.reflect) v _).symm

theorem mixedBoundaryOperator_reflection (χ ψ : Cutoff) (z : L2) :
    reflection (mixedBoundaryOperator χ ψ z) =
      mixedBoundaryOperator χ.reflect ψ.reflect (reflection z) := by
  change reflection (cutoffCurl χ (weakPotential ψ z)) =
    cutoffCurl χ.reflect (weakPotential ψ.reflect (reflection z))
  rw [cutoffCurl_reflection, weakPotential_reflection]

theorem boundaryOperator_reflection (χ : Cutoff) (z : L2) :
    reflection (boundaryOperator χ z) = boundaryOperator χ.reflect (reflection z) :=
  mixedBoundaryOperator_reflection χ χ z

theorem boundaryOperator_reflection_of_even (χ : Cutoff)
    (hχ : ∀ x, χ.field (-x) = χ.field x) (z : L2) :
    reflection (boundaryOperator χ z) = boundaryOperator χ (reflection z) := by
  rw [boundaryOperator_reflection, Cutoff.reflect_eq_of_even χ hχ]

/-- The concrete source boundary operator commutes with ordinary spatial reflection. -/
theorem scaledBoundaryOperator_reflection (ℓ : ℝ) (hℓ : 0 < ℓ) (z : L2) :
    reflection (boundaryOperator (scaledCutoff ℓ hℓ) z) =
      boundaryOperator (scaledCutoff ℓ hℓ) (reflection z) :=
  boundaryOperator_reflection_of_even (scaledCutoff ℓ hℓ) (scaledCutoff_even ℓ hℓ) z

end EulerMeanBoundary
