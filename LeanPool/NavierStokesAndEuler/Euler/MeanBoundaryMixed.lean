/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator

/-! Genuine mixed cutoff Newtonian operators and their quantitative dependence on both cutoffs. -/

@[expose] public section


noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest
open scoped ContDiff

@[ext] theorem Cutoff.ext {χ ψ : Cutoff} (h : χ.field = ψ.field) : χ = ψ := by
  cases χ
  cases ψ
  cases h
  rfl

/-- Add, given by `⟨χ.field + ψ.field, χ.smooth.add ψ.smooth, χ.compact.add ψ.compact⟩`. -/
def Cutoff.add (χ ψ : Cutoff) : Cutoff :=
  ⟨χ.field + ψ.field, χ.smooth.add ψ.smooth, χ.compact.add ψ.compact⟩

/-- Scale, given by `⟨c • χ.field, χ.smooth.const_smul c, χ.compact.comp_left (g := fun t : ℝ =>
c • t) (smul_zero c)⟩`. -/
def Cutoff.scale (χ : Cutoff) (c : ℝ) : Cutoff :=
  ⟨c • χ.field, χ.smooth.const_smul c,
    χ.compact.comp_left (g := fun t : ℝ => c • t) (smul_zero c)⟩

/-- Sub, given by `⟨χ.field - ψ.field, χ.smooth.sub ψ.smooth, χ.compact.sub ψ.compact⟩`. -/
def Cutoff.sub (χ ψ : Cutoff) : Cutoff :=
  ⟨χ.field - ψ.field, χ.smooth.sub ψ.smooth, χ.compact.sub ψ.compact⟩

/-- Translate, given by `⟨fun x => χ.field (x+a), χ.smooth.comp (contDiff_id.add
contDiff_const), χ.compact.comp_homeomorph (Homeomorph.addRight a)⟩`. -/
def Cutoff.translate (χ : Cutoff) (a : Space) : Cutoff :=
  ⟨fun x => χ.field (x+a), χ.smooth.comp (contDiff_id.add contDiff_const),
    χ.compact.comp_homeomorph (Homeomorph.addRight a)⟩

/-- Derivative, given by `⟨partialDerivative χ.field i, contDiff_partialDerivative χ.field
χ.smooth i, χ.compact.fderiv_apply ℝ (EuclideanSpace.single i 1)⟩`. -/
def Cutoff.derivative (χ : Cutoff) (i : Fin 3) : Cutoff :=
  ⟨partialDerivative χ.field i, contDiff_partialDerivative χ.field χ.smooth i,
    χ.compact.fderiv_apply ℝ (EuclideanSpace.single i 1)⟩

theorem testCurl_cutoff_add (χ ψ : Cutoff) (f : Test) :
    testCurl (χ.add ψ) f = testCurl χ f + testCurl ψ f := by
  apply Lp.ext
  filter_upwards [testCurl_ae (χ.add ψ) f, testCurl_ae χ f, testCurl_ae ψ f,
    Lp.coeFn_add (testCurl χ f) (testCurl ψ f)] with x hsum hχ hψ ha
  rw [hsum, ha]
  simp only [Pi.add_apply]
  rw [hχ, hψ]
  have heq : (fun y => (χ.add ψ).field y • (f : Space → Space) y) =
      (fun y => χ.field y • (f : Space → Space) y) +
        (fun y => ψ.field y • (f : Space → Space) y) := by
    funext y
    exact add_smul _ _ _
  rw [heq]
  exact congrFun (vectorCurl_add (fun y => χ.field y • (f : Space → Space) y)
    (fun y => ψ.field y • (f : Space → Space) y)
    ((χ.smooth.smul f.smooth).differentiable (by simp))
    ((ψ.smooth.smul f.smooth).differentiable (by simp))) x

theorem testCurl_cutoff_scale (χ : Cutoff) (c : ℝ) (f : Test) :
    testCurl (χ.scale c) f = c • testCurl χ f := by
  apply Lp.ext
  filter_upwards [testCurl_ae (χ.scale c) f, testCurl_ae χ f,
    Lp.coeFn_smul c (testCurl χ f)] with x hscale hχ hs
  rw [hscale, hs]
  simp only [Pi.smul_apply]
  rw [hχ]
  have heq : (fun y => (χ.scale c).field y • (f : Space → Space) y) =
      c • (fun y => χ.field y • (f : Space → Space) y) := by
    funext y
    exact smul_assoc c (χ.field y) ((f : Space → Space) y)
  rw [heq]
  exact congrFun (vectorCurl_smul c (fun y => χ.field y • (f : Space → Space) y)
    ((χ.smooth.smul f.smooth).differentiable (by simp))) x

theorem cutoffCurl_add (χ ψ : Cutoff) :
    cutoffCurl (χ.add ψ) = cutoffCurl χ + cutoffCurl ψ := by
  apply ContinuousLinearMap.ext
  intro u
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq (cutoffCurl (χ.add ψ)).continuous
      ((cutoffCurl χ).continuous.add (cutoffCurl ψ).continuous)
  · intro f
    change cutoffCurl (χ.add ψ) (homogeneousGradient f) =
      cutoffCurl χ (homogeneousGradient f) + cutoffCurl ψ (homogeneousGradient f)
    rw [cutoffCurl_on_test, cutoffCurl_on_test, cutoffCurl_on_test]
    exact testCurl_cutoff_add χ ψ f

theorem cutoffCurl_scale (χ : Cutoff) (c : ℝ) :
    cutoffCurl (χ.scale c) = c • cutoffCurl χ := by
  apply ContinuousLinearMap.ext
  intro u
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq (cutoffCurl (χ.scale c)).continuous
      ((cutoffCurl χ).continuous.const_smul c)
  · intro f
    change cutoffCurl (χ.scale c) (homogeneousGradient f) =
      c • cutoffCurl χ (homogeneousGradient f)
    rw [cutoffCurl_on_test, cutoffCurl_on_test]
    exact testCurl_cutoff_scale χ c f

theorem cutoffCurl_sub (χ ψ : Cutoff) :
    cutoffCurl (χ.sub ψ) = cutoffCurl χ - cutoffCurl ψ := by
  have heq : χ.sub ψ = χ.add (ψ.scale (-1)) := by
    apply Cutoff.ext
    ext x
    simp [Cutoff.sub, Cutoff.add, Cutoff.scale, sub_eq_add_neg]
  rw [heq, cutoffCurl_add, cutoffCurl_scale]
  apply ContinuousLinearMap.ext
  intro u
  change cutoffCurl χ u + (-1 : ℝ) • cutoffCurl ψ u = cutoffCurl χ u - cutoffCurl ψ u
  rw [neg_one_smul ℝ, sub_eq_add_neg]

theorem weakPotential_add (χ ψ : Cutoff) :
    weakPotential (χ.add ψ) = weakPotential χ + weakPotential ψ := by
  simp only [weakPotential, cutoffCurl_add, map_add]

theorem weakPotential_scale (χ : Cutoff) (c : ℝ) :
    weakPotential (χ.scale c) = c • weakPotential χ := by
  simp only [weakPotential, cutoffCurl_scale, map_smul]

theorem weakPotential_sub (χ ψ : Cutoff) :
    weakPotential (χ.sub ψ) = weakPotential χ - weakPotential ψ := by
  have heq : χ.sub ψ = χ.add (ψ.scale (-1)) := by
    apply Cutoff.ext
    ext x
    simp [Cutoff.sub, Cutoff.add, Cutoff.scale, sub_eq_add_neg]
  rw [heq, weakPotential_add, weakPotential_scale]
  apply ContinuousLinearMap.ext
  intro z
  change weakPotential χ z + (-1 : ℝ) • weakPotential ψ z = weakPotential χ z - weakPotential ψ z
  rw [neg_one_smul ℝ, sub_eq_add_neg]

/-- The literal weak `curl χ (-Δ)⁻¹ ψ curl` operator. -/
def mixedBoundaryOperator (χ ψ : Cutoff) : L2 →L[ℝ] L2 :=
  (cutoffCurl χ).comp (weakPotential ψ)

theorem mixedBoundaryOperator_diagonal (χ : Cutoff) :
    mixedBoundaryOperator χ χ = boundaryOperator χ := rfl

theorem mixedBoundaryOperator_norm_le (χ ψ : Cutoff) :
    ‖mixedBoundaryOperator χ ψ‖ ≤ cutoffBound χ * cutoffBound ψ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  change ‖cutoffCurl χ‖ * ‖(cutoffCurl ψ).adjoint‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul (cutoffCurl_norm_le χ) (cutoffCurl_norm_le ψ)
    (norm_nonneg (cutoffCurl ψ)) (cutoffBound_nonneg χ)

theorem mixedBoundaryOperator_pairing (χ ψ : Cutoff) (u v : L2) :
    ⟪mixedBoundaryOperator χ ψ u, v⟫_ℝ = ⟪weakPotential ψ u, weakPotential χ v⟫_ℝ :=
  (ContinuousLinearMap.adjoint_inner_right (cutoffCurl χ) (weakPotential ψ u) v).symm

theorem mixedBoundaryOperator_adjoint (χ ψ : Cutoff) :
    (mixedBoundaryOperator χ ψ).adjoint = mixedBoundaryOperator ψ χ := by
  simp only [mixedBoundaryOperator, weakPotential, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem mixedBoundaryOperator_solenoidal (χ ψ : Cutoff) (u : L2) :
    mixedBoundaryOperator χ ψ u ∈ solenoidalSpace := cutoffCurl_solenoidal χ (weakPotential ψ u)

theorem mixedBoundaryOperator_supported (χ ψ : Cutoff) (u : L2) :
    mixedBoundaryOperator χ ψ u ∈ supportedSpace χ := cutoffCurl_supported χ (weakPotential ψ u)

theorem mixedBoundaryOperator_add_left (χ ψ ρ : Cutoff) :
    mixedBoundaryOperator (χ.add ψ) ρ = mixedBoundaryOperator χ ρ + mixedBoundaryOperator ψ ρ := by
  simp only [mixedBoundaryOperator, cutoffCurl_add, ContinuousLinearMap.add_comp]

theorem mixedBoundaryOperator_add_right (χ ψ ρ : Cutoff) :
    mixedBoundaryOperator χ (ψ.add ρ) = mixedBoundaryOperator χ ψ + mixedBoundaryOperator χ ρ := by
  simp only [mixedBoundaryOperator, weakPotential_add, ContinuousLinearMap.comp_add]

theorem mixedBoundaryOperator_scale_left (χ ψ : Cutoff) (c : ℝ) :
    mixedBoundaryOperator (χ.scale c) ψ = c • mixedBoundaryOperator χ ψ := by
  simp only [mixedBoundaryOperator, cutoffCurl_scale, ContinuousLinearMap.smul_comp]

theorem mixedBoundaryOperator_scale_right (χ ψ : Cutoff) (c : ℝ) :
    mixedBoundaryOperator χ (ψ.scale c) = c • mixedBoundaryOperator χ ψ := by
  simp only [mixedBoundaryOperator, weakPotential_scale, ContinuousLinearMap.comp_smul]

theorem mixedBoundaryOperator_sub_left (χ ψ ρ : Cutoff) :
    mixedBoundaryOperator (χ.sub ψ) ρ = mixedBoundaryOperator χ ρ - mixedBoundaryOperator ψ ρ := by
  simp only [mixedBoundaryOperator, cutoffCurl_sub, ContinuousLinearMap.sub_comp]

theorem mixedBoundaryOperator_sub_right (χ ψ ρ : Cutoff) :
    mixedBoundaryOperator χ (ψ.sub ρ) = mixedBoundaryOperator χ ψ - mixedBoundaryOperator χ ρ := by
  simp only [mixedBoundaryOperator, weakPotential_sub, ContinuousLinearMap.comp_sub]

/-- The two actual coefficient differences are split between the two cutoff positions. -/
theorem mixedBoundaryOperator_difference (χ₁ χ₀ ψ₁ ψ₀ : Cutoff) :
    mixedBoundaryOperator χ₁ ψ₁ - mixedBoundaryOperator χ₀ ψ₀ =
      mixedBoundaryOperator (χ₁.sub χ₀) ψ₁ + mixedBoundaryOperator χ₀ (ψ₁.sub ψ₀) := by
  rw [mixedBoundaryOperator_sub_left, mixedBoundaryOperator_sub_right]
  abel

theorem mixedBoundaryOperator_difference_norm_le (χ₁ χ₀ ψ₁ ψ₀ : Cutoff) :
    ‖mixedBoundaryOperator χ₁ ψ₁ - mixedBoundaryOperator χ₀ ψ₀‖ ≤
      cutoffBound (χ₁.sub χ₀) * cutoffBound ψ₁ + cutoffBound χ₀ * cutoffBound (ψ₁.sub ψ₀) := by
  rw [mixedBoundaryOperator_difference]
  exact (norm_add_le _ _).trans (add_le_add (mixedBoundaryOperator_norm_le _ _)
    (mixedBoundaryOperator_norm_le _ _))

end EulerMeanBoundary
