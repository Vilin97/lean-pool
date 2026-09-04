/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.AugmentedParameterization
import LeanPool.Feige.TwoPointProductLaw

/-!
# Conditional calibration of augmented two-point products

The finite combinatorial theorem is isolated as a reusable proposition.
Once it is available (including boundary values `γᵢ = 0`), the actual
conditional product law selected by any admissible augmented latent vector
inherits the same rejection bound.
-/

open MeasureTheory

namespace Feige

noncomputable section

/-- The finite two-point rejection estimate needed by the mixture
argument, including the closed boundary `0 ≤ γᵢ ≤ 1`. -/
def TwoPointRejectionBound : Prop :=
  ∀ {m : ℕ} (γ β : Fin m → ℝ),
    (∀ i, 0 ≤ γ i) →
    (∀ i, γ i ≤ 1) →
    (∀ i, 0 < β i) →
    ∀ {α : ℝ}, 0 ≤ α →
      twoPointRejectionMass γ β α ≤ α

/-- Pointwise calibration of the ordinary product law associated with an
admissible augmented parameter vector. -/
theorem augmentedConditionalProduct_rejection_le
    (htwo : TwoPointRejectionBound)
    {n : ℕ} (p : Fin n → AugmentedTwoPointParams)
    (hp : AugmentedParamsNonnegative p)
    {α : ℝ} (hα : 0 ≤ α) :
    (augmentedConditionalProduct p).real
        {y | dirichletK y ≤ α} ≤ α := by
  rw [augmentedConditionalProduct_eq_twoPointProduct]
  rw [twoPointProductLaw_rejection
    (fun i ↦ augmentedGamma (p i))
    (fun i ↦ augmentedBeta (p i))
    (augmentedGamma_nonneg hp)
    (augmentedBeta_pos hp) α]
  exact htwo
    (fun i ↦ augmentedGamma (p i))
    (fun i ↦ augmentedBeta (p i))
    (augmentedGamma_nonneg hp)
    (augmentedGamma_le_one hp)
    (augmentedBeta_pos hp) hα

/-- The recursively measurable conditional kernel has the same pointwise
rejection estimate. -/
theorem recursiveAugmentedKernel_rejection_le
    (htwo : TwoPointRejectionBound)
    {n : ℕ} (p : Fin n → AugmentedTwoPointParams)
    (hp : AugmentedParamsNonnegative p)
    {α : ℝ} (hα : 0 ≤ α) :
    (recursiveAugmentedKernel n p).real
        {y | dirichletK y ≤ α} ≤ α := by
  rw [recursiveAugmentedKernel_apply_eq_conditionalProduct]
  exact augmentedConditionalProduct_rejection_le htwo p hp hα

end

end Feige
