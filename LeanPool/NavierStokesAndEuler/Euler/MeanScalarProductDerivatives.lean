/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicEnergy
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import Mathlib.Algebra.Order.Star.Real

/-! Scalar coordinate product rules for the localized harmonic estimates. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open InnerProductSpace EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

theorem partialDerivative_add {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    partialDerivative (f + g) i x = partialDerivative f i x + partialDerivative g i x := by
  unfold partialDerivative
  rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  rfl

theorem partialDerivative_mul {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    partialDerivative (f * g) i x = g x * partialDerivative f i x + f x * partialDerivative g i x
        := by
  rw [← gradient_coordinate, gradient_mul hf hg]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gradient_coordinate]

theorem secondPartial_mul (f g : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin 3) (x : Space) :
    partialDerivative (partialDerivative (f * g) i) i x =
      g x * partialDerivative (partialDerivative f i) i x +
        2 * partialDerivative f i x * partialDerivative g i x +
        f x * partialDerivative (partialDerivative g i) i x := by
  have heq : partialDerivative (f * g) i =
      g * partialDerivative f i + f * partialDerivative g i := by
    funext y
    exact partialDerivative_mul ((hf.differentiable (by simp)).differentiableAt)
      ((hg.differentiable (by simp)).differentiableAt) i
  have hdf := contDiff_partialDerivative f hf i
  have hdg := contDiff_partialDerivative g hg i
  have h₁ : DifferentiableAt ℝ (g * partialDerivative f i) x :=
    ((hg.mul hdf).differentiable (by simp)).differentiableAt
  have h₂ : DifferentiableAt ℝ (f * partialDerivative g i) x :=
    ((hf.mul hdg).differentiable (by simp)).differentiableAt
  rw [heq, partialDerivative_add h₁ h₂ i,
    partialDerivative_mul (f := g) (g := partialDerivative f i)
      ((hg.differentiable (by simp)).differentiableAt)
      ((hdf.differentiable (by simp)).differentiableAt),
    partialDerivative_mul (f := f) (g := partialDerivative g i)
      ((hf.differentiable (by simp)).differentiableAt)
      ((hdg.differentiable (by simp)).differentiableAt)]
  ring

theorem sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

end EulerMeanHarmonic
