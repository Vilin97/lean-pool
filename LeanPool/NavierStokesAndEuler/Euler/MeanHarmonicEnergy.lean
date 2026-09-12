/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local energy identities for the harmonic part of the mean inverse

The mean inverse requires an interior L² estimate for a genuinely harmonic
field. This file starts that argument with the classical localized energy
identity, proved by ordinary-space integration by parts. No interior estimate
or mean-value formula is assumed.
-/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
open scoped ContDiff

theorem gradient_mul {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (f * g) x =
      g x • gradient f x + f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradient_left, inner_gradient_left]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem localized_gradient_identity (η h : Space → ℝ)
    (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h) (x : Space) :
    ‖gradient (η * h) x‖ ^ 2 =
      ⟪gradient (η * (η * h)) x, gradient h x⟫_ℝ +
        h x ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hdη : DifferentiableAt ℝ η x := (hη.differentiable (by simp)).differentiableAt
  have hdh : DifferentiableAt ℝ h x := (hh.differentiable (by simp)).differentiableAt
  rw [← real_inner_self_eq_norm_sq,
    gradient_mul hdη hdh, gradient_mul hdη (hdη.mul hdh), gradient_mul hdη hdh]
  simp only [Pi.mul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [real_inner_comm (gradient h x) (gradient η x)]
  ring

/-- Exact localized Dirichlet-energy identity for a classical harmonic scalar. -/
theorem caccioppoli_identity (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h)
    (hharmonic : ∀ x ∈ tsupport η, divergence (gradient h) x = 0) :
    (∫ x, ‖gradient (η * h) x‖ ^ 2) =
      ∫ x, h x ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hcProduct : HasCompactSupport (η * h) := hcη.mul_right (f' := h)
  have hcGradient : HasCompactSupport (gradient (η * h)) := compactSupport_gradient hcProduct
  have hcGradientη : HasCompactSupport (gradient η) := compactSupport_gradient hcη
  have hcSquaredη : HasCompactSupport (fun x => ‖gradient η x‖ ^ 2) :=
    hcGradientη.comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)
  have hcompactA : HasCompactSupport (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    hcGradient.comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)
  have hcompactC : HasCompactSupport (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) :=
    hcSquaredη.mul_left (f := fun x => h x ^ 2)
  have hA : Integrable (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    ((contDiff_gradient (hη.mul hh)).continuous.norm.pow 2).integrable_of_hasCompactSupport
        hcompactA
  have hC : Integrable (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) :=
    ((hh.continuous.pow 2).mul ((contDiff_gradient hη).continuous.norm.pow
        2)).integrable_of_hasCompactSupport
      hcompactC
  have hcTest : HasCompactSupport (η * (η * h)) := hcη.mul_right (f' := η * h)
  have hip := gradient_test_integration_by_parts (gradient h) (contDiff_gradient hh)
    (η * (η * h)) hcTest (hη.mul (hη.mul hh))
  have hzero (x : Space) : η x * (η x * h x) * divergence (gradient h) x = 0 := by
    by_cases hx : x ∈ tsupport η
    · rw [hharmonic x hx, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      ring
  simp only [Pi.mul_apply] at hip
  simp_rw [hzero] at hip
  simp only [integral_zero, neg_zero] at hip
  have hrewrite : (fun x =>
      ⟪gradient (η * (η * h)) x, gradient h x⟫_ℝ) =
      (fun x => ‖gradient (η * h) x‖ ^ 2 - h x ^ 2 * ‖gradient η x‖ ^ 2) := by
    funext x
    linarith [localized_gradient_identity η h hη hh x]
  rw [hrewrite, integral_sub hA hC] at hip
  exact sub_eq_zero.mp hip

end EulerMeanHarmonic
