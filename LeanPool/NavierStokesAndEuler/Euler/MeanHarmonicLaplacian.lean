/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicEnergy
import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
import Mathlib.Algebra.Order.Star.Real

/-! Canonical Laplacian and the quantitative local harmonic energy bound. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal
open scoped ContDiff

theorem gradient_coordinate (f : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient f x i = partialDerivative f i x := by
  simpa only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, partialDerivative]
    using (inner_gradient_left (f := f) (x := x) (y := EuclideanSpace.single i 1))

theorem laplacian_eq_coordinate_sum (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (x : Space) :
    Δ f x = ∑ i : Fin 3, partialDerivative (partialDerivative f i) i x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, partialDerivative]
  change _ = (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x)
    (EuclideanSpace.single i 1)
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

/-- The Laplacian used in the harmonic argument is the canonical one. -/
theorem divergence_gradient_eq_laplacian (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (x : Space) :
    divergence (gradient f) x = Δ f x := by
  rw [divergence_eq_coordinate_sum, laplacian_eq_coordinate_sum f hf x]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fderiv_coordinate (gradient f) x
    (((contDiff_gradient hf).differentiable (by simp)).differentiableAt) i]
  have heq : (fun y => gradient f y i) = partialDerivative f i :=
    funext fun y => gradient_coordinate f y i
  rw [heq]
  rfl

theorem caccioppoli_identity_of_laplacian (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h)
    (hharmonic : ∀ x ∈ tsupport η, Δ h x = 0) :
    (∫ x, ‖gradient (η * h) x‖ ^ 2) = ∫ x, h x ^ 2 * ‖gradient η x‖ ^ 2 :=
  caccioppoli_identity η h hcη hη hh
    (fun x hx => (divergence_gradient_eq_laplacian h hh x).trans (hharmonic x hx))

private theorem norm_sub_sq_le_twice (a b : Space) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The usual Caccioppoli inequality, with an explicit universal constant. -/
theorem caccioppoli_bound (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h)
    (hharmonic : ∀ x ∈ tsupport η, Δ h x = 0) :
    (∫ x, η x ^ 2 * ‖gradient h x‖ ^ 2) ≤
      4 * ∫ x, h x ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hcProduct : HasCompactSupport (η * h) := hcη.mul_right (f' := h)
  have hcA : HasCompactSupport (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    (compactSupport_gradient hcProduct).comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)
  have hcC : HasCompactSupport (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) :=
    ((compactSupport_gradient hcη).comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)).mul_left
      (f := fun x => h x ^ 2)
  have hcD : HasCompactSupport (fun x => η x ^ 2 * ‖gradient h x‖ ^ 2) :=
    (hcη.comp_left (g := fun s : ℝ => s ^ 2) (by simp)).mul_right
      (f' := fun x => ‖gradient h x‖ ^ 2)
  have hA : Integrable (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    ((contDiff_gradient (hη.mul hh)).continuous.norm.pow 2).integrable_of_hasCompactSupport hcA
  have hC : Integrable (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) :=
    ((hh.continuous.pow 2).mul ((contDiff_gradient hη).continuous.norm.pow
        2)).integrable_of_hasCompactSupport hcC
  have hD : Integrable (fun x => η x ^ 2 * ‖gradient h x‖ ^ 2) :=
    ((hη.continuous.pow 2).mul ((contDiff_gradient hh).continuous.norm.pow
        2)).integrable_of_hasCompactSupport hcD
  have hpoint (x : Space) : η x ^ 2 * ‖gradient h x‖ ^ 2 ≤
      2 * ‖gradient (η * h) x‖ ^ 2 + 2 * (h x ^ 2 * ‖gradient η x‖ ^ 2) := by
    have heq : η x • gradient h x = gradient (η * h) x - h x • gradient η x := by
      rw [gradient_mul ((hη.differentiable (by simp)).differentiableAt)
        ((hh.differentiable (by simp)).differentiableAt)]
      abel
    have hnorm := norm_sub_sq_le_twice (gradient (η * h) x) (h x • gradient η x)
    rw [← heq] at hnorm
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hnorm
  have hint := integral_mono hD ((hA.const_mul 2).add (hC.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hA.const_mul 2) (hC.const_mul 2), integral_const_mul,
    integral_const_mul, caccioppoli_identity_of_laplacian η h hcη hη hh hharmonic] at hint
  linarith

end EulerMeanHarmonic
