/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration

/-!
# Spatial derivatives of Fourier test functions

These operators use the same coordinate vectors and spatial partial derivatives
as the equation.  Their Fourier identities include the `2π` normalization of
Mathlib's Fourier transform.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace NavierStokesR3.HarmonicTestFunctionals

open ProblemStatement Comparison

/-- Coordinate differentiation on Schwartz tests. -/
def partialCLM (i : Fin 3) : ComplexTest →L[ℂ] ComplexTest :=
  LineDeriv.lineDerivOpCLM ℂ ComplexTest (NavierStokes.ProblemStatement.coordinateVector i)

/-- The ordinary spatial Laplacian acting on Schwartz tests. -/
def laplacianCLM : ComplexTest →L[ℂ] ComplexTest :=
  ∑ i : Fin 3, (partialCLM i).comp (partialCLM i)

@[simp] theorem partialCLM_apply (i : Fin 3) (ψ : ComplexTest) (x : Space) :
    partialCLM i ψ x =
      NavierStokes.PeriodicIntegration.spatialPartial i (ψ : Space → ℂ) x := rfl

@[simp] theorem laplacianCLM_apply (ψ : ComplexTest) (x : Space) :
    laplacianCLM ψ x =
      ∑ i : Fin 3, NavierStokes.PeriodicIntegration.spatialPartial i
        (fun y => NavierStokes.PeriodicIntegration.spatialPartial i (ψ : Space → ℂ) y) x := by
  simp [laplacianCLM, Fin.sum_univ_succ, partialCLM,
    NavierStokes.PeriodicIntegration.spatialPartial, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

/-- Fourier transform of a coordinate derivative. -/
theorem fourier_partialCLM_apply (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
    EulerSobolev.schwartzFourier (partialCLM i ψ) ξ =
      (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) *
        EulerSobolev.schwartzFourier ψ ξ := by
  change FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ =
      (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) *
        FourierTransform.fourierCLE ℂ ComplexTest ψ ξ
  have hd : Integrable (fderiv ℝ (ψ : Space → ℂ)) := by
    exact (SchwartzMap.fderivCLM ℂ Space ℂ ψ).integrable
  change 𝓕 (fun x => fderiv ℝ (ψ : Space → ℂ) x
    (NavierStokes.ProblemStatement.coordinateVector i)) ξ = _
  rw [← Real.fourier_continuousLinearMap_apply hd,
    Real.fourier_fderiv ψ.integrable ψ.differentiable hd]
  simp only [NavierStokes.ProblemStatement.coordinateVector, VectorFourier.fourierSMulRight_apply,
      mul_assoc,
    neg_apply, neg_smul, Complex.real_smul, smul_eq_mul, mul_neg, neg_mul, neg_neg,
        FourierTransform.fourierCLE_apply,
    SchwartzMap.fourier_coe, mul_eq_mul_left_iff, mul_eq_mul_right_iff, Complex.ofReal_inj,
        Complex.I_ne_zero, or_false,
    Complex.ofReal_eq_zero, Real.pi_ne_zero, OfNat.ofNat_ne_zero]
  left
  change inner ℝ ξ (EuclideanSpace.single i 1) = ξ i
  simpa using! (EuclideanSpace.inner_single_right i (1 : ℝ) ξ)

/-- The ordinary Laplacian has Fourier multiplier `-4π²‖ξ‖²`. -/
theorem fourier_laplacianCLM_apply (ψ : ComplexTest) (ξ : Space) :
    EulerSobolev.schwartzFourier (laplacianCLM ψ) ξ =
      (-(4 * (Real.pi : ℂ) ^ 2) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) *
        EulerSobolev.schwartzFourier ψ ξ := by
  change FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ) ξ =
      (-(4 * (Real.pi : ℂ) ^ 2) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) *
        FourierTransform.fourierCLE ℂ ComplexTest ψ ξ
  have hnorm : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
  have hsplit : laplacianCLM ψ = partialCLM 0 (partialCLM 0 ψ) +
      (partialCLM 1 (partialCLM 1 ψ) + partialCLM 2 (partialCLM 2 ψ)) := by
    simp [laplacianCLM, Fin.sum_univ_succ]
  rw [hsplit, map_add, map_add]
  change FourierTransform.fourierCLE ℂ ComplexTest (partialCLM 0 (partialCLM 0 ψ)) ξ +
      (FourierTransform.fourierCLE ℂ ComplexTest (partialCLM 1 (partialCLM 1 ψ)) ξ +
       FourierTransform.fourierCLE ℂ ComplexTest (partialCLM 2 (partialCLM 2 ψ)) ξ) = _
  have hpartial (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
      FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ =
        (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) *
          FourierTransform.fourierCLE ℂ ComplexTest ψ ξ := fourier_partialCLM_apply i ψ ξ
  simp_rw [hpartial]
  rw [hnorm]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

end NavierStokesR3.HarmonicTestFunctionals
