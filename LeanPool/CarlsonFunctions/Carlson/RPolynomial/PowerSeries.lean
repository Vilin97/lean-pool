/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Basic
public import LeanPool.CarlsonFunctions.Dirichlet.Average.PowerSeries

/-!
# Power-series representations using Carlson R-polynomials

This file provides the native integral representation and the Taylor-series
definition. `Carlson.RPolynomial.TaylorContinuation` proves convergence on the
full disk of holomorphy and joint analyticity in parameters and nodes.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Translation of Carlson's variables by the center of a power-series expansion. -/
def shiftCarlsonVariables (A : ℂ) (z : ι → ℂ) : ι → ℂ :=
  fun i ↦ z i - A

/-- Carlson's Representation 5.7-2 in regularized form. The hypotheses state uniform
summable domination and pointwise summation of the scalar power series on the convex hull of
the supplied variables. -/
theorem hasSum_regCarlsonR_of_powerSeries
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (A : ℂ) (a : ℕ → ℂ)
    (z : ι → ℂ) (f : ℂ → ℂ) (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
      ‖a n * (carlsonAffineForm z u - A) ^ n‖ ≤ M n)
    (hsum : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
      HasSum (fun n ↦ a n * (carlsonAffineForm z u - A) ^ n)
        (f (carlsonAffineForm z u))) :
    HasSum (fun n ↦ a n * regCarlsonR n (shiftCarlsonVariables A z) b)
      (regCarlsonDirichletAverage b z f) := by
  let g : ℕ → ℂ → ℂ := fun n w ↦ a n * (w - A) ^ n
  have hg (n : ℕ) : ContinuousOn (fun u : ι → ℝ ↦ g n (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) := by
    exact (continuous_const.mul
      (((continuous_carlsonAffineForm z).sub continuous_const).pow n)).continuousOn
  have h := hasSum_regCarlsonDirichletAverage hb z g f M hg hM hbound hsum
  apply h.congr_fun
  intro n
  have hkernel : Set.EqOn
      (fun u : ι → ℝ ↦ g n (carlsonAffineForm z u))
      (fun u ↦ a n * carlsonAffineForm (shiftCarlsonVariables A z) u ^ n)
      (Convexity.StdSimplex.coordinateSet ℝ ι) := by
    intro u hu
    dsimp only [g]
    rw [show shiftCarlsonVariables A z = fun i ↦ 1 * z i + (-A) by
      funext i
      simp [shiftCarlsonVariables, sub_eq_add_neg]]
    rw [carlsonAffineForm_affine hu]
    simp [sub_eq_add_neg]
  calc
    a n * regCarlsonR n (shiftCarlsonVariables A z) b =
        regDirichletIntegral b
          (fun u ↦ a n * carlsonAffineForm (shiftCarlsonVariables A z) u ^ n) := by
      rw [regDirichletIntegral_smul]
      · congr 1
        simpa [regCarlsonDirichletAverage] using
          (regCarlsonDirichletAverage_pow n (shiftCarlsonVariables A z) hb).symm
    _ = regCarlsonDirichletAverage b z (g n) := by
      unfold regCarlsonDirichletAverage
      exact (regDirichletIntegral_congr b hkernel).symm

/-- The R-polynomial Taylor series for Carlson's regularized Dirichlet average.
Its convergence and continuation properties are proved in
`Carlson.RPolynomial.TaylorContinuation`. -/
def regCarlsonTaylorSeries (A : ℂ) (a : ℕ → ℂ) (z b : ι → ℂ) : ℂ :=
  ∑' n, a n * regCarlsonR n (fun i ↦ z i - A) b

/-- Each term of Carlson's Taylor-series construction is entire in the Dirichlet parameters. -/
theorem differentiable_regCarlsonTaylorTerm (A : ℂ) (a : ℕ → ℂ) (z : ι → ℂ) (n : ℕ) :
    Differentiable ℂ
      (fun b ↦ a n * regCarlsonR n (fun i ↦ z i - A) b) := by
  exact (differentiable_const (c := a n)).mul
    (differentiable_regCarlsonR n fun i ↦ z i - A)

/-- Every finite partial sum in Carlson's Taylor-series construction is entire in the
Dirichlet parameters. -/
theorem differentiable_regCarlsonTaylorPartialSum
    (A : ℂ) (a : ℕ → ℂ) (z : ι → ℂ) (N : ℕ) :
    Differentiable ℂ
      (fun b ↦ ∑ n ∈ Finset.range N, a n * regCarlsonR n (fun i ↦ z i - A) b) := by
  rw [show (fun b ↦ ∑ n ∈ Finset.range N,
      a n * regCarlsonR n (fun i ↦ z i - A) b) =
      ∑ n ∈ Finset.range N,
        (fun b ↦ a n * regCarlsonR n (fun i ↦ z i - A) b) by
    funext b
    simp]
  exact Differentiable.sum fun n _ ↦ differentiable_regCarlsonTaylorTerm A a z n

end DirichletTransform

end
