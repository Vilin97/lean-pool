/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic
public import LeanPool.CarlsonFunctions.Dirichlet.Polynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Carlson's R-polynomials -/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The entire regularized Carlson polynomial `Rₙ(b,z) / Γ(∑ i, b i)`. -/
def regCarlsonRPolynomial (n : ℕ) (b z : ι → ℂ) : ℂ :=
  regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b

/-- Compatibility spelling using the argument order of the original implementation. -/
abbrev regCarlsonR (n : ℕ) (z b : ι → ℂ) : ℂ :=
  regCarlsonRPolynomial n b z

/-- On the ordinary convergence region, the regularized Carlson polynomial agrees with the
native Dirichlet average of the corresponding power. -/
theorem regCarlsonDirichletAverage_pow (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b z (fun w ↦ w ^ n) = regCarlsonR n z b := by
  unfold regCarlsonDirichletAverage
  change regDirichletIntegral b (fun u ↦ carlsonAffineForm z u ^ n) =
    regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z) b
  rw [← regDirichletIntegral_mvPolynomial b hb (carlsonPowerPolynomial n z)]
  congr 1
  funext u
  exact (eval_carlsonPowerPolynomial n z u).symm

/-- For fixed degree and Carlson variables, the regularized Carlson polynomial is entire in
the Dirichlet parameters. -/
theorem differentiable_regCarlsonR (n : ℕ) (z : ι → ℂ) :
    Differentiable ℂ (regCarlsonR n z) :=
  differentiable_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

/-- Analytic form of entire dependence on the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonR (n : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonR n z) Set.univ :=
  analyticOnNhd_regDirichletMvPolynomialTransform (carlsonPowerPolynomial n z)

/-- The multivariate polynomial kernel defining the Carlson polynomial is homogeneous in its
Carlson variables. -/
theorem carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z : ι → ℂ) :
    carlsonPowerPolynomial n (fun i ↦ a * z i) =
      MvPolynomial.C (a ^ n) * carlsonPowerPolynomial n z := by
  unfold carlsonPowerPolynomial carlsonAffinePolynomial
  rw [show (∑ i, MvPolynomial.C (a * z i) * MvPolynomial.X i) =
      MvPolynomial.C a * ∑ i, MvPolynomial.C (z i) * MvPolynomial.X i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_assoc]]
  rw [mul_pow, MvPolynomial.C_pow]

/-- Evaluation of a translated and scaled Carlson power kernel gives the corresponding
binomial power. -/
theorem eval_carlsonPowerPolynomial_affine (n : ℕ) (a t : ℂ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i + t)).eval (fun i ↦ (u i : ℂ)) =
      (a * carlsonAffineForm z u + t) ^ n := by
  rw [eval_carlsonPowerPolynomial, carlsonAffineForm_affine hu]

/-- Carlson's degree-`n` regularized R-polynomial is homogeneous in its variables on the
native convergence domain.  This is the homogeneous-polynomial observation following
Definition 5.7-1. -/
theorem regCarlsonR_smul_of_mem_mvBetaConvergent (n : ℕ) (a : ℂ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonR n (fun i => a * z i) b = a ^ n * regCarlsonR n z b := by
  rw [← regCarlsonDirichletAverage_pow n _ hb,
    ← regCarlsonDirichletAverage_pow n z hb]
  unfold regCarlsonDirichletAverage
  calc
    regDirichletIntegral b (fun u => carlsonAffineForm (fun i => a * z i) u ^ n) =
        regDirichletIntegral b (fun u => a ^ n * carlsonAffineForm z u ^ n) := by
      apply regDirichletIntegral_congr
      intro u hu
      rw [show (fun i => a * z i) = fun i => a * z i + 0 by simp]
      dsimp only
      rw [carlsonAffineForm_affine hu]
      simp [mul_pow]
    _ = a ^ n * regDirichletIntegral b (fun u => carlsonAffineForm z u ^ n) :=
      regDirichletIntegral_smul b _ _

/-- The restriction of a regularized R-polynomial to the diagonal, corresponding to
Carlson's equation 5.7(3). -/
theorem regCarlsonR_const (n : ℕ) (w : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    regCarlsonR n (fun _ => w) b = w ^ n / Gamma (∑ i, b i) := by
  rw [← regCarlsonDirichletAverage_pow n _ hb]
  exact regCarlsonDirichletAverage_const (fun x => x ^ n) w hb

end DirichletTransform
end CarlsonRPolynomial
