/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Native Carlson S-integrals -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The native regularized integral representing `S(b,z) / Γ(∑ i, b i)` when all Dirichlet
parameters have positive real part. -/
def regCarlsonSIntegral (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z exp

/-- For each simplex point, the exponential Carlson kernel is entire in all `z` variables. -/
theorem analyticOnNhd_exp_carlsonAffineForm (u : ι → ℝ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ ↦ exp (carlsonAffineForm z u)) Set.univ := by
  intro z _
  apply analyticAt_cexp.comp
  unfold carlsonAffineForm
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)

/-- Varying coordinate `i` of `z`, the derivative of the exponential Carlson kernel is the
kernel multiplied by the simplex coordinate `u i`. -/
theorem hasDerivAt_exp_carlsonAffineForm_update
    (z : ι → ℂ) (u : ι → ℝ) (i : ι) :
    HasDerivAt (fun w ↦ exp (carlsonAffineForm (Function.update z i w) u))
      ((u i : ℂ) * exp (carlsonAffineForm z u)) (z i) := by
  exact HasDerivAt.comp_carlsonAffineForm_update i
    (Complex.hasDerivAt_exp (carlsonAffineForm z u))

/-- Coordinate differentiation of the native regularized `S` integral.  This is the
specialization of Carlson's differentiation formula to the exponential kernel. -/
theorem hasDerivAt_regCarlsonSIntegral_update
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι) :
    HasDerivAt (fun w ↦ regCarlsonSIntegral b (Function.update z i w))
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * exp (carlsonAffineForm z u))) (z i) := by
  simpa only [regCarlsonSIntegral, Complex.deriv_exp] using
    hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
      isOpen_univ convex_univ (fun _ _ => analyticAt_cexp) hb
      (Set.subset_univ (Set.range z)) i

/-- Carlson's coordinate differentiation formula for the regularized native `S` integral:
differentiation in `z i` raises the corresponding Dirichlet parameter. -/
theorem carlsonPartialDeriv_regCarlsonSIntegral
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι) :
    carlsonPartialDeriv i (regCarlsonSIntegral b) z =
      b i * regCarlsonSIntegral (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv, (hasDerivAt_regCarlsonSIntegral_update hb i).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ exp (carlsonAffineForm z u))).symm

/-- Every iterated complex derivative of the exponential function is the exponential function
itself. -/
theorem iteratedDeriv_cexp_eq (n : ℕ) :
    iteratedDeriv n exp = exp := by
  simpa using iteratedDeriv_cexp_const_mul n 1

/-- Carlson's Theorem 5.8-2 in regularized integral form: replacing the averaged exponential
by any of its iterated derivatives does not change the `S` integral.  Carlson denotes the
left-hand side by `S⁽ⁿ⁾` and writes `S⁽ⁿ⁾ = S`. -/
theorem regCarlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      regCarlsonSIntegral b z := by
  rw [iteratedDeriv_cexp_eq]
  rfl

/-- Carlson's native, unregularized `S` integral.  Its intended integral interpretation
requires `b ∈ Complex.mvBetaConvergent`. -/
def carlsonSIntegral (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonSIntegral b z

/-- The unregularized and regularized native `S` integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonSIntegral_eq_Gamma_mul_reg (b z : ι → ℂ) :
    carlsonSIntegral b z = Gamma (∑ i, b i) * regCarlsonSIntegral b z := rfl

/-- Carlson's Theorem 5.8-2 for the unregularized native integral. -/
theorem carlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    Gamma (∑ i, b i) *
        regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      carlsonSIntegral b z := by
  rw [regCarlsonDirichletAverage_iteratedDeriv_exp]
  rfl

end DirichletTransform
