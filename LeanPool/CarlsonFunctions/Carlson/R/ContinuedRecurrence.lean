/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.AssociatedRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.Continuation

/-!
# Carlson's homogeneity recurrence on the entire parameter space

Relation 8.4-1 is a polynomial identity after Gamma regularization. Its
coefficients therefore introduce no exceptional parameter values. This file
extends the native integral proof by permanence of functional relations.
-/

open Complex Set
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Carlson 8.4-1 for the continued regularized R-function, with arbitrary
complex exponent and Dirichlet parameters, including zeros of the recurrence
coefficients. Nodes remain in the existing right-half-plane domain. -/
theorem sum_carlsonAssociatedRecurrencePolynomial_mul_rContinued
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
        regCarlsonRContinued (-a - n) z hz b = 0 := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ?_ analyticOnNhd_const ?_) b
  · intro c _
    apply Finset.analyticAt_fun_sum
    intro n _
    apply AnalyticAt.mul
    · exact analyticAt_carlsonAssociatedRecurrencePolynomial_eval
        (a := fun _ : ι → ℂ => a) (a' := fun c : ι → ℂ => (∑ i, c i) - a)
        (b := fun c : ι → ℂ => c) (x := c) analyticAt_const
        ((Finset.analyticAt_fun_sum _ (fun i _ =>
          (ContinuousLinearMap.proj (R := ℂ) i).analyticAt c)).sub analyticAt_const)
        (fun i => (ContinuousLinearMap.proj (R := ℂ) i).analyticAt c) n z
    · exact analyticOnNhd_regCarlsonRContinued (-a - n) hz c (mem_univ _)
  · intro c hc
    dsimp only
    simp_rw [regCarlsonRContinued_eq_integral (-a - _) hz hc]
    exact carlsonAssociatedRecurrenceResidual_eq_zero a hc hz

end DirichletTransform
end
