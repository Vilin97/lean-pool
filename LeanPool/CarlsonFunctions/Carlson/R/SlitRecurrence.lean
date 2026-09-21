/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.ContinuedRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.SlitContinuation
public import Mathlib.Analysis.Analytic.Polynomial

/-! # Polynomial recurrences on the full slit domain -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A finite polynomial-coefficient relation extends with its original coefficients. -/
theorem polynomial_relation_regCarlsonRSlit_of_right {κ : Type*} (s : Finset κ)
    (A : κ → MvPolynomial ι ℂ) (t : κ → ℂ) (b : κ → ι → ℂ)
    (h : ∀ (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain),
      ∑ j ∈ s, (A j).eval z * regCarlsonRContinued (t j) z hz (b j) = 0)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ j ∈ s, (A j).eval z * regCarlsonRSlit (t j) (b j) z = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z =>
      ∑ j ∈ s, (A j).eval z * regCarlsonRSlit (t j) (b j) z) carlsonRSlitDomain := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact ((AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (A j)) z trivial).mul
      (analyticOnNhd_regCarlsonRSlit (t j) (b j) z hz)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane ha analyticOnNhd_const ?_ hz
  intro w hw
  change ∑ j ∈ s, (A j).eval w * regCarlsonRSlit (t j) (b j) w = 0
  simp_rw [regCarlsonRSlit_eq_continued _ _ hw]
  exact h w hw

/-- Relation 8.4-1, with its polynomial coefficients, on the full slit domain. -/
theorem sum_carlsonAssociatedRecurrencePolynomial_mul_rSlit [Nonempty ι]
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
        regCarlsonRSlit (-a - n) b z = 0 :=
  polynomial_relation_regCarlsonRSlit_of_right _ _ _ _
    (fun _ hw => sum_carlsonAssociatedRecurrencePolynomial_mul_rContinued a b hw) hz

end DirichletTransform
