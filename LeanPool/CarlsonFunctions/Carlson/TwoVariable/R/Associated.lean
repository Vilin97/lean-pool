/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.SlitRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.SlitDeriv

/-! # Two-variable associated R-relations -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The first two-node contiguous R-relation, without parameter denominators. -/
theorem regCarlsonRSlit_pair_contiguous (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    u * (y - x) * regCarlsonRSlit t (pair (u + 1) v) (pair x y) =
      y * regCarlsonRSlit t (pair u v) (pair x y) -
        regCarlsonRSlit (t + 1) (pair u v) (pair x y) := by
  have h₀ := regCarlsonRSlit_eq_sum_addDirichletUnit t (pair u v) hz
  have h₁ := regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit t (pair u v) hz
  have hu : addDirichletUnit (pair u v) 0 = pair (u + 1) v := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [Fin.sum_univ_two, pair_zero, pair_one, hu] at h₀ h₁
  linear_combination h₁ - y * h₀

/-- The companion contiguous relation, raising the second parameter. -/
theorem regCarlsonRSlit_pair_contiguous_last (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    v * (x - y) * regCarlsonRSlit t (pair u (v + 1)) (pair x y) =
      x * regCarlsonRSlit t (pair u v) (pair x y) -
        regCarlsonRSlit (t + 1) (pair u v) (pair x y) := by
  have h₀ := regCarlsonRSlit_eq_sum_addDirichletUnit t (pair u v) hz
  have h₁ := regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit t (pair u v) hz
  have hv : addDirichletUnit (pair u v) 1 = pair u (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [Fin.sum_univ_two, pair_zero, pair_one, hv] at h₀ h₁
  linear_combination h₁ - x * h₀

/-- The R-correction in (3.10) has a squared node-difference factor. -/
theorem regCarlsonRSlit_pair_correction_factor (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    -regCarlsonRSlit (t + 1) (pair u v) (pair x y) +
        (x + y) * regCarlsonRSlit t (pair u v) (pair x y) -
        x * y * regCarlsonRSlit (t - 1) (pair u v) (pair x y) =
      u * v * (x - y) ^ 2 * regCarlsonRSlit (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  have h₀ := regCarlsonRSlit_pair_contiguous_last t u v hz
  have h₁ := regCarlsonRSlit_pair_contiguous_last (t - 1) u v hz
  have h₂ := regCarlsonRSlit_pair_contiguous (t - 1) u (v + 1) hz
  simp only [sub_add_cancel] at h₁ h₂
  linear_combination -h₀ + y * h₁ + v * (x - y) * h₂

/-- The two-node mixed derivative, valid even at the exceptional integral exponents. -/
theorem carlsonPartialDeriv_regCarlsonRSlit_pair_mixed (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    carlsonPartialDeriv 0 (carlsonPartialDeriv 1 (regCarlsonRSlit (t + 1) (pair u v)))
        (pair x y) =
      t * (t + 1) * u * v * regCarlsonRSlit (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  have hshift : addDirichletUnit (addDirichletUnit (pair u v) 1) 0 =
      pair (u + 1) (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  rw [carlsonPartialDeriv_carlsonPartialDeriv_regCarlsonRSlit (t + 1) (pair u v) hz,
    hshift, show t + 1 - 2 = t - 1 by ring]
  simp [addDirichletUnit, pair]
  ring

/-- The three-term R-recurrence, with division-free coefficients. -/
theorem regCarlsonRSlit_pair_three_term (t u v : ℂ) {x y : ℂ}
    (hz : pair x y ∈ carlsonRSlitDomain) :
    (u + v + t) * regCarlsonRSlit (t + 1) (pair u v) (pair x y) -
      ((u + t) * x + (v + t) * y) * regCarlsonRSlit t (pair u v) (pair x y) +
      t * x * y * regCarlsonRSlit (t - 1) (pair u v) (pair x y) = 0 := by
  have he₂ : (MvPolynomial.esymm (Fin 2) ℂ 2).eval (pair x y) = x * y := by
    simpa [carlsonElementarySymmetric, Fin.prod_univ_two] using carlsonElementarySymmetric_card (pair x y)
  have h := sum_carlsonAssociatedRecurrencePolynomial_mul_rSlit (-t - 1) (pair u v) hz
  norm_num [Finset.sum_range_succ, carlsonAssociatedRecurrencePolynomial,
    MvPolynomial.esymm_one, Fin.sum_univ_two, he₂, pair_zero, pair_one] at h
  ring_nf at h ⊢
  linear_combination h

end DirichletTransform.TwoVariable
