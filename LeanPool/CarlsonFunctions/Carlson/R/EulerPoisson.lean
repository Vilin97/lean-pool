/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SlitDeriv

/-! # The R Euler–Poisson system on the full slit domain -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The Euler–Poisson system for R, for all complex parameters and slit-plane nodes.
Neither distinct indices nor separated nodes are required. -/
theorem carlsonEulerPoissonOperator_regCarlsonRSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (regCarlsonRSlit t b) = 0 := by
  by_cases hij : i = j
  · subst j; exact carlsonEulerPoissonOperator_self i b z _
  unfold carlsonEulerPoissonOperator
  rw [carlsonPartialDeriv_carlsonPartialDeriv_regCarlsonRSlit t b hz,
    carlsonPartialDeriv_regCarlsonRSlit t b hz j,
    carlsonPartialDeriv_regCarlsonRSlit t b hz i]
  rw [show addDirichletUnit b j i = b i by simp [addDirichletUnit, hij]]
  have h := regCarlsonRSlit_tangent (t - 1) b hz i j
  rw [show t - 1 - 1 = t - 2 by ring] at h
  linear_combination t * b i * b j * h

/-- The ordinary normalization obeys the same Euler–Poisson system. At Gamma
poles this is an identity of totalized expressions, not a finite ordinary value. -/
theorem carlsonEulerPoissonOperator_carlsonRSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (carlsonRSlit t b) = 0 := by
  change carlsonEulerPoissonOperator i j b z
    (fun w => Gamma (∑ k, b k) * regCarlsonRSlit t b w) = 0
  rw [carlsonEulerPoissonOperator_const_mul,
    carlsonEulerPoissonOperator_regCarlsonRSlit t b hz i j, mul_zero]

end DirichletTransform
