/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.S.Basic
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.R.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.Confluence

/-! # The two-variable Carlson S-function -/

open Complex Filter
open scoped Classical Topology
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- On the native convergence region, the two-variable S-series agrees with its Dirichlet
integral. -/
theorem regSSeries_eq_regSIntegral (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    regSSeries b₀ b₁ z₀ z₁ = regSIntegral b₀ b₁ z₀ z₁ :=
  regCarlsonSSeries_eq_regCarlsonSIntegral (pair z₀ z₁) hb

/-- Simultaneously exchanging the two parameters and variables leaves the native
regularized S-integral unchanged. -/
theorem regSIntegral_swap (b₀ b₁ z₀ z₁ : ℂ) :
    regSIntegral b₁ b₀ z₁ z₀ = regSIntegral b₀ b₁ z₀ z₁ := by
  have h := regCarlsonSIntegral_perm (pair b₀ b₁) (pair z₀ z₁) (Equiv.swap 0 1)
  rw [show pair b₀ b₁ ∘ Equiv.swap 0 1 = pair b₁ b₀ by
      funext i; fin_cases i <;> rfl,
    show pair z₀ z₁ ∘ Equiv.swap 0 1 = pair z₁ z₀ by
      funext i; fin_cases i <;> rfl] at h
  exact h

/-- Translating both variables gives the global exponential translation formula for the
analytically continued two-variable S-series. -/
theorem regSSeries_add_const (b₀ b₁ z₀ z₁ a : ℂ) :
    regSSeries b₀ b₁ (z₀ + a) (z₁ + a) =
      exp a * regSSeries b₀ b₁ z₀ z₁ := by
  change regCarlsonSSeries (pair (z₀ + a) (z₁ + a)) (pair b₀ b₁) = _
  rw [show pair (z₀ + a) (z₁ + a) = fun i => pair z₀ z₁ i + a by
    funext i; fin_cases i <;> rfl]
  exact regCarlsonSSeries_add_const (pair z₀ z₁) (pair b₀ b₁) a

/-- The natural-power two-variable R-integrals coalesce to the two-variable S-integral. -/
theorem tendsto_regRIntegral_confluent (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ regRIntegral n b₀ b₁ (1 + z₀ / n) (1 + z₁ / n)) atTop
      (𝓝 (regSIntegral b₀ b₁ z₀ z₁)) := by
  convert tendsto_regCarlsonRIntegral_confluent (pair b₀ b₁) (pair z₀ z₁) hb using 1
  funext n
  congr 2

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
