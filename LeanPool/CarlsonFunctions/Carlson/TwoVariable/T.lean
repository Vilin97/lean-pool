/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.T

/-!
# The two-variable Carlson T-function

This file specializes the multivariate T-function of Carlson's Definition 5.12-1 to two
variables.  Later files may develop Carlson's singular limit in which one variable tends to
zero; special-function identifications do not belong here.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonTwoVariable

namespace DirichletTransform.TwoVariable

/-- The canonical two-variable specialization of the native regularized T-integral. -/
abbrev regTIntegral (b₀ b₁ x y : ℂ) : ℂ :=
  regCarlsonTIntegral (pair b₀ b₁) (pair x y)

/-- The canonical two-variable specialization of Carlson's native T-integral. -/
abbrev tIntegral (b₀ b₁ x y : ℂ) : ℂ :=
  carlsonTIntegral (pair b₀ b₁) (pair x y)

/-- The intrinsic domain for the two-variable T-integral. -/
def TVariableDomain (x y : ℂ) : Prop :=
  pair x y ∈ carlsonTVariableDomain

/-- On the two-variable T-domain, every affine combination occurring in the Euler-simplex
integral is nonzero. -/
theorem affine_pair_ne_zero_of_mem_TVariableDomain
    {x y : ℂ} (hxy : TVariableDomain x y)
    {u : Fin 2 → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    carlsonAffineForm (pair x y) u ≠ 0 :=
  carlsonAffineForm_ne_zero_of_mem_carlsonTVariableDomain hxy hu

/-- The two-variable T-integrand is integrable on its native parameter and variable domain. -/
theorem integrableOn_regDirichletDensity_mul_TKernel
    {b₀ b₁ x y : ℂ} (hb : pair b₀ b₁ ∈ mvBetaConvergent)
    (hxy : TVariableDomain x y) :
    IntegrableOn (fun u : Fin 2 → ℝ =>
      regDirichletDensity (pair b₀ b₁) u *
        carlsonTKernel (carlsonAffineForm (pair x y) u))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) MeasureTheory.Measure.stdSimplexMeasure :=
  integrableOn_regDirichletDensity_mul_carlsonTKernel hb hxy

/-- Simultaneously exchanging the parameters and variables leaves the regularized
two-variable T-integral unchanged. -/
theorem regTIntegral_swap (b₀ b₁ x y : ℂ) :
    regTIntegral b₁ b₀ y x = regTIntegral b₀ b₁ x y := by
  have h := regCarlsonTIntegral_perm (pair b₀ b₁) (pair x y) (Equiv.swap 0 1)
  rw [show pair b₀ b₁ ∘ Equiv.swap 0 1 = pair b₁ b₀ by
      funext i; fin_cases i <;> rfl,
    show pair x y ∘ Equiv.swap 0 1 = pair y x by
      funext i; fin_cases i <;> rfl] at h
  exact h

/-- A two-variable T-continuation is the multivariate continuation specialized to a pair of
variables. -/
def IsRegTContinuation (x y : ℂ) (G : (Fin 2 → ℂ) → ℂ) : Prop :=
  IsRegCarlsonTContinuation (pair x y) G

/-- A two-variable regularized T-continuation is entire in its two Dirichlet parameters. -/
theorem IsRegTContinuation.analyticOnNhd {x y : ℂ} {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegTContinuation x y G) : AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- On the intrinsic variable domain, an entire regularized two-variable T-continuation
exists. -/
theorem exists_isRegTContinuation {x y : ℂ} (hxy : TVariableDomain x y) :
    ∃ G : (Fin 2 → ℂ) → ℂ, IsRegTContinuation x y G :=
  exists_isRegCarlsonTContinuation hxy

/-- The entire regularized two-variable T-continuation is unique. -/
theorem IsRegTContinuation.eq {x y : ℂ} {G H : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegTContinuation x y G) (hH : IsRegTContinuation x y H) : G = H :=
  DirichletTransform.IsRegCarlsonTContinuation.eq hG hH

end DirichletTransform.TwoVariable

end CarlsonTwoVariable
