/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Real
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Kernel

/-!
# Carlson's Dirichlet average with real positive parameters

This file provides the probability-theoretic form of Carlson's average. Its parameters are
strictly positive real numbers and integration is against `dirichletMeasure`.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory

@[expose] public noncomputable section RealCarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's probability average for positive real Dirichlet parameters. -/
def realCarlsonDirichletAverage (b : ι → ℝ) (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ u, f (carlsonAffineForm z u) ∂dirichletMeasure b

/-- The probability-theoretic Carlson average has the expected density representation. -/
theorem realCarlsonDirichletAverage_eq_integral [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) (f : ℂ → ℂ) :
    realCarlsonDirichletAverage b z f =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        (dirichletPdfReal b u : ℂ) * f (carlsonAffineForm z u)
          ∂stdSimplexMeasure :=
  integral_dirichletMeasure_complex hb _

end DirichletTransform

end RealCarlsonDirichletAverage
