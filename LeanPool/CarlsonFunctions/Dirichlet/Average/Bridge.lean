/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Bridge
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Real
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic

/-!
# Bridge between real and complex Carlson averages

This file identifies the probability average at positive real parameters with the regularized
complex Carlson integral.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonDirichletBridge

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- On positive real parameters, the regularized complex Carlson integral is the Dirichlet
probability average divided by the Gamma factor of the total parameter. -/
theorem regCarlsonDirichletAverage_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : ι → ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage (fun i ↦ (b i : ℂ)) z f =
      realCarlsonDirichletAverage b z f / Gamma (∑ i, (b i : ℂ)) := by
  exact regDirichletIntegral_ofReal hb (fun u ↦ f (carlsonAffineForm z u))

end DirichletTransform

end CarlsonDirichletBridge
