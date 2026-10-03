/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PsiM

/-! Statement file: `fluxIntegrand` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The integrand `(κ I + ψ_m(t,x) σ)(I + ∇Χ^κ_m(t,x))` of `e.am.kappa.def` (label 2971). -/
def fluxIntegrand (κ : ℝ) (m : ℕ) (t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.psiM m t x • sigmaMat) *
    (1 + gradMatrix (I.chiM κ m t) x)

end Ingredients
end AVenhance
