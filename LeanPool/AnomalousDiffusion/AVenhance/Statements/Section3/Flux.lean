/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.FluxIntegrand

/-! Statement file: `flux` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `e.am.kappa.def` (label 2971): `J^κ_m(t) = ⟨(κ I + ψ_m(t,·) σ)(I + ∇Χ^κ_m(t,·))⟩`. -/
def flux (κ : ℝ) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  spaceAvgMat (I.fluxIntegrand κ m t)

end Ingredients
end AVenhance
