/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval

/-! Statement file: `permissibleSet` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `e.permissible.K` (label 3550): `𝒦 = ⋃_{m ∈ ℕ} [½ ε_m^{2β/(q+1)}, 2 ε_m^{2β/(q+1)}]`. -/
def permissibleSet (β : ℝ) (Λ : ℕ) : Set ℝ :=
  ⋃ (M : ℕ) (_ : 1 ≤ M), permittedInterval β Λ M

/-! ### 5. The PDE definition of the correctors and its well-posedness (flagged: source says
"the solution", `e.parabcorr.k`, label 2791) -/

end AVenhance
