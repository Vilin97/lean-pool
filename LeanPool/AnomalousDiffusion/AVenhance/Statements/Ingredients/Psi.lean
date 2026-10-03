/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi0

/-! Statement file: `psi` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.def.streamr` (1207-1210): `ψ_{m,k} := a_m ε_m² ψ_{0,k}(· / ε_m)`, `m ≥ 1`. -/
def psi (β : ℝ) (Λ : ℕ) (m : ℕ) (k : ℤ) (x : Vec 2) : ℝ :=
  a β Λ m * epsilon β Λ m ^ 2 * psi0 k ((epsilon β Λ m)⁻¹ • x)

end AVenhance
