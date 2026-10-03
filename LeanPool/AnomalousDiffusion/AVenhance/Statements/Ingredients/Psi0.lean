/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx

/-! Statement file: `psi0` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.def.streamr.0` (1194-1201): `ψ_{0,k}(x) = sin(2π x_i)` if `k ∈ 4ℤ + 2i - 1`,
`i ∈ {1,2}` (coordinates `x 0`, `x 1`), and `0` for even `k`. -/
def psi0 (k : ℤ) (x : Vec 2) : ℝ :=
  if k % 4 = 1 then Real.sin (2 * Real.pi * x 0)
  else if k % 4 = 3 then Real.sin (2 * Real.pi * x 1)
  else 0

end AVenhance
