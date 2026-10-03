/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.TauP

/-! Statement file: `tau` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.taum.def` (1108-1116): `τ_0 := 1`, and for `m ≥ 1`,
`τ_m := (4⌈ε_{m-1}^{-δ}⌉ + 1)⁻² τ''_m`. -/
def tau (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1
  else (4 * ((⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℕ) : ℝ) + 1)⁻¹ ^ 2 * tauPP β Λ m

end AVenhance
