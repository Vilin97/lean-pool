/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.TauPP

/-! Statement file: `tauP` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.taum.prime.def` (1121-1127), for `m ≥ 1`:
`τ'_m := (4⌈ε_{m-1}^{-δ}⌉ + 1)⁻¹ τ''_m`. The value at `m = 0` is unused. -/
def tauP (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  (4 * ((⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℕ) : ℝ) + 1)⁻¹ * tauPP β Λ m

end AVenhance
