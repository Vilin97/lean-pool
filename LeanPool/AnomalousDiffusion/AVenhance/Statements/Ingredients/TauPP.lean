/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.A

/-! Statement file: `tauPP` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.taum.primeprime.def` (1130-1136), for `m ≥ 1`:
`τ''_m := 2⁻²⁵ ⌈a_{m-1} / ε_{m-1}^{2δ}⌉⁻¹`. The value at `m = 0` is unused. -/
def tauPP (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-25 : ℤ) *
    ((⌈a β Λ (m - 1) / epsilon β Λ (m - 1) ^ (2 * delta β)⌉₊ : ℕ) : ℝ)⁻¹

end AVenhance
