/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Tau

/-! Statement file: `lIdx` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.lk.def` (1173-1177): `l_k := ⌈(k τ_m + (τ''_m - τ_m)/2) / τ''_m⌉`, `k ∈ ℤ`. -/
/- Correction: the source (1173) has a ceiling; the floor is required for
`e.taum.prime.supp` and `e.cutoff.overlaps` (the ceiling gives l₀ = 1). -/
def lIdx (β : ℝ) (Λ : ℕ) (m : ℕ) (k : ℤ) : ℤ :=
  ⌊((k : ℝ) * tau β Λ m + (1 / 2) * (tauPP β Λ m - tau β Λ m)) / tauPP β Λ m⌋

end AVenhance
