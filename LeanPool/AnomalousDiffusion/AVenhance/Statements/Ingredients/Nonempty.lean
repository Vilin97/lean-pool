/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Ingredients.Nonempty

/-! Statement file: `nonempty` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization
namespace Ingredients

/-- statement `Ingredients.nonempty`: for every `β ∈ (1, 4/3)` there is a constant
`C₀` (depending only on `β`) such that for every integer `Λ ≥ 2^7` there are ingredients with
this `Λ` and all three cutoff constants at most `C₀`. -/
theorem nonempty (β : ℝ) (h1 : 1 < β) (h2 : β < 4 / 3) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ Λ : ℕ, 2 ^ 7 ≤ Λ →
      ∃ I : Ingredients β, I.Λ = Λ ∧ I.Czeta ≤ C₀ ∧ I.Cxi ≤ C₀ ∧ I.Chat ≤ C₀ := by
  exact AVenhance.Proofs.Ingredients.nonempty β h1 h2

end Ingredients
end AVenhance
