/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Flow.ExistsUniqueFlow

/-! Statement file: `existsUnique_flow` (Flow).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Global well-posedness of the flow for continuous, uniformly globally
Lipschitz fields. -/
theorem existsUnique_flow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ∃! X, IsFlow b X := by
  exact AVenhance.Proofs.existsUnique_flow b hb hL

end AVenhance
