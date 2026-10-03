/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow

/-! Statement file: `flowInv_leftInverse` (FlowDefs).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Characterization: `flowInv t · s` is a left inverse of `flow t · s`. -/
theorem flowInv_leftInverse (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) (t s : ℝ) :
    Function.LeftInverse (fun y => flowInv b hb hL t y s) (fun x => flow b hb hL t x s) := by
  intro x
  simp only [flowInv]
  rw [Infra.Flow.flow_group_law b hL (flow_isFlow b hb hL) x s t s]
  exact (flow_isFlow b hb hL).1 x s

end AVenhance
