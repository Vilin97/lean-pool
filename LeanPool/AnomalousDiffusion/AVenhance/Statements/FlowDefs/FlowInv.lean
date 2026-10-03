/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.Flow

/-! Statement file: `flowInv` (FlowDefs).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- The inverse flow `X⁻¹(t,·,s)`, the inverse function of `X(t,·,s)` (source 1410–1415,
`e.flowabbrev`), realized by the group law as `X⁻¹(t,y,s) = X(s,y,t)`. -/
noncomputable def flowInv (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (t : ℝ) (y : Vec 2) (s : ℝ) : Vec 2 :=
  flow b hb hL s y t

end AVenhance
