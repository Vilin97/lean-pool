/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass

/-! Statement file: `IsContinuousIntoHolder` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `t ↦ b(t,·)` is continuous on `[0,1]` for the spatial `α`-Hölder seminorm: for every
`s ∈ [0,1]` and `ε > 0` there is `δ > 0` such that `[b(t,·) - b(s,·)]_{C^{0,α}} ≤ ε` whenever
`t ∈ [0,1]` and `|t - s| < δ`. Together with `IsHolderClass α b` (which gives continuity in
time for the supremum norm) this is the class `C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x` of the paper. -/
def IsContinuousIntoHolder (α : ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |t - s| < δ → ∀ x y : Vec 2,
      ‖(b t x - b s x) - (b t y - b s y)‖ ≤ ε * ‖x - y‖ ^ α

end AVenhance
