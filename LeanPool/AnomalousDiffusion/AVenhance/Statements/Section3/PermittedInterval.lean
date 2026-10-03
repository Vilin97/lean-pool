/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt

/-! Statement file: `permittedInterval` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `e.permitted` (label 3564): the interval `[½ ε_M^{2β/(q+1)}, 2 ε_M^{2β/(q+1)}]`. -/
def permittedInterval (β : ℝ) (Λ : ℕ) (M : ℕ) : Set ℝ :=
  Set.Icc (1 / 2 * epsilon β Λ M ^ (2 * β / (q β + 1)))
    (2 * epsilon β Λ M ^ (2 * β / (q β + 1)))

end AVenhance
