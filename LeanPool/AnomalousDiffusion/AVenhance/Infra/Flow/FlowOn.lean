/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow

/-! A global-flow interface for normed state spaces beyond the case `Vec 2`. -/

@[expose] public section

namespace AVenhance.Infra.Flow

/-- A characterized global ODE flow on an arbitrary normed state space. -/
def IsFlowOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → E) (Y : ℝ → E → ℝ → E) : Prop :=
  (∀ y s, Y s y s = y) ∧
  (∀ y s t, HasDerivAt (fun r => Y r y s) (F t (Y t y s)) t)

end AVenhance.Infra.Flow
