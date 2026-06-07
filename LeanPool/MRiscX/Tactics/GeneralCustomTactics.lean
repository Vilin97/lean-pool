/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean
import Mathlib.Tactic.Push
import Mathlib.Data.Set.Basic

open Lean Elab Tactic Meta

/-
This file contains some custom tactics which are used several times wihthin all over
this project.
-/

elab "simp_set_eq" : tactic => do
  evalTactic (← `(tactic | (ext; simp; grind)))


elab "apply_to_last_goal" t:tacticSeq : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    match goals.getLast? with
    | some goal =>
      Lean.Elab.Tactic.setGoals ([goal] ++ goals.extract 0 (goals.length - 1))

    | none => throwError "No goals found while trying to apply {t} to the last goal"

  evalTactic (← `(tactic | . $t ))


/- A small tactic to prove `∀ (n' : ℕ), 0 < n' → ¬n' = 0`-/
macro "zero_lt_ne_zero" : tactic =>
  `(tactic | try (intros n' h ; intro h_eq ; rw [h_eq] at h); simp at h)
