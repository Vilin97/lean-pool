/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Lean

open Lean Meta Elab Tactic Term

namespace LeanPool.Polylean

/-- A tactic to reduce the main goal, up to definitional equality. -/
private def reduceGoal (transparency : TransparencyMode) : TacticM Unit := do
  let goal ← getMainGoal
  let reducedGoalType ← withTransparency transparency <|
    reduce (skipTypes := false) (skipProofs := false) (← getMainTarget)
  let newGoal ← mkFreshExprMVar reducedGoalType
  goal.assign newGoal
  replaceMainGoal [newGoal.mvarId!]

/--
`reduce_goal transparency` replaces the main goal by its reduced form using the
chosen transparency mode.
-/
elab "reduce_goal" tpc:ident : tactic => do
  let transparency : TransparencyMode :=
    match tpc.getId with
      |    `all    => .all
      |  `default  => .default
      | `reducible => .reducible
      | `instances => .instances
      |     _      => panic! "Unknown transparency mode"
  reduceGoal transparency

end LeanPool.Polylean
