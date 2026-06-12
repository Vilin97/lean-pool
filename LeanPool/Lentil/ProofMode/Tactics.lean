/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Tactics.Apply
import LeanPool.Lentil.ProofMode.Tactics.Assumption
import LeanPool.Lentil.ProofMode.Tactics.CheckGoalForm
import LeanPool.Lentil.ProofMode.Tactics.Clear
import LeanPool.Lentil.ProofMode.Tactics.Contradiction
import LeanPool.Lentil.ProofMode.Tactics.CoalesceToPTL
import LeanPool.Lentil.ProofMode.Tactics.Exists
import LeanPool.Lentil.ProofMode.Tactics.Exit
import LeanPool.Lentil.ProofMode.Tactics.Have
import LeanPool.Lentil.ProofMode.Tactics.Intro
import LeanPool.Lentil.ProofMode.Tactics.LeftRight
import LeanPool.Lentil.ProofMode.Tactics.ModalityMisc
import LeanPool.Lentil.ProofMode.Tactics.Monotone
import LeanPool.Lentil.ProofMode.Tactics.Normalize
import LeanPool.Lentil.ProofMode.Tactics.PurePred
import LeanPool.Lentil.ProofMode.Tactics.RCases
import LeanPool.Lentil.ProofMode.Tactics.Rename
import LeanPool.Lentil.ProofMode.Tactics.Revert
import LeanPool.Lentil.ProofMode.Tactics.Rewrite
import LeanPool.Lentil.ProofMode.Tactics.Simp
import LeanPool.Lentil.ProofMode.Tactics.Specialize
import LeanPool.Lentil.ProofMode.Tactics.SplitAnds
import LeanPool.Lentil.ProofMode.Tactics.Start

/-
NOTE: On the soundness theorems corresponding to these tactics:
(not including `normalize` and `start`)
- `clear`: simple inclusion reasoning
- `assumption`: inclusion reasoning for a singleton sub-context
- `coalesce_to_ptl`: generalize first-order predicate blocks while preserving
  their propositional temporal skeleton
- `exists`, `intro`: basically reducing to existing rules
- `revert`: basically the inversion of `intro`
- `pull_pure`: `revert` + `intro`
- `rename`: a very special case of inclusion reasoning (eq)
- `rcases`: reducing to `revert`
- `rintro`: `intro` followed by `rcases`
- `specialize`: general logic of filling in the LHS of an implication
- `have`/`suffices`: reducing to `specialize`
- `apply`: reducing to `have` then `specialize`
- `monotone`: distributing a supported modality over the proof-mode context,
  then using the corresponding `_monotone` rule
- `toggle_goal_under_always`: toggling the goal with `always_pred_implies`
  after recognizing an all-`always` proof-mode context
- `rewrite`: hide unselected proof-mode locations behind a local continuation,
  run Lean's `rewrite`, then reconstruct the `Entails` sequent
- `simp`/`dsimp`: run Lean's simplifiers as direct `conv` visits to selected
  proof-mode locations

NOTE: Currently, after applying meta soundness theorems, we almost always need a
post simplification step for the goal, which might be fragile in certain cases.
Probably, a better way is to (partially) compute the resulting goal at the meta
level, and then convert the goal to it by defeq?
-/
