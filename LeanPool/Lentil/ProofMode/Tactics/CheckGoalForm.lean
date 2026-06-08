/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

-- CHECK Does this also appear somewhere else?
private def parseCanonicalEntails (tm : Expr) (errorMsg : MessageData) :
    TacticM (Expr × List (String × Expr) × Expr) := do
  let tm ← cleanupAnnotAndMore tm
  let_expr Entails σ hyps goal := tm
    | throwError errorMsg
  let some (_, hyps) ← recognizeHypsList hyps
    | throwError errorMsg
  return (σ, hyps, goal)

private def checkNamedHyps (actualHyps expectedHyps : List (String × Expr)) : MetaM Unit :=
  go 0 actualHyps expectedHyps
where go : Nat → List (String × Expr) → List (String × Expr) → MetaM Unit
  | _, [], [] => pure ()
  | idx, (actualName, actualPred) :: actualHyps,
      (expectedName, expectedPred) :: expectedHyps => do
    unless actualName == expectedName do
      throwError "tla_check_goal: temporal hypothesis {idx} is named '{actualName}', expected '{expectedName}'"
    unless ← isDefEq actualPred expectedPred do
      throwError "tla_check_goal: temporal hypothesis '{actualName}' has predicate{indentExpr actualPred}\nbut expected{indentExpr expectedPred}"
    go (idx + 1) actualHyps expectedHyps
  | _, _, _ => throwError "tla_check_goal: internal hypothesis-count mismatch"

/--
`tlaCheckGoalForm` checks that the current proof-mode goal is in the
canonical literal `Entails [...] goal` form used by the proof-mode tactics.

It does not change the goal. This is useful in tests after a tactic that
reflects over the hypothesis list: if the goal still contains unreduced list
computations, then the check fails.
-/
elab "tlaCheckGoalForm" : tactic => do
  unless (← recognizeEntailsHypsFromGoal).isSome do
    throwError "tlaCheckGoalForm: goal is not in canonical Entails form"

/--
`tla_check_goal expected` checks that the current proof-mode goal has the
literal named hypothesis list and target predicate in `expected`.

Unlike `show Entails [...] goal`, this tactic does not forget proof-mode
hypothesis names. For example,
```lean
tla_check_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
```
checks that the context contains exactly `hp : p` followed by `hq : q`, and
that the goal is `r`. Predicates are compared by definitional equality.
-/
elab "tla_check_goal " expected:term : tactic => withMainContext do
  let (actualσ, actualHyps, actualGoal) ←
    parseCanonicalEntails (← getMainTarget)
      m!"tla_check_goal: goal is not in canonical Entails form"
  let expected ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize expected none
  let (expectedσ, expectedHyps, expectedGoal) ←
    parseCanonicalEntails expected
      m!"tla_check_goal: expected an Entails expression with a literal hypothesis list"
  unless ← isDefEq actualσ expectedσ do
    throwError "tla_check_goal: expected state type{indentExpr expectedσ}\nbut the goal has state type{indentExpr actualσ}"
  unless actualHyps.length == expectedHyps.length do
    throwError "tla_check_goal: expected {expectedHyps.length} temporal hypotheses, but the goal has {actualHyps.length}"
  checkNamedHyps actualHyps expectedHyps
  unless ← isDefEq actualGoal expectedGoal do
    throwError "tla_check_goal: goal predicate is{indentExpr actualGoal}\nbut expected{indentExpr expectedGoal}"

end TLA.ProofMode
