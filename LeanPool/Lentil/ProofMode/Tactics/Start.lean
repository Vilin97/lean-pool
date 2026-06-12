/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic
import LeanPool.Lentil.Expr

namespace TLA.ProofMode

open Lean Meta Elab Tactic

private def sequentOpt (e : Expr) : Option (Expr × Expr × Expr) :=
  match_expr e with
  | TLA.predImplies σ lhs rhs => some (σ, lhs, rhs)
  | _ => none

private def getPremiseList (lhs : Expr) : MetaM (List Expr) := do
  if lhs.isAppOfArity' ``TLA.tlaTrue 1 then pure [] else TLA.Expr.splitAndIntoParts lhs

private def mkNamedPredListExpr (σ : Expr) (hyps : List (String × Expr)) : MetaM Expr := do
  let elemTy ← mkAppM ``TLA.ProofMode.NamedPred #[σ]
  toHypsList elemTy hyps

/--
`tla_start h₁ h₂ ...` enters proof mode for a raw TLA sequent. It splits the
left-hand side conjunction into named temporal hypotheses and keeps the right
hand side as the proof-mode goal.

For example, from a raw goal `(p ∧ q) |-tla- r`,
```lean
tla_start hp hq
```
changes the proof state to a proof-mode context with `hp : p`, `hq : q`, and
goal `r`.
-/
syntax (name := tlaStartTac) "tla_start" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| tla_start $[$names:ident]*) => withMainContext do
    -- Get input labels
    let lbls := names.toList.map fun name => toString name.getId
    if LentilLib.List.containsDuplicateElemHashable lbls then
      throwError "tla_start hypothesis names must be distinct"
    -- Build the new goal view
    let mainGoal ← getMainGoal
    let ty ← mainGoal.getType
    let ty ← cleanupAnnotAndMore ty
    let some (σ, lhs, rhs) := sequentOpt ty |
      throwError "tla_start only supports goals reduced to a single |-tla- sequent, but got {ty}"
    let hyps ← getPremiseList lhs
    unless hyps.length == lbls.length do
      throwError "tla_start expected {hyps.length} names, but got {lbls.length}"
    let namedHyps ← mkNamedPredListExpr σ <| lbls.zip hyps
    let pmTarget ← mkAppM ``TLA.ProofMode.Entails #[namedHyps, rhs]
    -- Build the proof for the new goal
    -- ... well, the proof is refl!
    let g' ← mainGoal.change pmTarget
    replaceMainGoal [g']

end TLA.ProofMode
