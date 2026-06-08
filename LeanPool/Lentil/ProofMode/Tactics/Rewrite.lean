/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Location

namespace TLA.ProofMode

open Lean Meta Elab Tactic LentilLib
open Lean.Parser.Tactic

/-
Design notes.

`tla_rewrite` operates on selected pieces of a proof-mode sequent

  `Entails [⟨h₀, p₀⟩, ..., ⟨hₙ, pₙ⟩] goal`.

The first implementation tried to change the goal to a wrapper whose selected
locations were explicit arguments and whose unselected locations were implicit
arguments. That does not isolate the unselected predicates: Lean's `rewrite`
still traverses implicit arguments, so a rewrite intended for `hp₁ hp₃` could
also rewrite `hp₂`.

The current implementation instead follows the shape of the manual script

  `let cont := fun preds => EntailsWithSomePredsExtractedOut hyps idxs preds goal`
  `change cont [selected predicates]`
  `rewrite ...`
  `revert cont`
  `change Entails [updated hypotheses] updatedGoal`

for one selected location at a time. An earlier version exposed all selected
hypotheses together as one list argument, but that did not match Lean's
`rewrite` location semantics: Lean rewrites each selected hypothesis separately,
so `rewrite [h] at *` can rewrite both `hp` and `hr` even if `hq` has no
matching occurrence. Rewriting the whole selected list only rewrites the first
matching occurrence in that list.

If the goal itself is selected, `cont` takes a second explicit argument for it.
The body of the local `let` is opaque to `rewrite`, while the explicit argument
for the current location remains a normal Lean expression. After rewriting,
reverting and unfolding `cont` restores a literal `Entails` target with the
original hypothesis order and names. The final target is computed here at the
meta level; we do not rely on `dsimp` to clean up `replacePredsAtIndices`.

`tla_simp` and `tla_dsimp` deliberately do not use this helper. They are
implemented as direct `conv` visits to the selected expressions because
simplification does not need `rewrite`'s theorem-premise side-goal behavior.
-/

/-- Replace the predicates at the given hypothesis indices. -/
def replacePredsAtIndices {σ : Type u} (hyps : List (NamedPred σ))
    (idxs : List Nat) (preds : List (pred σ)) : List (NamedPred σ) :=
  (idxs.zip preds).foldl (fun hyps ⟨idx, pred⟩ => hyps.modify idx fun h => { h with pred := pred }) hyps

/-- An `Entails` goal with some hypothesis predicates extracted out for rewriting. -/
def EntailsWithSomePredsExtractedOut {σ : Type u} (hyps : List (NamedPred σ))
    (idxs : List Nat) (preds : List (pred σ)) (goal : pred σ) : Prop :=
  Entails (replacePredsAtIndices hyps idxs preds) goal

/-- Compute the restored `Entails` target by inspecting the partially exposed
target itself. This is the meta-level counterpart of
`change Entails [updated hypotheses] updatedGoal`: it reads the rewritten
predicate list, patches the original hypothesis list, and builds a fresh literal
`Entails` expression. -/
private def unfoldPartialHiddenTarget (target : Expr) : MetaM (Option Expr) := target.withApp' fun f args => do
  -- Recognize
  unless f.isConstOf ``EntailsWithSomePredsExtractedOut do
    return none
  let [σ, hypsExpr, idxsExpr, predsExpr, goal] := args.toList | return none
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr | return none
  let some (_, idxExprs) := idxsExpr.listLit? | return none
  let idxs := idxExprs.filterMap Expr.nat?
  unless idxs.length == idxExprs.length do
    return none
  let some (_, preds) := predsExpr.listLit? | return none
  unless idxs.length == preds.length do
    throwError "tla_rewrite: internal error: length of indices and predicates do not match in partial hidden target"
  -- Build `Entails`
  let hyps := idxs.zip preds |>.foldl (init := hyps) fun hyps' (idx, pred) =>
    hyps'.modify idx fun (name, _) => (name, pred)
  let hypsExpr ← toHypsList hypTy hyps
  return some <| ← mkAppOptM ``Entails #[some σ, some hypsExpr, some goal]

private def restorePartiallyHiddenGoals (contFVar : FVarId) : TacticM Unit := do
  let gs ← getGoals
  let gs' ← gs.mapM fun g => g.withContext do
    unless (← getLCtx).contains contFVar do
      return g
    let target ← cleanupAnnotAndMore (← g.getType)
    -- NOTE: `zetaDeltaFVars` seems good to use, so instead of `revert`,
    -- first do `zetaDeltaFVars` and then `clear`
    let target ← zetaDeltaFVars target #[contFVar]
    let g' ← g.change target
    let g' ← g'.clear contFVar
    if let some newTarget ← unfoldPartialHiddenTarget target then
      let g'' ← g'.change newTarget
      pure g''
    else
      pure g'
  setGoals gs'

-- NOTE: This is an overkill for the current `tla_rewrite`, but might be useful
-- in the future for other things? So just keep it for now.
private def exposeSelectedLocations (hypsExpr goal : Expr)
    (hyps : List (String × Expr)) (loc : RewriteLocation) (mainGoal : MVarId) :
    TacticM (FVarId × MVarId) := do
  let predTy ← inferType goal
  let idxs := loc.idxs.toList
  let preds := idxs.filterMap fun idx => hyps[idx]?.map Prod.snd   -- Should not fail since `parseRewriteLocation` checks the indices
  let predsExpr ← mkListLit predTy preds
  let idxsExpr := toExpr idxs
  let predsTy ← mkAppM ``List #[predTy]
  let contVal ← withLocalDeclD `preds predsTy fun predsVar => do
    if loc.includeGoal then
      withLocalDeclD `goal predTy fun goalVar => do
        let body ← mkAppOptM ``EntailsWithSomePredsExtractedOut
          #[none, some hypsExpr, some idxsExpr, some predsVar, some goalVar]
        mkLambdaFVars #[predsVar, goalVar] body
    else
      let body ← mkAppOptM ``EntailsWithSomePredsExtractedOut
        #[none, some hypsExpr, some idxsExpr, some predsVar, some goal]
      mkLambdaFVars #[predsVar] body
  let contName ← mainGoal.withContext do mkFreshUserName `cont
  let (contFVar, g') ← «let» mainGoal contName contVal
  let g'' ← g'.withContext do
    let cont := mkFVar contFVar
    let newTarget := if loc.includeGoal then mkApp2 cont predsExpr goal else mkApp cont predsExpr
    g'.change newTarget
  return (contFVar, g'')

private inductive RewriteOneLocation where
  | hyp (idx : Nat)
  | goal

private def exposeOneLocation (hypsExpr goal : Expr)
    (hyps : List (String × Expr)) (loc : RewriteOneLocation) (mainGoal : MVarId) :
    TacticM (FVarId × MVarId) := do
  match loc with
  | .hyp idx => exposeSelectedLocations hypsExpr goal hyps ⟨#[idx], false, true⟩ mainGoal
  | .goal => exposeSelectedLocations hypsExpr goal hyps ⟨#[], true, true⟩ mainGoal

/-- Expose one proof-mode location, run `k`, then restore all generated goals
back from the local-`let` view to `Entails`. -/
private def withExposedLocation (loc : RewriteOneLocation) (k : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target
    | throwError "tla_rewrite: goal is not an Entails sequent, but {target}"
  -- CHECK `recognizeEntailsHyps` is repetitively called. Will this be slow?
  let some (_, hyps) ← recognizeEntailsHyps target
    | throwError "tla_rewrite: failed to read the hypotheses from the goal"
  let (contFVar, g') ← exposeOneLocation hypsExpr goal hyps loc g
  replaceMainGoal [g']
  g'.withContext k
  restorePartiallyHiddenGoals contFVar

private def rewriteAtProofModeLocations
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location)) (k : TacticM Unit) : TacticM Unit := do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal
    | throwError "tla_rewrite: goal is not an Entails sequent"
  let loc ← parseRewriteLocation hyps loc? "tla_rewrite"
  if loc.isWildCard then
    let mut worked := false
    let ok ← tryTactic <| withMainContext <| withExposedLocation .goal k
    worked := worked || ok
    -- NOTE: In Lean's `rewrite`, local declarations are processed in the _reverse_ order,
    -- but here we don't follow that, since there is no dependency between temporal hypotheses
    for idx in loc.idxs do
      let ok ← tryTactic <| withMainContext <| withExposedLocation (.hyp idx) k
      worked := worked || ok
    unless worked do
      throwTacticEx `rewrite (← getMainGoal) "Did not find an occurrence of the pattern in the current goal"
  else
    for idx in loc.idxs do
      withExposedLocation (.hyp idx) k
    if loc.includeGoal then
      withExposedLocation .goal k

/--
`tla_rewrite [rules]` rewrites predicates in a proof-mode goal or selected
proof-mode hypotheses.

With no location, it rewrites the goal predicate. For example, if the goal is
`q` and `heq : q = r`, then
```lean
tla_rewrite [heq]
```
changes the goal to `r`.

Locations use Lean's location syntax, but refer to proof-mode hypotheses:
```lean
tla_rewrite [heq] at hp
tla_rewrite [← heq] at hp hq ⊢
```
The first rewrites only `hp`; the second rewrites `hp`, `hq`, and the goal.
With `at *`, each proof-mode hypothesis and the goal are considered separately;
locations that do not contain a matching occurrence are skipped as in Lean's
`rewrite`.
-/
syntax (name := tlaRewrite) "tla_rewrite" optConfig rwRuleSeq (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| tla_rewrite $cfg:optConfig $rules:rwRuleSeq $[$loc]?) => do
    rewriteAtProofModeLocations loc do
      evalTactic <| ← `(tactic| rewrite $cfg:optConfig $rules:rwRuleSeq)

end TLA.ProofMode
