/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Tactics.Intro

namespace TLA.ProofMode

open Lean Meta Elab Tactic

-- NOTE: The following approach to restoring binder names is inspired by
-- `binderNameHint` and `resolveBinderNameHint`
private def binderNameHintAsString (_n : String) (p : α → β) : α → β := p

private def resolveBinderNameHintAsString (e : Expr) : CoreM Expr := do
  Core.transform e (post := fun e' => do
    if e'.isAppOfArity' ``binderNameHintAsString 4 then
      let args := e'.getAppArgs'
      let α := args[0]!
      let target := args[3]!
      let some name := parseStringLitOpt args[2]! | return .done e'
      -- Manual eta-expansion
      return .done <| Expr.lam (Name.mkSimple name) α (.app (target.liftLooseBVars 0 1) (.bvar 0)) .default
    else return .done e')

-- NOTE: This is essentially the other direction of the equality,
-- but here we need to deal with the binder name, so make it a separate theorem.
theorem Entails_revert_forall {σ : Type u} {hyps : List (NamedPred σ)}
  {α : Sort v} {p : α → pred σ} (n : String) :
  Entails hyps (TLA.tlaForall (binderNameHintAsString n p)) → (∀ x, Entails hyps (p x)) := forall_elim.mpr

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

theorem Entails_revert_by_idx (idx : Nat) :
  -- NOTE: `get?Internal` should be only for internal use, but it's easier
  -- to reduce, so use it instead of `getElem?`
  letI rev := hyps.get?Internal idx
  letI hyps' := hyps.eraseIdx idx
  letI goal' := rev.elim goal fun r => [tlafml| (r.pred) → goal]
  Entails hyps' goal' → Entails hyps goal := by
  rw [List.get?Internal_eq_getElem?]
  rcases h : hyps[idx]? with _ | r <;> dsimp
  · simp at h; simp [List.eraseIdx_of_length_le h]
  · replace h := List.mem_of_getElem? h
    rw [← Entails_intro_temporal r.name]
    refine pred_implies_trans ?_
    apply repeatedAnd_subset_implies
    grind [List.mem_of_mem_eraseIdx]

theorem Entails_revert_by_name (toRevert : String) :
  -- NOTE: Still, linear complexity, but should be fine?
  letI idx := hyps.findIdx fun h => h.name == toRevert
  (type_of% (@Entails_revert_by_idx _ hyps goal idx)) := Entails_revert_by_idx _

theorem Entails_revert_all :
  Entails [] (repeatedImplies (hyps.map NamedPred.pred) goal) →
  Entails hyps goal := by
  intro h; replace h := (valid_eq_true_implies _).mpr h
  intro e h1; apply repeatedImplies_apply; apply And.intro; apply h1; apply h

end

private def revertTacDSimps := #[``List.findIdx, ``List.findIdx.go,
  ``List.get?Internal, ``List.eraseIdx, ``String.reduceBEq,
  ``String.reduceBNe, ``cond_false, ``cond_true, ``Option.elim]

private def revertAllTacDSimps := #[``repeatedImplies, ``List.map, ``List.foldr]

private def restoreBinderNameInForallCase : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ty ← getMainTarget
    let ty ← resolveBinderNameHintAsString ty
    -- The eta-expansion might introduce redexes, so do beta-reduction once
    let ty ← Core.betaReduce ty
    let g' ← g.replaceTargetDefEq ty
    replaceMainGoal [g']

/--
`tla_revert h₁ h₂ ...` moves assumptions back into the proof-mode goal.

If `hp : p` is a temporal hypothesis and the current goal is `q`, then
```lean
tla_revert hp
```
removes `hp` from the proof-mode context and changes the goal to `p → q`.

Lean locals can also be reverted: a proof `hP : P` becomes a pure implication
`⌞P⌟ → q`, while a non-Prop local such as `n : Nat` becomes a universal
quantifier in the goal.
-/
syntax (name := tlaRevertTac) "tla_revert" (ppSpace colGt ident)+ : tactic

/--
`tla_revert_all` moves every temporal hypothesis back into the proof-mode goal.

For example, if the proof-mode context contains `hp : p`, `hq : q`, and the
goal is `r`, then
```lean
tla_revert_all
```
leaves an empty temporal context and changes the goal to `p → q → r`.
Lean-local variables and pure assumptions are not reverted; use `tla_revert`
with explicit names for those.
-/
syntax (name := tlaRevertAllTac) "tla_revert_all" : tactic

-- FIXME: Better error message? Since the current semantics is if the target is missing,
-- then do nothing
elab_rules : tactic
  | `(tactic| tla_revert_all) => do
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_revert_all) ?_)
    postDSimpAfterApplyingReflectionTheorem revertAllTacDSimps
  | `(tactic| tla_revert $[$names:ident]*) => do
    -- Revert in reverse order so that the resulting nested implication mirrors
    -- the order of the names in the user's invocation (left-to-right becomes
    -- outermost-to-innermost in the goal).
    for name in names.reverse do
      withMainContext do
        match (← getLCtx).findFromUserName? name.getId with
        | some decl =>
          if ← Meta.isProp decl.type then
            evalTactic <| ← `(tactic|
              revert $name:ident; refine $(mkIdent ``Entails_pure_fact_intro).$(mkIdent `mpr) ?_)
          else
            let nameStr := toString name.getId
            evalTactic <| ← `(tactic|
              revert $name:ident; refine $(mkIdent ``Entails_revert_forall) $(quote nameStr) ?_)
            restoreBinderNameInForallCase
        | none =>
          let nameStr := toString name.getId
          evalTactic <| ← `(tactic|
            refine $(mkIdent ``Entails_revert_by_name) ($(quote nameStr)) ?_)
          postDSimpAfterApplyingReflectionTheorem revertTacDSimps

end TLA.ProofMode
