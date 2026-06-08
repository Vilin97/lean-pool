/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_drop_hyps {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (subHyps : List (NamedPred σ)) (hinc : subHyps.map NamedPred.pred ⊆ hyps.map NamedPred.pred) :
  Entails subHyps goal → Entails hyps goal := by
  intro h
  refine pred_implies_trans ?_ (by apply h); clear h
  apply repeatedAnd_subset_implies; exact hinc

theorem Entails_clear {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toClear : List String) :
  letI hyps' := hyps.filter fun h => !toClear.contains h.name
  Entails hyps' goal → Entails hyps goal := Entails_drop_hyps _ (by grind)

theorem Entails_clear_except {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toKeep : List String) :
  letI hyps' := hyps.filter fun h => toKeep.contains h.name
  Entails hyps' goal → Entails hyps goal := Entails_drop_hyps _ (by grind)

/--
`tla_clear * - h₁ h₂ ...` removes every temporal hypothesis except the named
ones. The kept hypotheses stay in their original order. For example, from
`hp : p`, `hq : q`, `hr : r`,
```lean
tla_clear * - hq
```
leaves only `hq : q`.
-/
syntax (name := tlaClearExceptTac) "tla_clear" "*" " -" (ppSpace colGt ident)* : tactic
/--
`tla_clear h₁ h₂ ...` removes temporal hypotheses from the proof-mode context.
The target predicate is unchanged, but the remaining proof must not use the
cleared hypotheses.

For example, from a context containing `hp : p`, `hq : q`, and goal `q`,
```lean
tla_clear hp
```
leaves only `hq : q` in the proof-mode context.
-/
syntax (name := tlaClearTac) "tla_clear" (ppSpace colGt ident)+ : tactic

private def clearTacDSimps := #[``List.filter, ``List.contains, ``List.elem, ``or, ``and, ``not,
  ``String.reduceBEq, ``String.reduceBNe, ``Bool.false_or, ``Bool.or_false]

/-- Clear the proof-mode hypotheses with the given names. -/
def tlaClearByName (name : List String) : TacticM Unit := do
  evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_clear) ($(quote name)) ?_)
  postDSimpAfterApplyingReflectionTheorem clearTacDSimps

elab_rules : tactic
  | `(tactic| tla_clear * - $[$names:ident]*) => withMainContext do
    let toKeep := names.toList.map fun name => toString name.getId
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_clear_except) ($(quote toKeep)) ?_)
    postDSimpAfterApplyingReflectionTheorem clearTacDSimps
  | `(tactic| tla_clear $[$names:ident]*) => withMainContext do
    let toClear := names.toList.map fun name => toString name.getId
    tlaClearByName toClear

end TLA.ProofMode
