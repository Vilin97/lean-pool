/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_intro_forall {σ : Type u} {hyps : List (NamedPred σ)}
  {α : Sort v} {p : α → pred σ} :
  (∀ x, Entails hyps (p x)) → Entails hyps (TLA.tlaForall p) := forall_elim.mp

theorem Entails_pure_fact_intro {σ : Type u} {hyps : List (NamedPred σ)}
  {q : Prop} {p : pred σ} :
  (q → Entails hyps p) = Entails hyps [tlafml| ⌞ q ⌟ → p ] := pure_fact_intro

theorem Entails_intro_temporal {σ : Type u} {hyps : List (NamedPred σ)}
  {goal newHyp : pred σ} (newHypName : String) :
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal =
  Entails hyps [tlafml| newHyp → goal ] := by
  unfold Entails; simp [impl_intro_add_r, repeatedAnd_append]; rfl

private def introTacDSimps := #[``List.cons_append, ``List.nil_append]

/-- Introduce one proof-mode hypothesis with the given name. -/
def tlaIntroCoreStep (k : SyntaxNodeKind) (name : TSyntax k)
  (ident? : TSyntax k → TacticM (Option Ident))
  (errorMsgPrefix : String) (tacIntroNonTemporalHyp : TSyntax k → TacticM (TSyntax `tactic))
  -- (tacIntroTemporalHyp : TSyntax k → TacticM Unit)
  : TacticM Bool := withMainContext do
  let ty ← getMainTarget
  let ty := ty.headBeta.cleanupAnnotations
  let_expr TLA.ProofMode.Entails _ _ goalPred := ty
    | throwError m!"{errorMsgPrefix}: goal is not an Entails sequent, but {ty}"
  match_expr goalPred with
  | TLA.tlaForall _ _ _ =>
    let tac ← tacIntroNonTemporalHyp name
    evalTactic <| ← `(tactic|
      refine $(mkIdent ``Entails_intro_forall) ?_; $tac)
    return false
  | TLA.tlaImplies _ lhs _ =>
    if lhs.isAppOf' ``TLA.purePred then
      let tac ← tacIntroNonTemporalHyp name
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_pure_fact_intro).$(mkIdent `mp) ?_; $tac)
      return false
    else
      let nameStr := match ← ident? name with
        | some nm => toString nm.getId
        | none => "h"
      evalTactic <| ← `(tactic|
        refine ($(mkIdent ``Entails_intro_temporal) ($(quote nameStr))).$(mkIdent `mp) ?_)
      postDSimpAfterApplyingReflectionTheorem introTacDSimps
      return true
  | _ =>
    throwError m!"{errorMsgPrefix}: goal predicate is not a ∀ or a ⌞..⌟ →; got {goalPred}"

/--
`tla_intro x₁ x₂ ...` introduces binders from the proof-mode goal.

If the goal starts with a temporal implication `p → q`, then `tla_intro hp`
adds `hp : p` to the proof-mode context and changes the goal to `q`.
If the goal starts with a universal quantifier, the introduced name becomes a
Lean local. If the goal starts with a pure implication `⌞P⌟ → q`, the introduced
name is a Lean proof of `P`.

Examples:
```lean
tla_intro hp    -- p → q  becomes  hp : p ⊢ q
tla_intro n hp -- ∀ n, p n → q n  introduces `n`, then `hp`
```
-/
syntax (name := tlaIntroTac) "tla_intro" (ppSpace colGt ident)+ : tactic

elab_rules : tactic
  | `(tactic| tla_intro%$tk $[$names:ident]*) => do
    let tacNonTemporal (name : Ident) : TacticM (TSyntax `tactic) := `(tactic| intro $name:ident)
    -- Following the built-in `intro` tactic: wrap each iteration in its own
    -- `withTacticInfoContext` so the proof state in the infoview steps through
    -- the identifiers one-by-one as the cursor advances past each name.
    for name in names, i in 0...* do
      let ctxRef := if i == 0 then Lean.mkNullNode #[tk, name] else name
      withTacticInfoContext ctxRef <| withRef name <|
        discard <| tlaIntroCoreStep `ident name (fun x => pure (some x)) "tla_intro" tacNonTemporal

end TLA.ProofMode
