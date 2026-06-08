/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Tactics.Rename

namespace TLA.ProofMode

open Lean Meta Elab Tactic LentilLib

/-
Design note: `tla_specialize` should be the shared specialization engine for
proof-mode automation.

The tactic repeatedly looks at the current predicate of one temporal hypothesis
and consumes one user argument according to that predicate shape:

* `forall`: the argument is elaborated as the Lean witness.
* pure implication: the argument is elaborated as a Lean proof of the pure
  proposition.
* temporal implication: the argument names one or more existing proof-mode
  hypotheses, written either as a single identifier or as a flat tuple.

This file supports both name-based and index-based positions through
`TemporalHypLoc`. The index form is important for callers such as `tla_have := ...`,
which can append an anonymous/internal temporal hypothesis and immediately
specialize exactly that newly-added hypothesis without relying on a user-visible
name.
-/

/-- The general thing used in `apply`, `have` and `suffices`. -/
theorem Entails_add_new {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (subHyps : List (pred σ)) (hinc : subHyps ⊆ hyps.map NamedPred.pred)
  (newHypName : String) (newHyp : pred σ) :
  ((repeatedAnd subHyps)) |-tla- (newHyp) →
  Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal →
  Entails hyps goal := by
  intro h1 h2
  refine pred_implies_trans ?_ (by apply h2); clear h2
  simp [repeatedAnd_append, and_pred_implies_split]; constructor
  · rfl
  · refine pred_implies_trans ?_ (by apply h1); clear h1
    apply repeatedAnd_subset_implies; grind

local macro "replaceFun" : term => `((fun h => { h with pred := $(mkIdent `newHyp) }))

section

variable {σ : Type u} {hyps hyps' : List (NamedPred σ)} {goal : pred σ} {newHyp : pred σ}
  (idx : Nat) (h : ModifyHypSpecWithIndex hyps hyps' replaceFun idx)

include h in
private theorem Entails_specializeHyp_aux
  (subHyps : List (pred σ)) (hinc : subHyps ⊆ hyps.map NamedPred.pred) :
  ((repeatedAnd subHyps)) |-tla- (newHyp) → Entails hyps' goal → Entails hyps goal := by
  intro h1 h2
  rcases h with rfl | ⟨hidx, rfl⟩
  on_goal 1=> exact h2
  apply Entails_add_new (newHypName := (hyps[idx]'hidx).name)
  on_goal 2=> apply h1
  on_goal 1=> exact hinc
  unfold Entails
  have htmp2 := repeatedAnd_modifyHyp_reorder hyps _ hidx fun ⟨name, _⟩ => NamedPred.mk name newHyp
  dsimp only at htmp2
  simp only [List.map_append, repeatedAnd_append, List.map_singleton, repeatedAnd_singleton, htmp2]
  apply impl_drop_hyp_one_r; exact h2

variable (hidx : idx < hyps.length) (hhyps' : hyps' = hyps.modify idx replaceFun)
include hidx hhyps'

private theorem Entails_specialize_forall_aux {α : Sort v} {p : α → pred σ} (witness : α)
  (heq : newHyp = p witness) (hpred : (hyps[idx]'hidx).pred = tlaForall p) :
  Entails hyps' goal → Entails hyps goal := by
  apply Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps := [TLA.tlaForall p])
  · grind
  · simp [repeatedAnd_singleton]; tlaUnfoldSimp; subst newHyp; grind

private theorem Entails_specialize_pure_aux {rhs : pred σ} {q : Prop} (hq : q)
  (heq : newHyp = rhs) (hpred : (hyps[idx]'hidx).pred = [tlafml| ⌞ q ⌟ → rhs]) :
  Entails hyps' goal → Entails hyps goal := by
  apply Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps := [[tlafml| ⌞ q ⌟ → rhs]])
  · grind
  · simp [repeatedAnd_singleton]; tlaUnfoldSimp; grind

private theorem Entails_specialize_valid_aux {lhs rhs : pred σ} (hlhs : TLA.valid lhs)
  (heq : newHyp = rhs) (hpred : (hyps[idx]'hidx).pred = [tlafml| lhs → rhs]) :
  Entails hyps' goal → Entails hyps goal := by
  apply Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps := [[tlafml| lhs → rhs]])
  · grind
  · subst newHyp; simp [repeatedAnd_singleton]; revert hlhs; tlaUnfoldSimp; grind

private theorem Entails_specialize_temporal_aux {rhs : pred σ} (lhss : List (pred σ))
  (hin : lhss ⊆ hyps.map NamedPred.pred)
  (heq : newHyp = rhs) (hpred : (hyps[idx]'hidx).pred = [tlafml| (repeatedAnd lhss) → rhs]) :
  Entails hyps' goal → Entails hyps goal := by
  apply Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps := [tlafml| (repeatedAnd lhss) → rhs] :: lhss)
  · grind
  · rw [repeatedAnd_cons]; tlaUnfoldSimp; grind

end

/-- Replace the chosen hypothesis predicate with a new one. -/
def replaceChosenPred {σ : Type u} (hyps : List (NamedPred σ)) (chosen : String) (newHyp : pred σ) :=
  modifyHypByName hyps chosen replaceFun

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

section

variable {α : Sort v} {p : α → pred σ} (witness : α)

theorem Entails_specialize_forall_by_name (chosen : String)
  (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, TLA.tlaForall p⟩) :
  Entails (replaceChosenPred hyps chosen (p witness)) goal → Entails hyps goal := by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_forall_aux _ hidx rfl _ rfl (by grind)

theorem Entails_specialize_forall_by_idx (idx : Nat)
  (hpred : hyps[idx]?.map NamedPred.pred = some (TLA.tlaForall p)) :
  Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, p witness⟩)) goal → Entails hyps goal := by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_forall_aux _ hidx rfl _ rfl (by grind)

end

section

variable {rhs : pred σ} {q : Prop} (hq : q)
include hq

theorem Entails_specialize_pure_by_name (chosen : String)
  (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, [tlafml| ⌞ q ⌟ → rhs]⟩) :
  Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal := by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_pure_aux _ hidx rfl hq rfl (by grind)

theorem Entails_specialize_pure_by_idx (idx : Nat)
  (hpred : hyps[idx]?.map NamedPred.pred = some [tlafml| ⌞ q ⌟ → rhs]) :
  Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal := by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_pure_aux _ hidx rfl hq rfl (by grind)

end

section

variable {lhs rhs : pred σ} (hlhs : TLA.valid lhs)
include hlhs

theorem Entails_specialize_valid_by_name (chosen : String)
  (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, [tlafml| lhs → rhs]⟩) :
  Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal := by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_valid_aux _ hidx rfl hlhs rfl (by grind)

theorem Entails_specialize_valid_by_idx (idx : Nat)
  (hpred : hyps[idx]?.map NamedPred.pred = some [tlafml| lhs → rhs]) :
  Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal := by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_valid_aux _ hidx rfl hlhs rfl (by grind)

end

section

variable {rhs : pred σ} {lhss : List (pred σ)} (premises : List String)
  -- (hprem : hyps.find? (fun h => h.name == premise) = some ⟨premise, lhs⟩)
  (hprem : premises.filterMap (fun premise => hyps.find? (fun h => h.name == premise) |>.map NamedPred.pred) = lhss)
include hprem

theorem Entails_specialize_temporal_by_name (chosen : String)
  (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, [tlafml| (repeatedAnd lhss) → rhs]⟩) :
  Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal := by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_temporal_aux _ hidx rfl lhss ?_ rfl (by grind)
  subst lhss; rw [← List.map_filterMap]; clear hpred ht heq1 heq2; grind

theorem Entails_specialize_temporal_by_idx (idx : Nat)
  (hpred : hyps[idx]?.map NamedPred.pred = some [tlafml| (repeatedAnd lhss) → rhs]) :
  Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal := by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_temporal_aux _ hidx rfl lhss ?_ rfl (by grind)
  subst lhss; rw [← List.map_filterMap]; clear heq; grind

end

end

private def specializeTacDSimps := #[``replaceChosenPred, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go,
  ``String.reduceBEq, ``String.reduceBNe, ``dreduceIte, ``Option.elim,
  ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx, ``List.modifyTailIdx.go,
  ``List.modifyHead]

/-- Specialize one temporal hypothesis once, then simplify the reflected
hypothesis list back to the literal proof-mode context. Callers build repeated
specialization by invoking this after each argument, so each step sees the
predicate produced by the previous step. -/
def tlaSpecializeStep (pos : TemporalHypLoc) (arg : TSyntax `term) : TacticM Unit := withMainContext do
  -- FIXME: Repetitively running `recognizeEntailsHypsFromGoal` and `find?` on it
  -- might be slow in some extreme cases?
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | throwError "tla_specialize: failed to read the hypotheses from the goal"
  let (_, pred) ← findByTemporalHypLoc hyps pos "tla_specialize" "the goal's Entails list"
  match_expr pred with
  | TLA.tlaForall _ _ _ =>
    let thm := if pos matches .byName .. then ``Entails_specialize_forall_by_name else ``Entails_specialize_forall_by_idx
    evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_)
  | TLA.tlaImplies _ lhs _ =>
    if lhs.isAppOfArity' ``TLA.purePred 2 then
      -- Treat `arg` as a Lean term
      let thm := if pos matches .byName .. then ``Entails_specialize_pure_by_name else ``Entails_specialize_pure_by_idx
      evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_)
    else
      (do
        let thm := if pos matches .byName .. then ``Entails_specialize_valid_by_name else ``Entails_specialize_valid_by_idx
        evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_))
      <|>
      (do
        let premises ← match arg with
          | `(term| ⟨ $args:term,* ⟩) => pure args.getElems.toList
          | _ => pure [arg]
        let premises ← premises.mapM fun arg => do
          match (← termIdentOpt arg) with
          | some id => pure <| toString id.getId
          | _ => throwError "tla_specialize: implication arguments must be a tuple or a single identifier; got {arg}"
        for premise in premises do
          unless hyps.any (fun ⟨name, _⟩ => name == premise) do
            throwError "tla_specialize: temporal hypothesis '{premise}' not found in the goal's Entails list"
        let thm := if pos matches .byName .. then ``Entails_specialize_temporal_by_name else ``Entails_specialize_temporal_by_idx
        evalTactic <| ← `(tactic| refine $(mkIdent thm) ($(quote premises)) (by rfl) ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_))
  | _ => throwError (specializeTargetBadShapeMsg pred pos)
  postDSimpAfterApplyingReflectionTheorem specializeTacDSimps
where
  /-- Error message for a specialize target of an unsupported shape. -/
  specializeTargetBadShapeMsg (pred : Expr) : TemporalHypLoc → MessageData
    | .byName name => m!"tla_specialize: hypothesis '{name}' is not a ∀ or implication; got {pred}"
    | .byIdx idx => m!"tla_specialize: hypothesis index {idx} is not a ∀ or implication; got {pred}"

/--
`tla_specialize h arg₁ arg₂ ...` specializes a proof-mode temporal hypothesis
in place.

If `h : ∀ n, P n`, then
```lean
tla_specialize h 0
```
changes `h` to `P 0`. If `h : p → q` and `hp : p` is a temporal hypothesis,
then
```lean
tla_specialize h hp
```
changes `h` to `q` and keeps `hp` in the context. Numeric hypothesis indices
may be used in place of names.
-/
syntax (name := tlaSpecializeTac) "tla_specialize" (ppSpace colGt temporalHypLoc) (ppSpace colGt term:arg)+ : tactic

elab_rules : tactic
  | `(tactic| tla_specialize $h:temporalHypLoc $[$args:term]*) => do
    let pos ← parseTemporalHypLoc h "tla_specialize: invalid syntax for specialization position"
    for arg in args do
      tlaSpecializeStep pos arg

end TLA.ProofMode
