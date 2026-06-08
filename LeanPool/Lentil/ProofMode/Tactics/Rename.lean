/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Location

namespace TLA.ProofMode

open Lean Meta Elab Tactic

local macro "renameFun" : term => `((fun ⟨_, pred⟩ => ⟨$(mkIdent `newName), pred⟩))

section

variable {σ : Type u} {hyps hyps' : List (NamedPred σ)} {goal : pred σ} (newName : String)
  (idx : Nat) (h : ModifyHypSpecWithIndex hyps hyps' renameFun idx)
include h

private theorem renameHyp_pred_same : hyps'.map NamedPred.pred = hyps.map NamedPred.pred := by
  rcases h with rfl | ⟨hidx, rfl⟩
  on_goal 1=> rfl
  dsimp; rw [List.modify_eq_take_cons_drop hidx]
  conv => enter [2, 2]; rw [← LentilLib.List.take_getElem_drop hidx]
  simp only [List.map_append, List.map_take, List.map_cons, List.map_drop]

private theorem Entails_rename_aux : Entails hyps' goal = Entails hyps goal := by
  unfold Entails; congr 1; rw [renameHyp_pred_same newName idx h]

end

/-- Rename a hypothesis in a hypothesis list. -/
def renameHyp {σ : Type u} (hyps : List (NamedPred σ)) (oldName newName : String) :=
  modifyHypByName hyps oldName renameFun

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ} (newName : String)

theorem Entails_rename_by_name (oldName : String) :
  Entails (renameHyp hyps oldName newName) goal = Entails hyps goal := by
  obtain ⟨idx, hspec⟩ := ModifyHypSpec_implies_ModifyHypSpecWithIndex <| modifyHypByName_spec hyps oldName renameFun
  exact Entails_rename_aux newName idx hspec

theorem Entails_rename_by_idx (idx : Nat) :
  Entails (hyps.modify idx renameFun) goal = Entails hyps goal := Entails_rename_aux newName idx (ModifyHypSpecWithIndex_modify _ _ _)

end

private def renameTacDSimps := #[``renameHyp, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go, ``String.reduceBEq, ``String.reduceBNe,
    ``dreduceIte, ``Option.elim, ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx,
    ``List.modifyTailIdx.go, ``List.modifyHead]

/-- Rename the hypothesis at the given location. -/
def tlaRename (old : TemporalHypLoc) (newStr : String) : TacticM Unit := do
  let thm := if old matches .byName .. then ``Entails_rename_by_name else ``Entails_rename_by_idx
  evalTactic <| ← `(tactic|
    refine ($(mkIdent thm) ($(quote newStr)) ($(quoteTemporalHypLocToTerm old))).$(mkIdent `mp) ?_)
  postDSimpAfterApplyingReflectionTheorem renameTacDSimps

/--
`tla_rename h => h'` renames a proof-mode temporal hypothesis. The predicate
and the hypothesis position are unchanged.

For example, if the context contains `hp : p`, then
```lean
tla_rename hp => hp'
```
changes the context entry to `hp' : p`. A numeric index can be used instead of
a name:
```lean
tla_rename 0 => hHead
```
-/
syntax (name := tlaRenameTac) "tla_rename" (ppSpace colGt temporalHypLoc) " => " ident : tactic

elab_rules : tactic
  | `(tactic| tla_rename $old:temporalHypLoc => $new:ident) => do
    let old ← parseTemporalHypLoc old "tla_rename: invalid syntax for renaming position"
    let newStr := toString new.getId
    tlaRename old newStr

end TLA.ProofMode
