/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Tactics.Revert
import LeanPool.Lentil.ProofMode.Tactics.Specialize

namespace TLA.ProofMode

open Lean Meta Elab Tactic

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

/-- If the proof-mode context contains `tlaFalse`, every goal follows
    vacuously. -/
theorem Entails_of_false_in_hyps (idx : Nat) (h : hyps[idx]?.map NamedPred.pred = some tlaFalse) :
  Entails hyps goal := by
  simp [← List.get?Internal_eq_getElem?] at h; rcases h with ⟨a, h1, h2⟩
  apply Entails_revert_by_idx idx
  simp only [h1, Option.elim, h2]
  intro _ _ hfalse; exact hfalse.elim

/-- If the proof-mode context contains both `p` and `¬ p`, every goal follows. -/
theorem Entails_of_contradicting_hyps {p : pred σ}
  (idx1 idx2 : Nat)
  (h1 : hyps[idx1]?.map NamedPred.pred = some p)
  (h2 : hyps[idx2]?.map NamedPred.pred = some (tlaNot p)) :
  Entails hyps goal := by
  apply Entails_add_new [p, tlaNot p] (by grind) "_" tlaFalse
  · dsimp only [repeatedAnd, LentilLib.List.foldrD]; rw [TLA.and_not_self_iff]
  · apply Entails_of_false_in_hyps hyps.length (by simp)

end

/--
`tla_contradiction` closes any proof-mode goal whose context contains an
explicit contradiction:

* a temporal hypothesis with predicate `⊥` (i.e. `tlaFalse`), or
* a pair of temporal hypotheses with predicates `p` and `¬ p`.

It fails if neither pattern is found.
-/
syntax (name := tlaContradictionTac) "tla_contradiction" : tactic

elab_rules : tactic
  | `(tactic| tla_contradiction) => withMainContext do
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "tla_contradiction: goal is not an Entails sequent"
    -- Step 1: a `tlaFalse` hypothesis closes the goal directly.
    if let some idx := hyps.findIdx? fun x => x.2.isAppOf' ``TLA.tlaFalse then
      evalTactic <| ← `(tactic| exact $(mkIdent ``Entails_of_false_in_hyps) ($(quote idx)) (by rfl))
      return
    -- Step 2: a `(p, ¬ p)` pair, with `p` matched by `isDefEq`.
    let hyps := hyps.zipIdx
    for (x, idx2) in hyps do
      let_expr TLA.tlaNot _ p := x.2 | continue
      if let some (_, idx1) ← hyps.findM? fun y => isDefEq y.1.2 p then
        evalTactic <| ← `(tactic|
          exact $(mkIdent ``Entails_of_contradicting_hyps) ($(quote idx1)) ($(quote idx2)) (by rfl) (by rfl))
        return
    throwError "tla_contradiction: no contradiction found in proof-mode context"

end TLA.ProofMode
