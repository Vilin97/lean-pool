/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_assumption {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (idx : Nat) (hlookup : (hyps.map NamedPred.pred)[idx]? = some goal) :
  Entails hyps goal := by apply repeatedAnd_subset_implies [goal]; grind

/--
`tla_assumption` closes a proof-mode goal when the target predicate already
appears among the temporal hypotheses.

For example, from a context containing `hp : p`,
```lean
tla_assumption
```
closes the goal `p`. The match is by definitional equality, so unfolded
abbreviations of the same predicate are accepted.

Outside proof mode, `tla_assumption` falls back to Lean's ordinary
`assumption`.
-/
syntax (name := tlaAssumptionTac) "tla_assumption" : tactic

-- CHECK If in the future Lean has built-in `findIdxMOpt`, use it instead
private def findIdxMOpt (xs : List α) (p : α → TacticM Bool) : TacticM (Option Nat) :=
  go 0 xs
where
  go (idx : Nat) : List α → TacticM (Option Nat)
    | [] => return none
    | x :: xs => do
      if ← p x then
        return some idx
      else
        go (idx + 1) xs

elab_rules : tactic
  | `(tactic| tla_assumption) => withMainContext do
    (evalTactic <| ← `(tactic| assumption)) <|> do
      let target ← getMainTarget
      let_expr Entails _ hyps goal := target.headBeta.cleanupAnnotations
        | throwError "tla_assumption: goal is not a proof-mode Entails goal"
      let some (_, hyps) ← recognizeHypsList hyps
        | throwError "tla_assumption: failed to read the proof-mode hypotheses"
      let some idx ← findIdxMOpt hyps fun (_, hyp) => isDefEq hyp goal
        | throwError "tla_assumption: no matching temporal hypothesis for{indentExpr goal}"
      evalTactic <| ← `(tactic| exact $(mkIdent ``Entails_assumption) $(Syntax.mkNatLit idx) (by rfl))

end TLA.ProofMode
