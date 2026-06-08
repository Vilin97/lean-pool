/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

-- FIXME: Replace this with `foldrDM`
/-- Build the right-associative `tlaAnd` chain `p₁ ∧ (p₂ ∧ (… ∧ pₙ))` that
    matches `repeatedAnd`'s reduced form. For `[p]` it is `p`. The empty case
    is unreachable from `tla_exit` — that branch goes through
    `Entails_nil_eq_valid` so the raw goal becomes `valid rhs` instead of the
    equivalent `(⊤) |-tla- rhs`. -/
private def buildAndChain (_σ : Expr) : List Expr → MetaM Expr
  | [] => panic! "buildAndChain: empty list"
  | [p] => pure p
  | p :: ps => do mkAppM ``TLA.tlaAnd #[p, ← buildAndChain _σ ps]

/--
`tla_exit` is the inverse of `tla_start`: it leaves the proof mode by
converting an `Entails`-shaped goal back into a raw `|-tla-` sequent whose
left-hand side is the conjunction of the proof-mode hypotheses.

For example, in a proof-mode context with `hp : p`, `hq : q`, and goal `r`,
```lean
tla_exit
```
changes the proof state back to `(p ∧ q) |-tla- r`. A single hypothesis
`hp : p` becomes `p |-tla- r`. An empty proof-mode context becomes the
canonical `|-tla- r` (i.e. `valid r`), rather than the equivalent
`(⊤) |-tla- r`.
-/
syntax (name := tlaExitTac) "tla_exit" : tactic

elab_rules : tactic
  | `(tactic| tla_exit) => withMainContext do
    let mainGoal ← getMainGoal
    let ty ← mainGoal.getType
    let ty ← cleanupAnnotAndMore ty
    let_expr TLA.ProofMode.Entails σ hypsExpr rhs := ty
      | throwError "tla_exit: goal is not an Entails sequent, but {ty}"
    let some (_, hyps) ← recognizeHypsList hypsExpr
      | throwError "tla_exit: failed to read the hyp list from {hypsExpr}"
    let preds := hyps.map (·.2)
    if preds.isEmpty then
      let thm ← mkAppM ``valid_eq_true_implies #[rhs]
      let thm ← mkAppM ``Eq.mp #[thm]
      let gs ← mainGoal.apply thm
      replaceMainGoal gs
    else
      let lhs ← buildAndChain σ preds
      let newGoal ← mkAppM ``TLA.predImplies #[lhs, rhs]
      let g' ← mainGoal.change newGoal
      replaceMainGoal [g']

end TLA.ProofMode
