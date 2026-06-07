/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

theorem Entails_exists {σ : Type u} {hyps : List (NamedPred σ)}
    {α : Sort v} {p : α → pred σ} (witness : α) :
    Entails hyps (p witness) → Entails hyps (TLA.tla_exists p) := exists_elim witness

/--
`tla_exists w₁, w₂, ...` supplies witnesses for existential quantifiers in the
proof-mode goal.

For example, if the goal is `∃ n : Nat, P n`, then
```lean
tla_exists 0
```
changes the goal to `P 0`. Multiple witnesses are applied from left to right,
so `tla_exists n, m` handles a goal such as `∃ n, ∃ m, P n m`.
-/
syntax (name := tlaExistsTac) "tla_exists" (ppSpace colGt term),+ : tactic

elab_rules : tactic
  | `(tactic| tla_exists $[$ts],*) => do
    for t in ts do
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_exists) $t ?_)

end TLA.ProofMode
