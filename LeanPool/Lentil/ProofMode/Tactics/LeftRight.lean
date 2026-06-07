/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {a b : pred σ}

-- NOTE: Implemented in a way that is probably more boring than you'd have expected
theorem Entails_or_left : Entails hyps a → Entails hyps (tla_or a b) :=
  fun h => pred_implies_trans h TLA.or_inl

theorem Entails_or_right : Entails hyps b → Entails hyps (tla_or a b) :=
  fun h => pred_implies_trans h TLA.or_inr

end

/--
`tla_left` reduces a disjunctive proof-mode goal `p ∨ q` to its left disjunct
`p`.
-/
macro "tla_left" : tactic => `(tactic| refine $(mkIdent ``Entails_or_left) ?_)

/--
`tla_right` reduces a disjunctive proof-mode goal `p ∨ q` to its right
disjunct `q`.
-/
macro "tla_right" : tactic => `(tactic| refine $(mkIdent ``Entails_or_right) ?_)

end TLA.ProofMode
