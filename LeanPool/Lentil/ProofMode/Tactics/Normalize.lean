/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

attribute [tlanormsimp ↓] TLA.impl_intro TLA.valid_eq_true_implies TLA.impl_intro_add_r TLA.and_assoc
  TLA.and_true TLA.true_and TLA.imp_true TLA.always_true TLA.eventually_true TLA.later_true
  TLA.or_false TLA.false_or TLA.forall_unit TLA.exists_unit

/--
`tlaNormalize` rewrites a raw TLA goal into a shape that proof-mode tactics can
introduce and split more predictably.

For example,
```lean
tlaNormalize
```
turns a valid implication goal such as `|-tla- p → q` into the corresponding
sequent shape `p |-tla- q`, and reassociates simple conjunction structure using
the proof-mode normalization simp set.
-/
macro "tlaNormalize" : tactic => `(tactic| simp -$(mkIdent `failIfUnchanged) only [tlanormsimp])

end TLA.ProofMode
