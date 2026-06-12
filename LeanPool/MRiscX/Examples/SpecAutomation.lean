/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Basic
import LeanPool.MRiscX.Tactics.ApplySpec

/-!
# SpecAutomation

This module exercises the automatic specification application (`applySpec''` and
`applySpec'`) on the store instruction and on every jump instruction shape, so that
each branch of the instruction-dispatch in `Tactics/ApplySpec.lean` is covered by a
proved Hoare triple.
-/

/-
Store via the inferred specification (`specification_StoreWordImmediate`).
-/
example :
    mriscx
      start:  sw x 2, x 3
    end
    ⦃(x[2] = 7 ∧ x[3] = 0x321) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[2] = 7 ∧ x[3] = 0x321) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

/-
Unconditional jump (`specification_Jump`).
-/
example :
    mriscx
      start:  j fin
              inc x 5
      fin: end
    ⦃(x[0] = 7 ∧ labels[fin] = some 2) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] = 7) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

/-
Conditional jumps, taken branch (`specification_…_true`): the postcondition keeps
the label fact, so the inferred application unifies with the `_true` specification.
-/
example :
    mriscx
      start:  beq x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] = x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] = x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  bne x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] ≠ x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] ≠ x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  bgt x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] > x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] > x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  ble x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] ≤ x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] ≤ x[1]) ∧ labels[fin] = some 2 ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  beqz x 0, fin
              inc x 5
      fin: end
    ⦃(x[0] = 0 ∧ labels[fin] = some 2) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] = 0) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  bnez x 0, fin
              inc x 5
      fin: end
    ⦃(x[0] ≠ 0 ∧ labels[fin] = some 2) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{2} | {n : UInt64 | n ≠ 2}⟩
    ⦃(x[0] ≠ 0) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

/-
Conditional jumps, fall-through branch (`specification_…_false`): without the label
fact in the postcondition the `_true` specification does not unify, so the inferred
application falls back to the `_false` specification.
-/
example :
    mriscx
      start:  beq x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] ≠ x[1]) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] ≠ x[1]) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  bne x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] = x[1]) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] = x[1]) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  bgt x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] ≤ x[1]) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] ≤ x[1]) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

example :
    mriscx
      start:  ble x 0, x 1, fin
              inc x 5
      fin: end
    ⦃(x[0] > x[1]) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] > x[1]) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec''

/-
For `beqz`/`bnez` the `_true` and `_false` postconditions have the same shape, so the
fall-through case names the specification explicitly (`applySpec'`), which dispatches
through the same corrected tactic branch.
-/
example :
    mriscx
      start:  beqz x 0, fin
              inc x 5
      fin: end
    ⦃(x[0] ≠ 0) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] ≠ 0) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec' specification_JumpEqZero_false

example :
    mriscx
      start:  bnez x 0, fin
              inc x 5
      fin: end
    ⦃(x[0] = 0) ∧ ¬⸨terminated⸩⦄
    "start" ↦ ⟨{1} | {n : UInt64 | n ≠ 1}⟩
    ⦃(x[0] = 0) ∧ ¬⸨terminated⸩⦄
  := by
  applySpec' specification_JumpNeqZero_false
