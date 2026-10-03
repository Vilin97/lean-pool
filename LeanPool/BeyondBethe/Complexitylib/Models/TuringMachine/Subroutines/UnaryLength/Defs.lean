/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Unary input-length transducer — definitions

This module defines a deterministic transducer that scans its Boolean input
once and writes one `true` bit per input bit. Its output is therefore the
unary representation `List.replicate x.length true` of the input length.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Control states for `unaryLengthTM`: scan the input, then halt at its first
trailing blank. -/
inductive UnaryLengthPhase where
  | copying
  | done
  deriving DecidableEq

instance : Fintype UnaryLengthPhase where
  elems := {.copying, .done}
  complete := fun state => by cases state <;> simp

/-- Scan the Boolean input from left to right and emit one `true` bit per
input bit. The first step skips the left-end markers, and the machine halts
when the input head reaches its first trailing blank. -/
def unaryLengthTM {n : ℕ} : TM n where
  Q := UnaryLengthPhase
  qstart := .copying
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copying =>
      if iHead = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.copying, fun i => readBackWrite (wHeads i), .one,
          Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copying =>
      dsimp only []
      split
      · exact rightOfStart_allIdle iHead wHeads oHead
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

end TM

end Complexity
