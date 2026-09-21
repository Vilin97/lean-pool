/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Data.Nat.Bits

/-!
# Little-endian binary successor — definitions

This module defines the canonical tape representation and finite controller
for ripple-carry successor. Natural numbers use `Nat.bits`, whose least
significant bit comes first and whose representation of zero is empty.
Overflow therefore appends one new high bit at the first blank cell.
-/


@[expose] public section

namespace Complexity

namespace BinarySucc

/-- Ripple one carry through a little-endian bit string. -/
def ripple : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: ripple rest

/-- Exact number of transitions used by `binarySuccTM` on a canonical bit
string. It is twice the successor of the number of initial low-order one bits. -/
def steps : List Bool → ℕ
  | [] => 2
  | false :: _ => 2
  | true :: rest => steps rest + 2

end BinarySucc

namespace Tape

/-- A rewound tape containing the canonical little-endian representation of
one natural number, including its immutable left-end marker. -/
def HasBinaryNat (t : Tape) (value : ℕ) : Prop :=
  t.cells 0 = Γ.start ∧ t.HasBinaryString value.bits

end Tape

namespace TM

/-- Finite phases of ripple-carry successor. -/
inductive BinarySuccPhase where
  | carry
  | rewind
  | done
  deriving DecidableEq

/-- `BinarySuccPhase` has exactly three states. -/
instance instFintypeBinarySuccPhase : Fintype BinarySuccPhase where
  elems := {.carry, .rewind, .done}
  complete := fun state => by cases state <;> simp

/-- Exact running time of canonical successor on `value.bits`. -/
def binarySuccTime (value : ℕ) : ℕ :=
  BinarySucc.steps value.bits

/-- Increment the canonical little-endian natural on work tape `idx`.

The carry phase turns initial one bits into zero bits. The first zero becomes
one; if the carry reaches the terminating blank, one is appended there. The
machine then rewinds to cell one. Input, output, and unrelated work tapes use
the structurally safe read-back/idle action. -/
def binarySuccTM {n : ℕ} (idx : Fin n) : TM n where
  Q := BinarySuccPhase
  qstart := .carry
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .carry =>
        match wHeads idx with
        | .zero =>
            (.rewind,
              fun i => if i = idx then Γw.one else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .one =>
            (.carry,
              fun i => if i = idx then Γw.zero else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
        | .blank =>
            (.rewind,
              fun i => if i = idx then Γw.one else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .start =>
            (.carry, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
    | .rewind =>
        if wHeads idx = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = idx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = idx then Dir3.left else idleDir (wHeads i),
            idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    match phase with
    | .carry =>
        dsimp only
        match htarget : wHeads idx with
        | .zero | .one | .blank =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · subst i
              rw [htarget] at hi
              exact absurd hi (by decide)
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
        | .start =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · rw [if_pos hitarget]
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
    | .rewind =>
        dsimp only
        split
        · simp only
          refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
          by_cases hitarget : i = idx
          · rw [if_pos hitarget]
          · rw [if_neg hitarget]
            exact idleDir_right_of_start hi
        · next hnotStart =>
          simp only
          refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
          by_cases hitarget : i = idx
          · subst i
            exact absurd hi hnotStart
          · rw [if_neg hitarget]
            exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

end TM

end Complexity
