/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import Mathlib.Data.Nat.Bits

/-!
# Little-endian binary predecessor — definitions

This module defines the finite controller for in-place predecessor on a
positive canonical binary natural. Borrow turns initial low-order zero bits
into ones. The first one becomes zero; when it was the unique high bit, a
one-cell lookahead detects the terminating blank and erases that now-redundant
zero before rewinding.

The controller is total on zero, where it simply rewinds the unchanged empty
representation. Public correctness theorems intentionally start from
`value + 1`, so no underflow behavior is claimed.
-/


@[expose] public section

namespace Complexity

namespace BinaryPred

/-- Ripple one borrow through a little-endian bit string, dropping a vacated
unique high bit. The empty case defines underflow as unchanged zero. -/
def ripple : List Bool → List Bool
  | [] => []
  | false :: rest => true :: ripple rest
  | [true] => []
  | true :: bit :: rest => false :: bit :: rest

/-- Exact transition count used by `binaryPredTM` on a canonical bit string. -/
def steps : List Bool → ℕ
  | [] => 2
  | false :: rest => steps rest + 2
  | true :: _ => 4

end BinaryPred

namespace TM

/-- Finite phases of ripple-borrow predecessor. -/
inductive BinaryPredPhase where
  | borrow
  | check
  | erase
  | rewind
  | done
  deriving DecidableEq

/-- `BinaryPredPhase` has exactly five states. -/
instance instFintypeBinaryPredPhase : Fintype BinaryPredPhase where
  elems := {.borrow, .check, .erase, .rewind, .done}
  complete := fun state => by cases state <;> simp

/-- Exact running time for decrementing canonical `value + 1` to `value`. -/
def binaryPredTime (value : ℕ) : ℕ :=
  BinaryPred.steps (value + 1).bits

/-- Explicit width-based all-prefix space budget for predecessor. -/
def binaryPredSpace (initialSpace value : ℕ) : ℕ :=
  initialSpace + 2 * (value + 1).size + 2

/-- Decrement a positive canonical little-endian natural on work tape `idx`.

The borrow phase flips initial zeros to ones and replaces the first one by
zero. A lookahead distinguishes an internal bit from the terminating blank;
the latter case erases the vacated high zero. The machine finally rewinds to
cell one. On canonical zero it takes the blank branch and leaves zero intact.
-/
def binaryPredTM {n : ℕ} (idx : Fin n) : TM n where
  Q := BinaryPredPhase
  qstart := .borrow
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .borrow =>
        match wHeads idx with
        | .zero =>
            (.borrow,
              fun i => if i = idx then Γw.one else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
        | .one =>
            (.check,
              fun i => if i = idx then Γw.zero else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
        | .blank =>
            (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .start =>
            (.borrow, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
    | .check =>
        match wHeads idx with
        | .blank =>
            (.erase, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .start =>
            (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
        | .zero | .one =>
            (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
    | .erase =>
        if wHeads idx = Γ.start then
          (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = idx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          (.rewind,
            fun i => if i = idx then Γw.blank else readBackWrite (wHeads i),
            readBackWrite oHead, idleDir iHead,
            fun i => if i = idx then Dir3.left else idleDir (wHeads i),
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
    | .borrow =>
        dsimp only
        match htarget : wHeads idx with
        | .zero | .one | .blank =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · subst i
              rw [htarget] at hi
              exact absurd hi (by decide)
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
        | .start =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · rw [if_pos hitarget]
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
    | .check =>
        dsimp only
        match htarget : wHeads idx with
        | .zero | .one | .blank =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · subst i
              rw [htarget] at hi
              exact absurd hi (by decide)
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
        | .start =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · rw [if_pos hitarget]
            · rw [if_neg hitarget]
              exact idleDir_right_of_start hi
    | .erase =>
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
