/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Self-delimiting word emission — definitions

The encoded-store update path needs to re-emit decoded entries. A generic
work-tape pass either emits one unary width mark per source bit or copies the
payload bits themselves. `wordEncodeTM` composes those passes around a rewind.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Which half of a self-delimiting word a work-tape pass emits. -/
inductive WorkEmitMode where
  | width
  | payload
  deriving DecidableEq

/-- `WorkEmitMode` is a finite controller parameter. -/
instance instFintypeWorkEmitMode : Fintype WorkEmitMode where
  elems := {.width, .payload}
  complete := fun mode => by cases mode <;> simp

/-- Finite phases of one work-tape emission pass. -/
inductive WorkEmitPhase where
  | scan
  | done
  deriving DecidableEq

/-- `WorkEmitPhase` has exactly two states. -/
instance instFintypeWorkEmitPhase : Fintype WorkEmitPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- Bits emitted by one complete pass. Width mode emits unary length followed
by its zero separator; payload mode copies the source bits verbatim. -/
def workEmitBits : WorkEmitMode → List Bool → List Bool
  | .width, bits => List.replicate bits.length true ++ [false]
  | .payload, bits => bits

/-- Scan one canonical Boolean work tape and append either its unary-width
header or its payload to the output. -/
def workEmitTM {n : ℕ} (idx : Fin n) (mode : WorkEmitMode) : TM n where
  Q := WorkEmitPhase
  qstart := .scan
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .scan =>
        match wHeads idx with
        | .zero =>
            (.scan, fun i => TM.readBackWrite (wHeads i),
              if mode = .width then .one else .zero,
              TM.idleDir iHead,
              fun i => if i = idx then .right else TM.idleDir (wHeads i),
              .right)
        | .one =>
            (.scan, fun i => TM.readBackWrite (wHeads i), .one,
              TM.idleDir iHead,
              fun i => if i = idx then .right else TM.idleDir (wHeads i),
              .right)
        | .blank =>
            if mode = .width then
              (.done, fun i => TM.readBackWrite (wHeads i), .zero,
                TM.idleDir iHead, fun i => TM.idleDir (wHeads i), .right)
            else
              TM.allReadBack .done iHead wHeads oHead
        | .start => TM.allReadBack .scan iHead wHeads oHead
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | scan =>
        cases hread : wHeads idx
        · exact ⟨TM.idleDir_right_of_start, by
            intro i hi
            by_cases hidx : i = idx
            · simp [hidx]
            · simp [hidx, TM.idleDir_right_of_start hi], fun _ => rfl⟩
        · exact ⟨TM.idleDir_right_of_start, by
            intro i hi
            by_cases hidx : i = idx
            · simp [hidx]
            · simp [hidx, TM.idleDir_right_of_start hi], fun _ => rfl⟩
        · dsimp only
          split
          · exact ⟨TM.idleDir_right_of_start,
              fun _ => TM.idleDir_right_of_start, fun _ => rfl⟩
          · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Exact time of one work-tape emission pass. -/
def workEmitTime (bits : List Bool) : ℕ := bits.length + 1

/-- Emit one complete self-delimiting word from a canonical binary work tape. -/
def wordEncodeTM {n : ℕ} (idx : Fin n) : TM n :=
  TM.seqTM (workEmitTM idx .width)
    (TM.seqTM (TM.rewindWorkTM idx) (workEmitTM idx .payload))

/-- Conservative exact-composition bound for one emitted natural. -/
def wordEncodeTime (value : ℕ) : ℕ :=
  3 * value.bits.length + 7

/-- Rewind an arbitrary positive cursor over canonical binary contents, then
emit the complete self-delimiting word. -/
def rewindWordEncodeTM {n : ℕ} (idx : Fin n) : TM n :=
  TM.seqTM (TM.rewindWorkTM idx) (wordEncodeTM idx)

/-- Composition bound for rewind followed by complete word emission. -/
def rewindWordEncodeTime (value headBound : ℕ) : ℕ :=
  headBound + 2 + 1 + wordEncodeTime value

end Machine

end RegisterStore

end RAM

end Complexity
