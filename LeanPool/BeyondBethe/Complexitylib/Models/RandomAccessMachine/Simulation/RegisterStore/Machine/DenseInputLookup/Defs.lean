/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Dense public-input lookup -- definitions

These finite controllers are the concrete bridge from a sparse mutable RAM
overlay to the immutable public input on the Turing input tape. The scan keeps
a binary countdown on a work tape. When that countdown first reaches zero,
the preceding input symbol is copied to a canonical Boolean result tape.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Two-state framed identity used as a direct-branch leaf. -/
inductive DenseInputIdlePhase where
  | run
  | done
  deriving DecidableEq

instance : Fintype DenseInputIdlePhase where
  elems := {.run, .done}
  complete := fun phase => by cases phase <;> simp

/-- A one-step identity on every parked tape. -/
def denseInputIdleTM {n : ℕ} : TM n where
  Q := DenseInputIdlePhase
  qstart := .run
  qhalt := .done
  δ := fun _ iHead wHeads oHead =>
    (.done, fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
      TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
      TM.idleDir_right_of_start⟩

/-- Two-step controller that moves left to the preceding input symbol, copies
that Boolean value to one work cell, and restores the input head. -/
inductive DenseInputCapturePhase where
  | moveLeft
  | write
  | done
  deriving DecidableEq

instance : Fintype DenseInputCapturePhase where
  elems := {.moveLeft, .write, .done}
  complete := fun phase => by cases phase <;> simp

/-- Canonical binary work tape representing one public-input bit. -/
def denseInputBitTape (bit : Bool) : Tape :=
  TM.resetBinaryBlank.writeAndMove
    (if bit then Γw.one.toΓ else Γw.blank.toΓ) Dir3.stay

/-- Copy the Boolean input symbol immediately to the left of the current head
onto a blank canonical result tape, restoring the input head in two steps. -/
def capturePreviousInputBitTM {n : ℕ} (result : Fin n) : TM n where
  Q := DenseInputCapturePhase
  qstart := .moveLeft
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .moveLeft =>
        (.write, fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, TM.moveLeftDir iHead,
          fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
    | .write =>
        (.done,
          fun i =>
            if i = result then
              if iHead = Γ.one then Γw.one else Γw.blank
            else TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, Dir3.right,
          fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | moveLeft =>
        exact ⟨TM.moveLeftDir_right_of_start,
          fun _ => TM.idleDir_right_of_start,
          TM.idleDir_right_of_start⟩
    | write =>
        exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
          TM.idleDir_right_of_start⟩
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- One input-scan body step. A zero countdown is stationary. A positive
countdown is decremented; when it becomes zero, the preceding input bit is
captured exactly once. -/
def denseInputStepTM {n : ℕ} (counter result : Fin n) : TM n :=
  TM.branchWorkBlankTM counter denseInputIdleTM
    (TM.seqTM (TM.binaryPredTM counter)
      (TM.branchWorkBlankTM counter
        (capturePreviousInputBitTM result) denseInputIdleTM))

/-- Exact body time as a function of the positive-or-zero countdown. -/
def denseInputStepTime (remaining : ℕ) : ℕ :=
  if remaining = 0 then 2
  else if remaining = 1 then TM.binaryPredTime 0 + 5
  else TM.binaryPredTime (remaining - 1) + 4

/-- Result tape after one scan iteration. Only the transition from countdown
one to zero captures the current input bit. -/
def denseInputStepResult (remaining : ℕ) (bit : Bool)
    (current : Tape) : Tape :=
  if remaining = 1 then denseInputBitTape bit else current

/-- Scan the entire immutable Boolean input while decrementing a canonical
binary address counter and capturing the addressed bit. -/
def denseInputScanTM {n : ℕ} (counter result : Fin n) : TM n :=
  TM.forInputTM (denseInputStepTM counter result)

/-- Exact complete input-scan time from a positive address. -/
def denseInputScanTime (inputLength address : ℕ) : ℕ :=
  TM.forInputLoopTime
    (fun processed => denseInputStepTime (address - processed))
    0 inputLength

/-- Full positive-address dense-bank fallback: copy the query into a private
countdown, scan the immutable input, rewind the input head, and clear the
countdown back to the reusable blank boundary. -/
def denseInputLookupTM {n : ℕ}
    (query counter result scratch : Fin n) : TM n :=
  TM.seqTM (TM.binaryCopyIntoTM query counter scratch)
    (TM.seqTM (denseInputScanTM counter result)
      (TM.seqTM TM.rewindInputTM (TM.resetBinaryWorkTM counter)))

/-- Complete fallback budget, including all three sequencing seams. -/
def denseInputLookupTime (inputLength address : ℕ) : ℕ :=
  TM.binaryCopyTime address 0 + 1 +
    (denseInputScanTime inputLength address + 1 +
      (inputLength + 3 + 1 +
        TM.resetBinaryWorkTime 1 (address - inputLength).bits.length))

/-- Reusable work-tape boundary before a positive-address dense-bank lookup. -/
structure DenseInputLookupReady {n : ℕ}
    (query counter result scratch : Fin n) (address : ℕ)
    (work : Fin n → Tape) : Prop where
  query : (work query).HasBinaryNat address
  counter : (work counter).HasBinaryNat 0
  result : (work result).HasBinaryNat 0
  scratch : (work scratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)

/-- Reusable work-tape endpoint after dense-bank fallback. -/
structure DenseInputLookupResult {n : ℕ}
    (query counter result scratch : Fin n) (input : List Bool)
    (address : ℕ) (initialWork finalWork : Fin n → Tape) : Prop where
  query_eq : finalWork query = initialWork query
  counter_zero : (finalWork counter).HasBinaryNat 0
  result_value : (finalWork result).HasBinaryNat
    (Complexity.RAM.initRegs input address)
  scratch_eq : finalWork scratch = initialWork scratch
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, i ≠ query → i ≠ counter → i ≠ result → i ≠ scratch →
    finalWork i = initialWork i

end Machine
end RegisterStore
end RAM
end Complexity
