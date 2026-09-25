/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Defs

/-!
# Dense-overlay public-input initialization -- definitions

The optimized initializer counts the immutable input in binary but emits only
the tagged `R₀` overlay entry. It then installs the ordinary sparse scanner ABI
and rewinds the real input for dense fallback reads.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Phases of the input-length counter. -/
inductive DenseInitialLengthPhase where
  | scan
  | done
  deriving DecidableEq

instance : Fintype DenseInitialLengthPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- State space for input scanning with one binary-successor body. -/
abbrev DenseInitialLengthQ {n : ℕ} (tapes : ControlInstructionTapes n) :=
  DenseInitialLengthPhase ⊕ (initialZeroBitTM tapes).Q

/-- Count every input symbol into the existing initialization address tape. -/
def denseInitialLengthLoopTM {n : ℕ}
    (tapes : ControlInstructionTapes n) : TM (n + 1) where
  Q := DenseInitialLengthQ tapes
  qstart := .inl .scan
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .scan =>
        if iHead = Γ.blank then
          TM.allReadBack (.inl .done) iHead wHeads oHead
        else
          TM.allReadBack (.inr (initialZeroBitTM tapes).qstart)
            iHead wHeads oHead
    | .inl .done => TM.allIdle (.inl .done) iHead wHeads oHead
    | .inr state =>
        if state = (initialZeroBitTM tapes).qhalt then
          (.inl .scan, fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, Dir3.right,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let action := (initialZeroBitTM tapes).δ state iHead wHeads oHead
          (.inr action.1, action.2.1, action.2.2.1, action.2.2.2.1,
            action.2.2.2.2.1, action.2.2.2.2.2)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .scan =>
        dsimp only
        split <;> exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact TM.rightOfStart_allIdle iHead wHeads oHead
    | .inr state =>
        dsimp only
        split
        · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (initialZeroBitTM tapes).δ_right_of_start state
            iHead wHeads oHead

/-- Exact recursive time budget for binary input-length counting. -/
def denseInitialLengthLoopTime : ℕ → List Bool → ℕ
  | _, [] => 1
  | address, _ :: rest =>
      1 + TM.binarySuccTime address + 1 +
        denseInitialLengthLoopTime (address + 1) rest

/-- The lone positive-tag overlay installed for the public input. -/
def denseProgramInitialStore (input : List Bool) : Store :=
  (DenseOverlay.Snapshot.initial input).overlay

/-- Exact clean work image of a dense-overlay snapshot. -/
def denseProgramSnapshotWork {n : ℕ} (tapes : ControlInstructionTapes n)
    (snapshot : DenseOverlay.Snapshot) : Fin (n + 1) → Tape :=
  programSnapshotWork tapes { pc := snapshot.pc, store := snapshot.overlay }

/-- Count the input, emit its positive `R₀` tag, install the sparse ABI, and
rewind the immutable input bank to cell one. -/
def denseProgramInitTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM (initialSetupTM tapes)
    (TM.seqTM (denseInitialLengthLoopTM tapes)
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes) TM.rewindInputTM)))

/-- Exact compositional time budget for dense-overlay initialization. -/
def denseProgramInitTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (input : List Bool) : ℕ :=
  (1 + 1 + (TM.binarySuccTime 0 + 1 + TM.binarySuccTime 0)) + 1 +
    (denseInitialLengthLoopTime 1 input + 1 +
      ((rewindEntryEncodeRestoreTime (0, input.length + 1) + 1 +
          TM.binarySuccTime 0) + 1 +
        (initialAbiInstallTime tapes (denseProgramInitialStore input)
            (input.length + 1) + 1 +
          (input.length + 1 + 2))))

end Machine
end RegisterStore
end RAM
end Complexity
