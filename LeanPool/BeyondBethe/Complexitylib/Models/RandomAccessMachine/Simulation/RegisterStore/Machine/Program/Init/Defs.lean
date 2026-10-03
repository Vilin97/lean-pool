/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Defs

/-!
# Sparse RAM public-input initialization definitions

This layer constructs the reusable sparse-snapshot ABI from the standard TM
input tape. It emits nonzero bit registers in increasing address order, then
appends the nonzero length register `R₀`. The resulting order need not equal
`initialStore`; it is a canonical sparse store representing the same total
RAM register file.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Nonzero public-input bit registers, beginning at `address`. -/
def inputBitStoreFrom : ℕ → List Bool → Store
  | _, [] => []
  | address, bit :: rest =>
      (if bit then [(address, 1)] else []) ++
        inputBitStoreFrom (address + 1) rest

/-- Streaming-friendly public-input store: bit registers first and the
nonzero length register last. -/
def programInitialStore (input : List Bool) : Store :=
  RegisterStore.write (inputBitStoreFrom 1 input) 0 input.length

/-- Sparse initial snapshot used by the concrete initialization machine. -/
def programInitialSnapshot (input : List Bool) : Snapshot :=
  { pc := 0, store := programInitialStore input }

/-- Number of nonzero entries emitted by the bit-register prefix. -/
def inputTrueCount : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + inputTrueCount rest

/-- Append-positioned binary tape for an emitted store prefix. -/
def programBinaryPrefixTape (bits : List Bool) : Tape :=
  { head := bits.length + 1
    cells := (Tape.init (bits.map Γ.ofBool)).cells }

/-- Exact work family at a streaming input-loop boundary. -/
def initialLoopWork {n : ℕ} (tapes : ControlInstructionTapes n)
    (address count : ℕ) (entries : Store) : Fin (n + 1) → Tape :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.const (Fin (n + 1)) TM.resetBinaryBlank)
          tapes.liftedLhs (programBinaryTape address.bits))
        tapes.lifted.data.rhs (programBinaryTape (1 : ℕ).bits))
      tapes.lifted.data.update.remaining
        (programBinaryTape count.bits))
    tapes.buffer
      (programBinaryPrefixTape (entries.flatMap Entry.encode))

/-- Streaming input-loop invariant. Only the current address, fixed value one,
runtime entry count, and append buffer differ from the standard blank frame. -/
structure InitialLoopReady {n : ℕ} (tapes : ControlInstructionTapes n)
    (address count : ℕ) (entries : Store)
    (work : Fin (n + 1) → Tape) : Prop where
  address : (work tapes.liftedLhs).HasBinaryNat address
  value : (work tapes.lifted.data.rhs).HasBinaryNat 1
  count : (work tapes.lifted.data.update.remaining).HasBinaryNat count
  buffer : (work tapes.buffer).HasBinaryPrefix
    (entries.flatMap Entry.encode)
  parked : ∀ i, TM.Parked (work i)
  frame : ∀ i, i ≠ tapes.liftedLhs → i ≠ tapes.lifted.data.rhs →
    i ≠ tapes.lifted.data.update.remaining → i ≠ tapes.buffer →
    work i = TM.resetBinaryBlank

/-- Recursive work-independent streaming-loop bound. -/
def initialInputLoopTime {n : ℕ} (tapes : ControlInstructionTapes n) :
    ℕ → ℕ → List Bool → ℕ
  | _, _, [] => 1
  | address, count, bit :: rest =>
      let bodyTime := if bit then
        rewindEntryEncodeRestoreTime (address, 1) + 1 +
          TM.binarySuccTime count + 1 + TM.binarySuccTime address
        else TM.binarySuccTime address
      1 + bodyTime + 1 +
        initialInputLoopTime tapes (address + 1)
          (count + if bit then 1 else 0) rest

/-- Dynamic address/value assignment for one nonzero input bit. -/
def initialBitEntryTapes {n : ℕ} (tapes : ControlInstructionTapes n) :
    EntryEncodeTapes n where
  address := tapes.data.lhs
  value := tapes.data.rhs
  ne := tapes.data.ne (by decide)

/-- Address-zero/length assignment for the final `R₀` entry. -/
def initialLengthEntryTapes {n : ℕ} (tapes : ControlInstructionTapes n) :
    EntryEncodeTapes n where
  address := tapes.data.update.entry.query
  value := tapes.data.lhs
  ne := tapes.data.ne (by decide)

/-- Emit one nonzero bit entry, restore both entry sources to cell one, then
increment the runtime entry count and current input address. -/
def initialOneBitTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM
    (rewindEntryEncodeRestoreTM (initialBitEntryTapes tapes)).retargetOutput
    (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
      (TM.binarySuccTM tapes.liftedLhs))

/-- A zero input bit emits no entry and only advances the current address. -/
def initialZeroBitTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.binarySuccTM tapes.liftedLhs

/-- Driver phases for streaming over the real Boolean input. -/
inductive InitialInputPhase where
  | scan
  | done
  deriving DecidableEq

instance : Fintype InitialInputPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- State space of the public-input bit loop. -/
abbrev InitialInputQ {n : ℕ} (tapes : ControlInstructionTapes n) :=
  InitialInputPhase ⊕ ((initialOneBitTM tapes).Q ⊕ (initialZeroBitTM tapes).Q)

/-- Scan the real input without moving before body entry. Each `1` invokes the
entry-emitting body, each `0` invokes the address-only body, and the preserving
body seam advances the input by one cell. -/
def initialInputLoopTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) where
  Q := InitialInputQ tapes
  qstart := .inl .scan
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .scan =>
        if iHead = Γ.blank then
          TM.allReadBack (.inl .done) iHead wHeads oHead
        else if iHead = Γ.one then
          TM.allReadBack (.inr (.inl (initialOneBitTM tapes).qstart))
            iHead wHeads oHead
        else
          TM.allReadBack (.inr (.inr (initialZeroBitTM tapes).qstart))
            iHead wHeads oHead
    | .inl .done => TM.allIdle (.inl .done) iHead wHeads oHead
    | .inr (.inl state) =>
        if state = (initialOneBitTM tapes).qhalt then
          (.inl .scan, fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, Dir3.right,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let action := (initialOneBitTM tapes).δ state iHead wHeads oHead
          (.inr (.inl action.1), action.2.1, action.2.2.1,
            action.2.2.2.1, action.2.2.2.2.1, action.2.2.2.2.2)
    | .inr (.inr state) =>
        if state = (initialZeroBitTM tapes).qhalt then
          (.inl .scan, fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, Dir3.right,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let action := (initialZeroBitTM tapes).δ state iHead wHeads oHead
          (.inr (.inr action.1), action.2.1, action.2.2.1,
            action.2.2.2.1, action.2.2.2.2.1, action.2.2.2.2.2)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .scan =>
        dsimp only
        split
        · exact TM.rightOfStart_allReadBack iHead wHeads oHead
        · split <;> exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact TM.rightOfStart_allIdle iHead wHeads oHead
    | .inr (.inl state) =>
        dsimp only
        split
        · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (initialOneBitTM tapes).δ_right_of_start state
            iHead wHeads oHead
    | .inr (.inr state) =>
        dsimp only
        split
        · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (initialZeroBitTM tapes).δ_right_of_start state
            iHead wHeads oHead

/-- Emit the nonzero `R₀ = |input|` entry and increment the entry count. -/
def initialLengthEmitTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM
    (rewindEntryEncodeRestoreTM
      (initialLengthEntryTapes tapes)).retargetOutput
    (TM.binarySuccTM tapes.lifted.data.update.remaining)

/-- Skip the length entry at zero; otherwise append it to the buffer. -/
def initialLengthTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.branchWorkBlankTM tapes.liftedLhs TM.skipTM
    (initialLengthEmitTM tapes)

/-- Selected-branch bound for optional length-register emission. -/
def initialLengthTime (length count : ℕ) : ℕ :=
  1 + if length = 0 then 1 else
    rewindEntryEncodeRestoreTime (0, length) + 1 +
      TM.binarySuccTime count

/-- Cleanup targets used after the complete input store has been copied into
the read-only source role. -/
def initialCleanupTargets {n : ℕ}
    (tapes : ControlInstructionTapes n) : List (Fin (n + 1)) :=
  [tapes.liftedLhs, tapes.lifted.data.rhs]

/-- Canonical contents reset by the final two-target cleanup. -/
def initialCleanupBits {n : ℕ} (tapes : ControlInstructionTapes n)
    (length : ℕ) (i : Fin (n + 1)) : List Bool :=
  if i = tapes.liftedLhs then length.bits
  else if i = tapes.lifted.data.rhs then (1 : ℕ).bits
  else []

/-- Exact compositional bound for installing a completed store into the
program-loop ABI. -/
def initialAbiInstallTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) (length : ℕ) : ℕ :=
  let encodedLength := (store.flatMap Entry.encode).length
  TM.binaryCopyTime store.length 0 + 1 +
    (encodedLength + 1 + 2) + 1 +
    (encodedLength + 1) + 1 +
    (encodedLength + 1 + 2) + 1 +
    TM.resetBinaryWorkTime (encodedLength + 1) encodedLength + 1 +
    TM.resetBinaryWorkManyTime (initialCleanupBits tapes length)
      (fun _ => 1) (initialCleanupTargets tapes)

/-- Park the standard initial tapes and seed the streaming address/value
sources with one. -/
def initialSetupTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM TM.skipTM
    (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
      (TM.binarySuccTM tapes.lifted.data.rhs))

/-- Restore the address cursor from `|input| + 1` to `|input|`, then append
the optional nonzero length register. -/
def initialLengthInstallTM {n : ℕ}
    (tapes : ControlInstructionTapes n) : TM (n + 1) :=
  TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
    (initialLengthTM tapes)

/-- Copy the completed buffer into the reusable source/count roles and clear
the remaining initialization temporaries. -/
def initialAbiInstallTM {n : ℕ}
    (tapes : ControlInstructionTapes n) : TM (n + 1) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      tapes.lifted.data.update.remaining
      tapes.lifted.data.update.resultCount
      tapes.lifted.data.update.found)
    (TM.seqTM (TM.rewindWorkTM tapes.buffer)
      (TM.seqTM
        (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
        (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
          (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
            (TM.resetBinaryWorkManyTM
              (initialCleanupTargets tapes))))))

/-- Install the length entry, source/count ABI, and clean loop temporaries. -/
def initialFinalizeTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM (initialLengthInstallTM tapes) (initialAbiInstallTM tapes)

/-- Complete public-input initialization. A leading skip parks every standard
initial tape, the streaming loop writes the sparse store into the last buffer,
and the tail installs the reusable source/count ABI and clears temporary roles. -/
def programInitTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM (initialSetupTM tapes)
    (TM.seqTM (initialInputLoopTM tapes) (initialFinalizeTM tapes))

/-- Exact compositional time bound for complete public-input initialization. -/
def programInitTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (input : List Bool) : ℕ :=
  (1 + 1 + (TM.binarySuccTime 0 + 1 + TM.binarySuccTime 0)) + 1 +
    (initialInputLoopTime tapes 1 0 input + 1 +
      ((TM.binaryPredTime input.length + 1 +
          initialLengthTime input.length (inputTrueCount input)) + 1 +
        initialAbiInstallTime tapes (programInitialStore input) input.length))

end Machine

end RegisterStore

end RAM

end Complexity
