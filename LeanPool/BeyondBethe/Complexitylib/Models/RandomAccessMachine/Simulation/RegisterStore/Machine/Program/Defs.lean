/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs

/-!
# Sparse RAM program controller -- definitions

This layer adds the fixed-program halt test needed to iterate the checked
single-instruction simulator. The test copies the canonical program counter,
walks the same decrementing finite branch tree as instruction dispatch, and
writes `1` exactly for a selected `halt`; every continuing branch writes blank.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Two-state leaf that writes one halt verdict at the current output head. -/
inductive HaltVerdictPhase where
  | write
  | done
  deriving DecidableEq

instance : Fintype HaltVerdictPhase where
  elems := {.write, .done}
  complete := fun state => by cases state <;> simp

/-- Output symbol used by the fixed-program halt test. Continuing instructions
write blank so the instruction body regains its blank-output ABI. -/
def instructionHaltVerdict : Instr → Γw
  | .halt => .one
  | _ => .blank

/-- Canonical output tape produced by one halt-verdict leaf. -/
def instructionHaltOutput (instruction : Instr) : Tape :=
  let blank := (Tape.init []).move Dir3.right
  blank.writeAndMove (instructionHaltVerdict instruction).toΓ
    (TM.idleDir blank.read)

/-- Write the selected instruction's halt verdict in one transition while
preserving input and work tapes. -/
def instructionHaltVerdictTM {n : ℕ} (instruction : Instr) : TM n where
  Q := HaltVerdictPhase
  qstart := .write
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .write =>
        (.done, fun i => TM.readBackWrite (wHeads i),
          instructionHaltVerdict instruction,
          TM.idleDir iHead, fun i => TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state <;> exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Decrementing fixed-program branch tree for the halt verdict. -/
def dispatchHaltTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    Program → TM (n + 1)
  | [] => TM.seqTM (TM.resetBinaryWorkTM tapes.liftedLhs)
      (instructionHaltVerdictTM .halt)
  | instruction :: program =>
      TM.branchWorkBlankTM tapes.liftedLhs
        (instructionHaltVerdictTM instruction)
        (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
          (dispatchHaltTM tapes program))

/-- Copy the canonical PC and emit whether its fixed-program instruction is
`halt`. -/
def programHaltTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM
    (TM.binaryCopyIntoTM tapes.liftedPC tapes.liftedLhs tapes.liftedFound)
    (dispatchHaltTM tapes program)

/-- Branch-tree bound for a selector represented by `selector`. -/
def dispatchHaltTime {n : ℕ} (tapes : ControlInstructionTapes n) :
    Program → ℕ → ℕ
  | [], selector =>
      TM.resetBinaryWorkTime 1 selector.bits.length + 1 + 1
  | _ :: program, selector =>
      TM.branchWorkBlankTime 1
        (TM.binaryPredTime (selector - 1) + 1 +
          dispatchHaltTime tapes program (selector - 1))

/-- Complete fixed-program halt-test bound. -/
def programHaltTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) (pcValue : ℕ) : ℕ :=
  TM.binaryCopyTime pcValue 0 + 1 +
    dispatchHaltTime tapes program pcValue

/-- Repeated pure sparse-snapshot stepping without an explicit halt check.
Because the selected `halt` instruction is a no-op, this agrees with
`Snapshot.run`. -/
def snapshotSteps (program : Program) : ℕ → Snapshot → Snapshot
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => snapshotSteps program fuel (snapshot.step program)

/-- Canonical parked tape containing one Boolean string. -/
def programBinaryTape (bits : List Bool) : Tape :=
  (Tape.init (bits.map Γ.ofBool)).move Dir3.right

/-- Exact clean work-tape image of one sparse RAM snapshot. The store stream,
runtime count, preserved count, and program counter occupy their established
instruction-ABI roles; every other tape is the standard parked blank tape. -/
def programSnapshotWork {n : ℕ} (tapes : ControlInstructionTapes n)
    (snapshot : Snapshot) : Fin (n + 1) → Tape :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.const (Fin (n + 1)) TM.resetBinaryBlank)
          tapes.liftedSource
          (programBinaryTape (snapshot.store.flatMap Entry.encode)))
        tapes.lifted.data.update.remaining
        (programBinaryTape snapshot.store.length.bits))
      tapes.lifted.data.update.resultCount
      (programBinaryTape snapshot.store.length.bits))
    tapes.liftedPC (programBinaryTape snapshot.pc.bits)

/-- Boolean output symbol obtained from the RAM verdict convention. -/
def registerVerdictSymbol (value : ℕ) : Γw :=
  if value = 0 then .zero else .one

/-- Exact output tape emitted from one RAM register value. -/
def registerVerdictOutput (value : ℕ) : Tape :=
  let blank := (Tape.init []).move Dir3.right
  blank.writeAndMove (registerVerdictSymbol value).toΓ
    (TM.idleDir blank.read)

/-- Read a canonical register-value tape and emit zero exactly for value zero,
or one for any nonzero value. -/
def registerVerdictTM {n : ℕ} (idx : Fin n) : TM n where
  Q := HaltVerdictPhase
  qstart := .write
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .write =>
        (.done, fun i => TM.readBackWrite (wHeads i),
          if wHeads idx = Γ.blank then .zero else .one,
          TM.idleDir iHead, fun i => TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state
    · dsimp only
      exact TM.rightOfStart_allIdle iHead wHeads oHead
    · exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Recover register `R₀` through the reusable sparse lookup and emit its
Boolean verdict on the real output tape. -/
def programOutputTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    TM (n + 1) :=
  TM.seqTM (entryLookupStaticTM tapes.lifted.data.lhsLookup 0)
    (registerVerdictTM tapes.liftedLhs)

/-- Complete final-verdict extraction bound. -/
def programOutputTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) : ℕ :=
  entryLookupStaticTime tapes.lifted.data.lhsLookup store 0 + 1 + 1

/-- Fixed halt-aware loop for one concrete RAM program. -/
def programLoopTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.loopTM (programStepTM tapes program) (programHaltTM tapes program)

/-- Bound for one loop body, body/test seams, halt test, and the three-step
rewind/check tail. -/
noncomputable def programLoopIterationTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (snapshot : Snapshot) : ℕ :=
  let next := snapshot.step program
  programStepTime tapes program snapshot.pc snapshot.store + 1 +
    programHaltTime tapes program next.pc + 1 + 3

/-- Sum of the first `fuel` loop-iteration bounds. -/
noncomputable def programLoopTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program) :
    ℕ → Snapshot → ℕ
  | 0, _ => 0
  | fuel + 1, snapshot =>
      programLoopIterationTime tapes program snapshot +
        programLoopTime tapes program fuel (snapshot.step program)

end Machine

end RegisterStore

end RAM

end Complexity
