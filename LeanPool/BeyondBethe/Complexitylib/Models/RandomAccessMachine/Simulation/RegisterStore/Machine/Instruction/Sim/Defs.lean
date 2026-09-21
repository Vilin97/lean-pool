/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Lift

/-!
# Fixed-program sparse RAM instruction dispatch -- definitions

One fresh last work tape is the next-store buffer. Data instructions redirect
their encoded output there; control instructions copy the unchanged read-only
store there. A binary copy of the program counter is then decremented through a
fixed finite branch tree, so the resulting TM depends only on the RAM program.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace ControlInstructionTapes

/-- Embed every control/data role into the initial `n` tapes of the one-buffer
layout. -/
def lifted {n : ℕ} (tapes : ControlInstructionTapes n) :
  ControlInstructionTapes (n + 1) where
  data :=
    { idx := fun slot => Fin.castSucc (tapes.data.idx slot)
      injective := by
        intro i j h
        apply tapes.data.injective
        exact Fin.castSucc_injective _ h }
  pc := Fin.castSucc tapes.pc
  pc_ne := by
    intro slot h
    exact tapes.pc_ne slot (Fin.castSucc_injective _ h)

/-- Program counter in the one-buffer execution layout. -/
def liftedPC {n : ℕ} (tapes : ControlInstructionTapes n) : Fin (n + 1) :=
  tapes.lifted.pc

/-- First temporary operand in the one-buffer execution layout. -/
def liftedLhs {n : ℕ} (tapes : ControlInstructionTapes n) : Fin (n + 1) :=
  tapes.lifted.data.lhs

/-- Zero scratch used while copying the dispatch selector. -/
def liftedFound {n : ℕ} (tapes : ControlInstructionTapes n) : Fin (n + 1) :=
  tapes.lifted.data.update.found

/-- Read-only encoded-store source in the one-buffer execution layout. -/
def liftedSource {n : ℕ} (tapes : ControlInstructionTapes n) : Fin (n + 1) :=
  tapes.lifted.data.update.entry.source

/-- Fresh last work tape receiving the next encoded store. -/
def buffer {n : ℕ} (_tapes : ControlInstructionTapes n) : Fin (n + 1) :=
  Fin.last n

theorem liftedSource_ne_buffer {n : ℕ}
    (tapes : ControlInstructionTapes n) :
    tapes.liftedSource ≠ tapes.buffer := by
  intro h
  have hval : tapes.data.update.entry.source.val = n := by
    simpa [liftedSource, buffer, lifted] using congrArg Fin.val h
  have hlt := tapes.data.update.entry.source.isLt
  omega

theorem liftedPC_ne_buffer {n : ℕ}
    (tapes : ControlInstructionTapes n) :
    tapes.liftedPC ≠ tapes.buffer := by
  intro h
  have hval : tapes.pc.val = n := by
    simpa [liftedPC, buffer, lifted] using congrArg Fin.val h
  exact Nat.ne_of_lt tapes.pc.isLt hval

/-- The lifted program counter is disjoint from the encoded-store source. -/
theorem liftedPC_ne_source {n : ℕ}
    (tapes : ControlInstructionTapes n) :
    tapes.liftedPC ≠ tapes.liftedSource := by
  exact tapes.lifted.pc_ne 0

theorem liftedData_ne_buffer {n : ℕ}
    (tapes : ControlInstructionTapes n) (slot : Fin 18) :
    tapes.lifted.data.idx slot ≠ tapes.buffer := by
  intro h
  have hval : (tapes.data.idx slot).val = n := by
    simpa [buffer, lifted] using congrArg Fin.val h
  exact Nat.ne_of_lt (tapes.data.idx slot).isLt hval

end ControlInstructionTapes

/-- Emit the unchanged store from the read-only source into the fresh buffer
after executing a control-only instruction. -/
def finishControlInstructionTM {n : ℕ}
    (tapes : ControlInstructionTapes n) (control : TM (n + 1)) : TM (n + 1) :=
  TM.seqTM control
    (TM.copyWorkToWorkTM tapes.liftedSource tapes.buffer)

/-- Execute one statically selected RAM instruction. Every case writes the
next encoded store to the fresh last work tape and leaves real output blank. -/
def executeInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    Instr → TM (n + 1)
  | .imm destination value =>
      TM.seqTM
        (immediateInstructionTM tapes.data destination value).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .add destination source₀ source₁ =>
      TM.seqTM
        (directBinaryInstructionTM tapes.data .add destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .sub destination source₀ source₁ =>
      TM.seqTM
        (directBinaryInstructionTM tapes.data .sub destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .mul destination source₀ source₁ =>
      TM.seqTM
        (directBinaryInstructionTM tapes.data .mul destination source₀
          source₁).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .load destination addressRegister =>
      TM.seqTM
        (indirectLoadInstructionTM tapes.data destination
          addressRegister).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .store addressRegister source =>
      TM.seqTM
        (indirectStoreInstructionTM tapes.data addressRegister
          source).retargetOutput
        (TM.binarySuccTM tapes.liftedPC)
  | .jz source target =>
      finishControlInstructionTM tapes
        (zeroJumpInstructionTM tapes.lifted source target)
  | .jmp target =>
      finishControlInstructionTM tapes (jumpInstructionTM tapes.lifted target)
  | .halt =>
      finishControlInstructionTM tapes (haltInstructionTM (n := n + 1))

/-- Representation-independent finite branch tree for any family of static
instruction executors sharing the standard decrementing selector tape. -/
def dispatchWithTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (execute : Instr → TM (n + 1)) : Program → TM (n + 1)
  | [] => TM.seqTM (TM.resetBinaryWorkTM tapes.liftedLhs) (execute .halt)
  | instruction :: program =>
      TM.branchWorkBlankTM tapes.liftedLhs
        (execute instruction)
        (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
          (dispatchWithTM tapes execute program))

/-- Finite branch tree selected by a decrementing canonical PC copy. -/
def dispatchProgramTM {n : ℕ} (tapes : ControlInstructionTapes n) :
    Program → TM (n + 1)
  | [] => TM.seqTM (TM.resetBinaryWorkTM tapes.liftedLhs)
      (executeInstructionTM tapes .halt)
  | instruction :: program =>
      TM.branchWorkBlankTM tapes.liftedLhs
        (executeInstructionTM tapes instruction)
        (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
          (dispatchProgramTM tapes program))

/-- Pure instruction selected by the same finite branch-tree recursion. -/
def selectedInstruction : Program → ℕ → Instr
  | [], _ => .halt
  | instruction :: _, 0 => instruction
  | _ :: program, selector + 1 => selectedInstruction program selector

/-- Copy the preserved PC into zero scratch and enter the fixed branch tree. -/
def programInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM
    (TM.binaryCopyIntoTM tapes.liftedPC tapes.liftedLhs tapes.liftedFound)
    (dispatchProgramTM tapes program)

/-- Pure next store selected by one RAM instruction. -/
def instructionStore (instruction : Instr) (pcValue : ℕ)
    (store : Store) : Store :=
  (Snapshot.stepInstr instruction { pc := pcValue, store := store }).store

/-- Pure next program counter selected by one RAM instruction. -/
def instructionPC (instruction : Instr) (pcValue : ℕ)
    (store : Store) : ℕ :=
  (Snapshot.stepInstr instruction { pc := pcValue, store := store }).pc

/-- Parent data slots cleared between simulated RAM instructions. -/
def instructionCleanupParentSlot : Fin 5 → Fin 18
  | 0 => 7
  | 1 => 10
  | 2 => 11
  | 3 => 13
  | _ => 14

/-- Five canonical data roles that must be cleared between simulated RAM
instructions: update query, replacement, found flag, and the two operands. -/
def instructionCleanupTape {n : ℕ} (tapes : ControlInstructionTapes n)
    (slot : Fin 5) : Fin (n + 1) :=
  tapes.lifted.data.idx (instructionCleanupParentSlot slot)

theorem instructionCleanupTape_ne_source {n : ℕ}
    (tapes : ControlInstructionTapes n) (slot : Fin 5) :
    instructionCleanupTape tapes slot ≠ tapes.liftedSource := by
  exact tapes.lifted.data.ne (by fin_cases slot <;> decide)

theorem instructionCleanupTape_ne_buffer {n : ℕ}
    (tapes : ControlInstructionTapes n) (slot : Fin 5) :
    instructionCleanupTape tapes slot ≠ tapes.buffer :=
  tapes.liftedData_ne_buffer (instructionCleanupParentSlot slot)

/-- Exact values left on the five cleanup roles by one instruction kernel. -/
def instructionCleanupValue (instruction : Instr) (store : Store) :
    Fin 5 → ℕ
  | 0 =>
      match instruction with
      | .imm destination _ => destination
      | .add destination _ _ => destination
      | .sub destination _ _ => destination
      | .mul destination _ _ => destination
      | .load destination _ => destination
      | .store addressRegister _ => RegisterStore.read store addressRegister
      | .jz _ _ | .jmp _ | .halt => 0
  | 1 =>
      match instruction with
      | .imm _ value => value
      | .add _ source₀ source₁ =>
          RegisterStore.read store source₀ + RegisterStore.read store source₁
      | .sub _ source₀ source₁ =>
          RegisterStore.read store source₀ - RegisterStore.read store source₁
      | .mul _ source₀ source₁ =>
          RegisterStore.read store source₀ * RegisterStore.read store source₁
      | .load _ addressRegister =>
          RegisterStore.read store (RegisterStore.read store addressRegister)
      | .store _ source => RegisterStore.read store source
      | .jz _ _ | .jmp _ | .halt => 0
  | 2 =>
      match instruction with
      | .imm destination _ | .add destination _ _ |
          .sub destination _ _ | .mul destination _ _ |
          .load destination _ =>
          if destination ∈ store.map Prod.fst then 1 else 0
      | .store addressRegister _ =>
          if RegisterStore.read store addressRegister ∈ store.map Prod.fst then
            1
          else 0
      | .jz _ _ | .jmp _ | .halt => 0
  | 3 =>
      match instruction with
      | .add _ source₀ _ | .sub _ source₀ _ | .mul _ source₀ _ =>
          RegisterStore.read store source₀
      | .load _ addressRegister | .store addressRegister _ =>
          RegisterStore.read store addressRegister
      | .imm _ _ | .jz _ _ | .jmp _ | .halt => 0
  | _ =>
      match instruction with
      | .add _ _ source₁ | .sub _ _ source₁ | .mul _ _ source₁ =>
          RegisterStore.read store source₁
      | .store _ source => RegisterStore.read store source
      | .imm _ _ | .load _ _ | .jz _ _ | .jmp _ | .halt => 0

/-- The old-entry counter is exhausted by data updates and untouched by
control instructions. Cleanup resets either canonical value uniformly. -/
def instructionRemainingValue (instruction : Instr) (store : Store) : ℕ :=
  match instruction with
  | .imm _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ |
      .load _ _ | .store _ _ => 0
  | .jz _ _ | .jmp _ | .halt => store.length

/-- Clean one-buffer entry boundary shared by every selected instruction. -/
structure InstructionExecutionReady {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (work : Fin (n + 1) → Tape) : Prop where
  /-- The sparse representation contains one nonzero entry per address. -/
  canonical : Canonical store
  /-- The lifted control/lookup ABI is ready. -/
  control : ControlInstructionReady tapes.lifted store pcValue work
  /-- The read-only source has the complete canonical sparse-store image. -/
  sourceContent : (work tapes.liftedSource).HasBinaryContent
    (store.flatMap Entry.encode)
  /-- The second direct operand starts at zero. -/
  rhs : (work tapes.lifted.data.rhs).HasBinaryNat 0
  /-- Sparse-update replacement starts at zero. -/
  replacement :
    (work tapes.lifted.data.update.replacement).HasBinaryNat 0
  /-- First multiplication alternating scratch starts at zero. -/
  tmp : (work tapes.lifted.data.tmp).HasBinaryNat 0
  /-- Second multiplication alternating scratch starts at zero. -/
  dbl : (work tapes.lifted.data.dbl).HasBinaryNat 0
  /-- The next-store buffer is fresh. -/
  buffer : work tapes.buffer = (Tape.init []).move Dir3.right

/-- Dispatch boundary obtained by replacing the clean zero `lhs` tape by a
canonical decrementing selector. -/
def DispatchReady {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work : Fin (n + 1) → Tape) : Prop :=
  InstructionExecutionReady tapes store pcValue cleanWork ∧
    work = Function.update cleanWork tapes.liftedLhs
      ((Tape.init (selector.bits.map Γ.ofBool)).move Dir3.right)

/-- Common semantic endpoint of every selected instruction before cleanup. -/
structure InstructionExecutionResult {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (work : Fin (n + 1) → Tape) : Prop where
  /-- The fresh buffer contains exactly the pure next sparse store. -/
  buffer : (work tapes.buffer).HasBinaryPrefix
    ((instructionStore instruction pcValue store).flatMap Entry.encode)
  /-- The canonical PC equals the pure instruction successor. -/
  pc : (work tapes.liftedPC).HasBinaryNat
    (instructionPC instruction pcValue store)
  /-- The preserved output-entry count equals the next store cardinality. -/
  resultCount :
    (work tapes.lifted.data.update.resultCount).HasBinaryNat
      (instructionStore instruction pcValue store).length
  /-- The old encoded source remains available for bounded clearing. -/
  sourceContent : (work tapes.liftedSource).HasBinaryContent
    (store.flatMap Entry.encode)
  /-- Every instruction leaves the cleanup roles as canonical binary naturals. -/
  cleanup : ∀ slot, (work (instructionCleanupTape tapes slot)).HasBinaryNat
    (instructionCleanupValue instruction store slot)
  /-- The runtime old-entry counter has a canonical value before reset. -/
  remaining : (work tapes.lifted.data.update.remaining).HasBinaryNat
    (instructionRemainingValue instruction store)
  /-- Decode/match scratch is clean; only the update query remains loaded. -/
  scanner : EntryScanReady tapes.lifted.data.update.entry []
    (instructionCleanupValue instruction store 0).bits work work
  /-- Lookup query-source scratch is restored. -/
  shift : (work tapes.lifted.data.shift).HasBinaryNat 0
  /-- First multiplication scratch is restored. -/
  tmp : (work tapes.lifted.data.tmp).HasBinaryNat 0
  /-- Second multiplication scratch is restored. -/
  dbl : (work tapes.lifted.data.dbl).HasBinaryNat 0
  /-- Every work head is parked at the instruction/cleanup boundary. -/
  parked : ∀ i, TM.Parked (work i)

/-- Instruction-independent buffered endpoint. This is the semantic interface
needed by physical cleanup; sparse and dense register representations provide
their own next-store, next-PC, and scratch-value witnesses. -/
structure BufferedInstructionResult {n : ℕ}
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (nextPC : ℕ) (cleanupValues : Fin 5 → ℕ) (remainingValue : ℕ)
    (work : Fin (n + 1) → Tape) : Prop where
  buffer : (work tapes.buffer).HasBinaryPrefix
    (nextStore.flatMap Entry.encode)
  pc : (work tapes.liftedPC).HasBinaryNat nextPC
  resultCount :
    (work tapes.lifted.data.update.resultCount).HasBinaryNat nextStore.length
  sourceContent : (work tapes.liftedSource).HasBinaryContent
    (oldStore.flatMap Entry.encode)
  cleanup : ∀ slot,
    (work (instructionCleanupTape tapes slot)).HasBinaryNat
      (cleanupValues slot)
  remaining : (work tapes.lifted.data.update.remaining).HasBinaryNat
    remainingValue
  scanner : EntryScanReady tapes.lifted.data.update.entry []
    (cleanupValues 0).bits work work
  shift : (work tapes.lifted.data.shift).HasBinaryNat 0
  tmp : (work tapes.lifted.data.tmp).HasBinaryNat 0
  dbl : (work tapes.lifted.data.dbl).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)

/-- Parent roles reset before the buffered successor store is installed. The
first five are instruction-specific data, followed by the old remaining count
and the old encoded source. -/
def instructionCleanupResetParentSlot : Fin 7 → Fin 18
  | 0 => 7
  | 1 => 10
  | 2 => 11
  | 3 => 13
  | 4 => 14
  | 5 => 9
  | _ => 0

/-- Physical reset target in the one-buffer instruction layout. -/
def instructionCleanupResetTape {n : ℕ}
    (tapes : ControlInstructionTapes n) (slot : Fin 7) : Fin (n + 1) :=
  tapes.lifted.data.idx (instructionCleanupResetParentSlot slot)

theorem instructionCleanupResetTape_injective {n : ℕ}
    (tapes : ControlInstructionTapes n) :
    Function.Injective (instructionCleanupResetTape tapes) := by
  intro i j h
  apply Fin.ext
  have hparent := tapes.lifted.data.injective h
  fin_cases i <;> fin_cases j <;>
    simp [instructionCleanupResetParentSlot] at hparent ⊢

/-- Fixed distinct list consumed by the bulk binary reset. -/
def instructionCleanupResetTargets {n : ℕ}
    (tapes : ControlInstructionTapes n) : List (Fin (n + 1)) :=
  List.ofFn (instructionCleanupResetTape tapes)

/-- Binary contents advertised at each reset target. -/
def instructionCleanupResetBits (instruction : Instr) (store : Store) :
    Fin 7 → List Bool
  | 0 => (instructionCleanupValue instruction store 0).bits
  | 1 => (instructionCleanupValue instruction store 1).bits
  | 2 => (instructionCleanupValue instruction store 2).bits
  | 3 => (instructionCleanupValue instruction store 3).bits
  | 4 => (instructionCleanupValue instruction store 4).bits
  | 5 => (instructionRemainingValue instruction store).bits
  | _ => store.flatMap Entry.encode

/-- Head bounds at the seven bulk-reset targets. Canonical natural tapes are
at cell one; only the scanned old source needs an external bound. -/
def instructionCleanupResetHeadBound (sourceHeadBound : ℕ) : Fin 7 → ℕ
  | 0 | 1 | 2 | 3 | 4 | 5 => 1
  | _ => sourceHeadBound

/-- Extend the indexed reset contents to the whole physical work family. -/
noncomputable def instructionCleanupResetBitsAt {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (store : Store) : Fin (n + 1) → List Bool :=
  Function.extend (instructionCleanupResetTape tapes)
    (instructionCleanupResetBits instruction store) (fun _ => [])

/-- Extend the indexed reset head bounds to the whole work family. -/
noncomputable def instructionCleanupResetHeadBoundAt {n : ℕ}
    (tapes : ControlInstructionTapes n) (sourceHeadBound : ℕ) :
    Fin (n + 1) → ℕ :=
  Function.extend (instructionCleanupResetTape tapes)
    (instructionCleanupResetHeadBound sourceHeadBound) (fun _ => 0)

/-- Binary contents reset by representation-independent buffered cleanup. -/
def bufferedCleanupResetBits (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ) (oldStore : Store) : Fin 7 → List Bool
  | 0 => (cleanupValues 0).bits
  | 1 => (cleanupValues 1).bits
  | 2 => (cleanupValues 2).bits
  | 3 => (cleanupValues 3).bits
  | 4 => (cleanupValues 4).bits
  | 5 => remainingValue.bits
  | _ => oldStore.flatMap Entry.encode

/-- Extend generic buffered-cleanup contents to all physical work tapes. -/
noncomputable def bufferedCleanupResetBitsAt {n : ℕ}
    (tapes : ControlInstructionTapes n) (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ) (oldStore : Store) : Fin (n + 1) → List Bool :=
  Function.extend (instructionCleanupResetTape tapes)
    (bufferedCleanupResetBits cleanupValues remainingValue oldStore)
    (fun _ => [])

/-- Canonical tape with `bits` and its head immediately after the payload. -/
def instructionCleanupPrefixTape (bits : List Bool) : Tape where
  head := bits.length + 1
  cells := (Tape.init (bits.map Γ.ofBool)).cells

/-- Buffered post-state plus the two left markers and old-source cursor bound
needed by the executable cleanup pass. -/
structure InstructionCleanupReady {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (sourceHeadBound : ℕ)
    (work : Fin (n + 1) → Tape) : Prop where
  canonical : Canonical store
  result : InstructionExecutionResult tapes instruction pcValue store work
  sourceStart : (work tapes.liftedSource).cells 0 = Γ.start
  bufferStart : (work tapes.buffer).cells 0 = Γ.start
  sourceHead : (work tapes.liftedSource).head ≤ sourceHeadBound

/-- Representation-independent input boundary for the physical cleanup pass. -/
structure BufferedCleanupReady {n : ℕ}
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (nextPC : ℕ) (cleanupValues : Fin 5 → ℕ) (remainingValue : ℕ)
    (sourceHeadBound : ℕ) (work : Fin (n + 1) → Tape) : Prop where
  nextCanonical : Canonical nextStore
  result : BufferedInstructionResult tapes oldStore nextStore nextPC
    cleanupValues remainingValue work
  sourceStart : (work tapes.liftedSource).cells 0 = Γ.start
  bufferStart : (work tapes.buffer).cells 0 = Γ.start
  sourceHead : (work tapes.liftedSource).head ≤ sourceHeadBound

/-- Restore the clean instruction ABI around the buffered successor store. -/
def instructionCleanupTM {n : ℕ}
    (tapes : ControlInstructionTapes n) : TM (n + 1) :=
  TM.seqTM
    (TM.resetBinaryWorkManyTM (instructionCleanupResetTargets tapes))
    (TM.seqTM (TM.rewindWorkTM tapes.buffer)
      (TM.seqTM
        (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
        (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
          (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
            (TM.binaryCopyIntoTM
              tapes.lifted.data.update.resultCount
              tapes.lifted.data.update.remaining
              tapes.lifted.data.update.found)))))

/-- Exact compositional cleanup bound for one buffered instruction result. -/
noncomputable def instructionCleanupTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (sourceHeadBound : ℕ) : ℕ :=
  let nextStore := instructionStore instruction pcValue store
  let nextBits := nextStore.flatMap Entry.encode
  TM.resetBinaryWorkManyTime
      (instructionCleanupResetBitsAt tapes instruction store)
      (instructionCleanupResetHeadBoundAt tapes sourceHeadBound)
      (instructionCleanupResetTargets tapes) + 1 +
    ((nextBits.length + 1 + 2) + 1 +
      ((nextBits.length + 1) + 1 +
        (TM.resetBinaryWorkTime (nextBits.length + 1) nextBits.length + 1 +
          ((nextBits.length + 1 + 2) + 1 +
            TM.binaryCopyTime nextStore.length 0))))

/-- Exact cleanup budget expressed only through the buffered representation
boundary, independent of the instruction semantics that produced it. -/
noncomputable def bufferedCleanupTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (cleanupValues : Fin 5 → ℕ) (remainingValue sourceHeadBound : ℕ) : ℕ :=
  let nextBits := nextStore.flatMap Entry.encode
  TM.resetBinaryWorkManyTime
      (bufferedCleanupResetBitsAt tapes cleanupValues remainingValue oldStore)
      (instructionCleanupResetHeadBoundAt tapes sourceHeadBound)
      (instructionCleanupResetTargets tapes) + 1 +
    ((nextBits.length + 1 + 2) + 1 +
      ((nextBits.length + 1) + 1 +
        (TM.resetBinaryWorkTime (nextBits.length + 1) nextBits.length + 1 +
          ((nextBits.length + 1 + 2) + 1 +
            TM.binaryCopyTime nextStore.length 0))))

/-- Runtime bound for a statically selected instruction before iteration
cleanup. -/
def executeInstructionTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (instruction : Instr) (pcValue : ℕ) (store : Store) : ℕ :=
  match instruction with
  | .imm destination value =>
      immediateInstructionTime tapes.data store destination value + 1 +
        TM.binarySuccTime pcValue
  | .add destination source₀ source₁ =>
      directBinaryInstructionTime tapes.data .add store destination source₀
        source₁ + 1 + TM.binarySuccTime pcValue
  | .sub destination source₀ source₁ =>
      directBinaryInstructionTime tapes.data .sub store destination source₀
        source₁ + 1 + TM.binarySuccTime pcValue
  | .mul destination source₀ source₁ =>
      directBinaryInstructionTime tapes.data .mul store destination source₀
        source₁ + 1 + TM.binarySuccTime pcValue
  | .load destination addressRegister =>
      indirectLoadInstructionTime tapes.data store destination addressRegister +
        1 + TM.binarySuccTime pcValue
  | .store addressRegister source =>
      indirectStoreInstructionTime tapes.data store addressRegister source + 1 +
        TM.binarySuccTime pcValue
  | .jz source target =>
      zeroJumpInstructionTime tapes.lifted store pcValue source target + 1 +
        (store.flatMap Entry.encode).length + 1
  | .jmp target =>
      jumpInstructionTime pcValue target + 1 +
        (store.flatMap Entry.encode).length + 1
  | .halt =>
      haltInstructionTime + 1 + (store.flatMap Entry.encode).length + 1

/-- Representation-independent path-sensitive branch-tree time. Unlike the
coarse branch combinator bound, this charges only the instruction selected by
the represented selector. -/
def dispatchWithTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (executeTime : Instr → ℕ) : Program → ℕ → ℕ
  | [], selector =>
      TM.resetBinaryWorkTime 1 selector.bits.length + 1 + executeTime .halt
  | instruction :: _, 0 => executeTime instruction + 1
  | _ :: program, selector + 1 =>
      TM.binaryPredTime selector + 1 +
        dispatchWithTime tapes executeTime program selector + 1

/-- Branch-tree bound for a selector currently represented by `selector`. -/
def dispatchProgramTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue : ℕ) : Program → ℕ → ℕ
  | [], selector =>
      TM.resetBinaryWorkTime 1 selector.bits.length + 1 +
        executeInstructionTime tapes .halt pcValue store
  | instruction :: program, selector =>
      TM.branchWorkBlankTime
        (executeInstructionTime tapes instruction pcValue store)
        (TM.binaryPredTime (selector - 1) + 1 +
          dispatchProgramTime tapes store pcValue program (selector - 1))

/-- Complete fixed-program selection and selected-instruction bound. -/
def programInstructionTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) (pcValue : ℕ) (store : Store) : ℕ :=
  TM.binaryCopyTime pcValue 0 + 1 +
    dispatchProgramTime tapes store pcValue program pcValue

/-- Select and execute one RAM instruction, then restore the clean instruction
ABI for the successor snapshot. -/
def programStepTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) : TM (n + 1) :=
  TM.seqTM (programInstructionTM tapes program) (instructionCleanupTM tapes)

/-- Source-head bound available after fixed-program selection and execution. -/
def programStepSourceHeadBound {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (pcValue : ℕ) (store : Store) : ℕ :=
  1 + programInstructionTime tapes program pcValue store

/-- Exact compositional time bound for one selected and cleaned RAM step. -/
noncomputable def programStepTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (pcValue : ℕ) (store : Store) : ℕ :=
  let instruction := selectedInstruction program pcValue
  programInstructionTime tapes program pcValue store + 1 +
    instructionCleanupTime tapes instruction pcValue store
      (programStepSourceHeadBound tapes program pcValue store)

end Machine

end RegisterStore

end RAM

end Complexity
