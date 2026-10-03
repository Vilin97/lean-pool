/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs

public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Tapes

/-!
# Concrete sparse-store arithmetic instruction kernel

This layer joins the width-efficient arithmetic machines to encoded sparse
update. The destination address and two looked-up operands are supplied on
canonical work tapes; the arithmetic result is written directly to the update
controller's replacement tape, so no value-sized bridge is hidden between the
two phases.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Pure result of the selected arithmetic operation. -/
def BinaryInstrOp.eval : BinaryInstrOp → ℕ → ℕ → ℕ
  | .add, lhs, rhs => lhs + rhs
  | .sub, lhs, rhs => lhs - rhs
  | .mul, lhs, rhs => lhs * rhs

/-- Concrete arithmetic phase selected in finite control. -/
def binaryInstructionArithmeticTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) : BinaryInstrOp → TM n
  | .add => TM.binaryRippleAddTM tapes.lhs tapes.rhs tapes.update.replacement
  | .sub => TM.binaryRippleSubTM tapes.lhs tapes.rhs tapes.update.replacement
  | .mul => TM.binaryShiftMulTM tapes.mul

/-- Uniform endpoint of the selected arithmetic phase. -/
structure BinaryInstructionArithmeticResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (lhs rhs : ℕ) (initialWork finalWork : Fin n → Tape) : Prop where
  /-- First operand is restored canonically. -/
  lhsValue : (finalWork tapes.lhs).HasBinaryNat lhs
  /-- Second operand is restored canonically. -/
  rhsValue : (finalWork tapes.rhs).HasBinaryNat rhs
  /-- The update replacement tape contains the selected result. -/
  result : (finalWork tapes.update.replacement).HasBinaryNat (op.eval lhs rhs)
  /-- Multiplication scratch is reset. -/
  shift : (finalWork tapes.shift).HasBinaryNat 0
  /-- First alternating scratch is reset. -/
  tmp : (finalWork tapes.tmp).HasBinaryNat 0
  /-- Second alternating scratch is reset. -/
  dbl : (finalWork tapes.dbl).HasBinaryNat 0
  /-- Every work head is parked at the phase boundary. -/
  parked : ∀ i, TM.Parked (finalWork i)
  /-- Tapes outside the six arithmetic roles are literally preserved. -/
  frame : ∀ i, i ≠ tapes.lhs → i ≠ tapes.rhs →
    i ≠ tapes.update.replacement → i ≠ tapes.shift →
    i ≠ tapes.tmp → i ≠ tapes.dbl →
    finalWork i = initialWork i

/-- Uniform endpoint of arithmetic followed by encoded sparse update. -/
def BinaryInstructionUpdateResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (address lhs rhs : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ arithmeticWork : Fin n → Tape,
    BinaryInstructionArithmeticResult tapes op lhs rhs
      initialWork arithmeticWork ∧
    EntryUpdateOutcome tapes.update store address (op.eval lhs rhs)
      arithmeticWork finalWork ∧
    (finalWork tapes.update.entry.source).cells =
      (initialWork tapes.update.entry.source).cells

/-- Arithmetic followed immediately by the fixed sparse update controller. -/
def binaryInstructionUpdateTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) : TM n :=
  TM.seqTM (binaryInstructionArithmeticTM tapes op)
    (entryUpdateTM tapes.update)

/-- Load two direct register operands, prepare the direct destination address,
then run arithmetic and sparse update. -/
def directBinaryInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (destination source₀ source₁ : ℕ) : TM n :=
  TM.seqTM (entryLookupStaticTM tapes.lhsLookup source₀)
    (TM.seqTM (entryLookupStaticTM tapes.rhsLookup source₁)
      (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
        (binaryInstructionUpdateTM tapes op)))

/-- Load an address register, perform the loaded indirect read into the update
replacement tape, synthesize the direct destination, and update the store. -/
def indirectLoadInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (destination addressRegister : ℕ) :
    TM n :=
  TM.seqTM (entryLookupStaticTM tapes.lhsLookup addressRegister)
    (TM.seqTM (entryLookupLoadedTM tapes.indirectLoadLookup)
      (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
        (entryUpdateTM tapes.update)))

/-- Synthesize an immediate value and direct destination, then update the
sparse store. -/
def immediateInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (destination value : ℕ) : TM n :=
  TM.seqTM (TM.binaryAddConstTM tapes.update.replacement value)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (entryUpdateTM tapes.update))

/-- Load the indirect destination and direct source, copy both into the update
ABI, and update the sparse store. -/
def indirectStoreInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n)
    (addressRegister source : ℕ) : TM n :=
  TM.seqTM
    (TM.seqTM (entryLookupStaticTM tapes.lhsLookup addressRegister)
      (entryLookupStaticTM tapes.rhsLookup source))
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query
        tapes.update.found)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement
          tapes.update.found)
        (entryUpdateTM tapes.update)))

/-- Replace the canonical binary program counter by a fixed literal. -/
def setProgramCounterTM {n : ℕ} (pc : Fin n) (target : ℕ) : TM n :=
  TM.seqTM (TM.resetBinaryWorkTM pc) (TM.binaryAddConstTM pc target)

/-- Conditional-zero control instruction. The fixed sparse read is cleared
after branching so the reusable lookup ABI is restored at the endpoint. -/
def zeroJumpInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (source target : ℕ) : TM n :=
  TM.seqTM (entryLookupStaticTM tapes.data.lhsLookup source)
    (TM.seqTM
      (TM.branchWorkBlankTM tapes.data.lhs
        (setProgramCounterTM tapes.pc target)
        (TM.binarySuccTM tapes.pc))
      (TM.resetBinaryWorkTM tapes.data.lhs))

/-- Unconditional jump control instruction. -/
def jumpInstructionTM {n : ℕ} (tapes : ControlInstructionTapes n)
    (target : ℕ) : TM n :=
  setProgramCounterTM tapes.pc target

/-- Halt is represented by a one-step exact no-op instruction kernel. The
outer run controller detects halt before beginning another iteration. -/
def haltInstructionTM {n : ℕ} : TM n := TM.skipTM

/-- Canonical entry boundary for a control instruction. -/
structure ControlInstructionReady {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (work : Fin n → Tape) : Prop where
  /-- The fixed sparse-lookup ABI is ready. -/
  lookup : EntryLookupStaticReady tapes.data.lhsLookup store work
  /-- The program counter contains the represented value. -/
  pc : (work tapes.pc).HasBinaryNat pcValue

/-- Semantic endpoint shared by the three control-only instruction forms. -/
structure ControlInstructionResult {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store) (pcValue : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  /-- The clean control ABI is restored with the new program counter. -/
  ready : ControlInstructionReady tapes store pcValue finalWork
  /-- The encoded source cells are read-only. -/
  sourceCells : (finalWork tapes.data.update.entry.source).cells =
    (initialWork tapes.data.update.entry.source).cells
  /-- Every tape outside the lookup ABI and PC assignment is preserved. -/
  frame : ∀ i, i ≠ tapes.pc →
    (∀ slot, i ≠ tapes.data.lhsLookup.idx slot) →
    finalWork i = initialWork i

/-- Runtime for replacing a canonical program counter by a literal. -/
def setProgramCounterTime (pcValue target : ℕ) : ℕ :=
  TM.resetBinaryWorkTime 1 pcValue.bits.length + 1 +
    TM.binaryAddConstTime target 0

/-- Runtime for conditional-zero control, including lookup and operand reset. -/
def zeroJumpInstructionTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue source target : ℕ) : ℕ :=
  entryLookupStaticTime tapes.data.lhsLookup store source + 1 +
    (TM.branchWorkBlankTime (setProgramCounterTime pcValue target)
      (TM.binarySuccTime pcValue) + 1 +
      TM.resetBinaryWorkTime 1
        (RegisterStore.read store source).bits.length)

/-- Runtime for an unconditional jump. -/
def jumpInstructionTime (pcValue target : ℕ) : ℕ :=
  setProgramCounterTime pcValue target

/-- Runtime for the exact halt no-op. -/
def haltInstructionTime : ℕ := 1

/-- Boundary after the two direct source-register lookups. -/
def DirectBinaryOperandsResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (source₀ source₁ : ℕ) (initialWork finalWork : Fin n → Tape) :
    Prop :=
  ∃ lhsWork,
    EntryLookupStaticResult tapes.lhsLookup store source₀
      initialWork lhsWork ∧
    EntryLookupStaticResult tapes.rhsLookup store source₁
      lhsWork finalWork

/-- Boundary after the direct destination literal has been synthesized on the
update query tape. -/
def DirectBinaryAddressResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ operandsWork,
    DirectBinaryOperandsResult tapes store source₀ source₁
      initialWork operandsWork ∧
    finalWork = Function.update operandsWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)

/-- Exact update-controller ABI established by the lookup and address-loading
prefix of a direct arithmetic instruction. -/
structure DirectBinaryUpdateReady {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination source₀ source₁ : ℕ) (work : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.update.entry (store.flatMap Entry.encode)
    destination.bits work work
  lhs : (work tapes.lhs).HasBinaryNat (RegisterStore.read store source₀)
  rhs : (work tapes.rhs).HasBinaryNat (RegisterStore.read store source₁)
  replacement : (work tapes.update.replacement).HasBinaryNat 0
  shift : (work tapes.shift).HasBinaryNat 0
  tmp : (work tapes.tmp).HasBinaryNat 0
  dbl : (work tapes.dbl).HasBinaryNat 0
  remaining : (work tapes.update.remaining).HasBinaryNat store.length
  found : (work tapes.update.found).HasBinaryNat 0
  resultCount : (work tapes.update.resultCount).HasBinaryNat store.length
  parked : ∀ i, TM.Parked (work i)

/-- Semantic endpoint of a complete direct arithmetic instruction. -/
def DirectBinaryInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ updateWork,
    DirectBinaryAddressResult tapes store destination source₀ source₁
      initialWork updateWork ∧
    BinaryInstructionUpdateResult tapes op store destination
      (RegisterStore.read store source₀)
      (RegisterStore.read store source₁) updateWork finalWork

/-- Semantic endpoint of a complete indirect load. -/
def IndirectLoadInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination addressRegister : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ addressWork loadedWork updateWork,
    EntryLookupStaticResult tapes.lhsLookup store addressRegister
      initialWork addressWork ∧
    EntryLookupRestoreResult tapes.indirectLoadLookup store
      (RegisterStore.read store addressRegister) addressWork loadedWork ∧
    updateWork = Function.update loadedWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) ∧
    EntryUpdateOutcome tapes.update store destination
      (RegisterStore.read store (RegisterStore.read store addressRegister))
      updateWork finalWork ∧
    (finalWork tapes.update.entry.source).cells =
      (initialWork tapes.update.entry.source).cells

/-- Semantic endpoint of one immediate assignment. -/
def ImmediateInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value : ℕ) (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ valueWork updateWork,
    valueWork = Function.update initialWork tapes.update.replacement
      ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) ∧
    updateWork = Function.update valueWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) ∧
    EntryUpdateOutcome tapes.update store destination value updateWork finalWork ∧
    (finalWork tapes.update.entry.source).cells =
      (initialWork tapes.update.entry.source).cells

/-- Semantic endpoint of one indirect store. -/
def IndirectStoreInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ operandsWork queryWork updateWork,
    DirectBinaryOperandsResult tapes store addressRegister source initialWork
      operandsWork ∧
    queryWork = Function.update operandsWork tapes.update.entry.query
      ((Tape.init ((RegisterStore.read store addressRegister).bits.map
        Γ.ofBool)).move Dir3.right) ∧
    updateWork = Function.update queryWork tapes.update.replacement
      ((Tape.init ((RegisterStore.read store source).bits.map Γ.ofBool)).move
        Dir3.right) ∧
    EntryUpdateOutcome tapes.update store
      (RegisterStore.read store addressRegister)
      (RegisterStore.read store source) updateWork finalWork ∧
    (finalWork tapes.update.entry.source).cells =
      (initialWork tapes.update.entry.source).cells

/-- Operation-specific arithmetic budget. -/
def binaryInstructionArithmeticTime (op : BinaryInstrOp) (lhs rhs : ℕ) : ℕ :=
  match op with
  | .add => TM.binaryRippleAddTime lhs rhs
  | .sub => TM.binaryRippleSubTime lhs rhs
  | .mul => TM.binaryShiftMulTime lhs rhs

/-- Complete arithmetic-plus-update budget, including the composition seam. -/
def binaryInstructionUpdateTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (address lhs rhs : ℕ) : ℕ :=
  binaryInstructionArithmeticTime op lhs rhs + 1 +
    entryUpdateTime tapes.update store address (op.eval lhs rhs)

/-- Complete direct arithmetic-instruction budget. -/
def directBinaryInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ : ℕ) : ℕ :=
  entryLookupStaticTime tapes.lhsLookup store source₀ + 1 +
    (entryLookupStaticTime tapes.rhsLookup store source₁ + 1 +
      (TM.binaryAddConstTime destination 0 + 1 +
        binaryInstructionUpdateTime tapes op store destination
          (RegisterStore.read store source₀)
          (RegisterStore.read store source₁)))

/-- Complete indirect-load instruction budget. -/
def indirectLoadInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination addressRegister : ℕ) : ℕ :=
  entryLookupStaticTime tapes.lhsLookup store addressRegister + 1 +
    (entryLookupLoadedTime tapes.indirectLoadLookup store
      (RegisterStore.read store addressRegister) + 1 +
      (TM.binaryAddConstTime destination 0 + 1 +
        entryUpdateTime tapes.update store destination
          (RegisterStore.read store
            (RegisterStore.read store addressRegister))))

/-- Complete immediate-assignment instruction budget. -/
def immediateInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value : ℕ) : ℕ :=
  TM.binaryAddConstTime value 0 + 1 +
    (TM.binaryAddConstTime destination 0 + 1 +
      entryUpdateTime tapes.update store destination value)

/-- Complete indirect-store instruction budget. -/
def indirectStoreInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ) : ℕ :=
  (entryLookupStaticTime tapes.lhsLookup store addressRegister + 1 +
      entryLookupStaticTime tapes.rhsLookup store source) + 1 +
    (TM.binaryCopyTime (RegisterStore.read store addressRegister) 0 + 1 +
      (TM.binaryCopyTime (RegisterStore.read store source) 0 + 1 +
        entryUpdateTime tapes.update store
          (RegisterStore.read store addressRegister)
          (RegisterStore.read store source)))

end Machine

end RegisterStore

end RAM

end Complexity
