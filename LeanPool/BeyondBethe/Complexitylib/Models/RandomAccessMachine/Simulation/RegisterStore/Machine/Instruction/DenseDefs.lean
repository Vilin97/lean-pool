/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.TaggedDefs

/-!
# Dense-overlay RAM instruction kernels -- definitions

These kernels retain the checked sparse scanner/update ABI while interpreting
the immutable public input in place. Reads use the dense-overlay lookup and
writes successor-tag their actual value before sparse update.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Arithmetic followed by positive tagging and sparse overlay update. -/
def denseBinaryInstructionUpdateTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) : TM n :=
  TM.seqTM (binaryInstructionArithmeticTM tapes op)
    (taggedEntryUpdateTM tapes.update)

/-- Two direct dense-overlay reads, arithmetic, and a tagged destination write. -/
def denseDirectBinaryInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (destination source₀ source₁ : ℕ) : TM n :=
  TM.seqTM
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup source₀)
      (denseOverlayLookupStaticTM tapes.rhsLookup source₁))
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (denseBinaryInstructionUpdateTM tapes op))

/-- Dense-overlay indirect read followed by a tagged direct destination write. -/
def denseIndirectLoadInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n)
    (destination addressRegister : ℕ) : TM n :=
  TM.seqTM
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
      (denseOverlayLookupTM tapes.indirectLoadLookup))
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (taggedEntryUpdateTM tapes.update))

/-- Immediate assignment with its value converted to a positive overlay tag. -/
def denseImmediateInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n) (destination value : ℕ) : TM n :=
  TM.seqTM (TM.binaryAddConstTM tapes.update.replacement value)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (taggedEntryUpdateTM tapes.update))

/-- Dense-overlay indirect destination/source reads followed by a tagged write. -/
def denseIndirectStoreInstructionTM {n : ℕ}
    (tapes : BinaryInstructionTapes n)
    (addressRegister source : ℕ) : TM n :=
  TM.seqTM
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
      (denseOverlayLookupStaticTM tapes.rhsLookup source))
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query
        tapes.update.found)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement
          tapes.update.found)
        (taggedEntryUpdateTM tapes.update)))

/-- Conditional jump whose tested register is read through the dense overlay. -/
def denseZeroJumpInstructionTM {n : ℕ}
    (tapes : ControlInstructionTapes n) (source target : ℕ) : TM n :=
  TM.seqTM (denseOverlayLookupStaticTM tapes.data.lhsLookup source)
    (TM.seqTM
      (TM.branchWorkBlankTM tapes.data.lhs
        (setProgramCounterTM tapes.pc target)
        (TM.binarySuccTM tapes.pc))
      (TM.resetBinaryWorkTM tapes.data.lhs))

/-- Semantic endpoint of arithmetic and one tagged overlay update. -/
def DenseBinaryInstructionUpdateResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (overlay : Store) (address lhs rhs : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ arithmeticWork : Fin n → Tape,
    BinaryInstructionArithmeticResult tapes op lhs rhs
      initialWork arithmeticWork ∧
    TaggedEntryUpdateResult tapes.update overlay address (op.eval lhs rhs)
      arithmeticWork finalWork

/-- Boundary after two fixed-address dense-overlay reads. -/
def DenseDirectBinaryOperandsResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ lhsWork,
    DenseOverlayLookupStaticResult tapes.lhsLookup input overlay source₀
      initialWork lhsWork ∧
    DenseOverlayLookupStaticResult tapes.rhsLookup input overlay source₁
      lhsWork finalWork

/-- Boundary after dense operands and direct destination synthesis. -/
def DenseDirectBinaryAddressResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ operandsWork,
    DenseDirectBinaryOperandsResult tapes input overlay source₀ source₁
      initialWork operandsWork ∧
    finalWork = Function.update operandsWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)

/-- Semantic endpoint of a complete dense direct arithmetic instruction. -/
def DenseDirectBinaryInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (input : List Bool) (overlay : Store)
    (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ updateWork,
    DenseDirectBinaryAddressResult tapes input overlay destination source₀
      source₁ initialWork updateWork ∧
    DenseBinaryInstructionUpdateResult tapes op overlay destination
      (DenseOverlay.read input overlay source₀)
      (DenseOverlay.read input overlay source₁) updateWork finalWork

/-- Semantic endpoint of one dense immediate assignment. -/
def DenseImmediateInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (overlay : Store)
    (destination value : ℕ) (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ valueWork updateWork,
    valueWork = Function.update initialWork tapes.update.replacement
      ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) ∧
    updateWork = Function.update valueWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) ∧
    TaggedEntryUpdateResult tapes.update overlay destination value updateWork
      finalWork

/-- Semantic endpoint of a complete dense indirect load. -/
def DenseIndirectLoadInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (destination addressRegister : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ addressWork loadedWork updateWork,
    DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
      addressRegister initialWork addressWork ∧
    DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
      (DenseOverlay.read input overlay addressRegister) addressWork loadedWork ∧
    updateWork = Function.update loadedWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) ∧
    TaggedEntryUpdateResult tapes.update overlay destination
      (DenseOverlay.read input overlay
        (DenseOverlay.read input overlay addressRegister))
      updateWork finalWork

/-- Semantic endpoint of a complete dense indirect store. -/
def DenseIndirectStoreInstructionResult {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ operandsWork queryWork updateWork,
    DenseDirectBinaryOperandsResult tapes input overlay addressRegister source
      initialWork operandsWork ∧
    queryWork = Function.update operandsWork tapes.update.entry.query
      ((Tape.init ((DenseOverlay.read input overlay addressRegister).bits.map
        Γ.ofBool)).move Dir3.right) ∧
    updateWork = Function.update queryWork tapes.update.replacement
      ((Tape.init ((DenseOverlay.read input overlay source).bits.map Γ.ofBool)).move
        Dir3.right) ∧
    TaggedEntryUpdateResult tapes.update overlay
      (DenseOverlay.read input overlay addressRegister)
      (DenseOverlay.read input overlay source) updateWork finalWork

/-- Runtime of arithmetic followed by positive tagging and overlay update. -/
def denseBinaryInstructionUpdateTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (overlay : Store) (address lhs rhs : ℕ) : ℕ :=
  binaryInstructionArithmeticTime op lhs rhs + 1 +
    taggedEntryUpdateTime tapes.update overlay address (op.eval lhs rhs)

/-- Complete direct dense arithmetic-instruction budget. -/
def denseDirectBinaryInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (input : List Bool) (overlay : Store)
    (destination source₀ source₁ : ℕ) : ℕ :=
  (denseOverlayLookupStaticTime tapes.lhsLookup input.length overlay source₀ + 1 +
      denseOverlayLookupStaticTime tapes.rhsLookup input.length overlay source₁) + 1 +
    (TM.binaryAddConstTime destination 0 + 1 +
      denseBinaryInstructionUpdateTime tapes op overlay destination
        (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁))

/-- Complete immediate dense assignment budget. -/
def denseImmediateInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (overlay : Store)
    (destination value : ℕ) : ℕ :=
  TM.binaryAddConstTime value 0 + 1 +
    (TM.binaryAddConstTime destination 0 + 1 +
      taggedEntryUpdateTime tapes.update overlay destination value)

/-- Complete dense indirect-load instruction budget. -/
def denseIndirectLoadInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (destination addressRegister : ℕ) : ℕ :=
  (denseOverlayLookupStaticTime tapes.lhsLookup input.length overlay
      addressRegister + 1 +
      denseOverlayLookupTime tapes.indirectLoadLookup input.length overlay
        (DenseOverlay.read input overlay addressRegister)) + 1 +
    (TM.binaryAddConstTime destination 0 + 1 +
      taggedEntryUpdateTime tapes.update overlay destination
        (DenseOverlay.read input overlay
          (DenseOverlay.read input overlay addressRegister)))

/-- Complete dense indirect-store instruction budget. -/
def denseIndirectStoreInstructionTime {n : ℕ}
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ) : ℕ :=
  (denseOverlayLookupStaticTime tapes.lhsLookup input.length overlay
      addressRegister + 1 +
      denseOverlayLookupStaticTime tapes.rhsLookup input.length overlay source) + 1 +
    (TM.binaryCopyTime (DenseOverlay.read input overlay addressRegister) 0 + 1 +
      (TM.binaryCopyTime (DenseOverlay.read input overlay source) 0 + 1 +
        taggedEntryUpdateTime tapes.update overlay
          (DenseOverlay.read input overlay addressRegister)
          (DenseOverlay.read input overlay source)))

/-- Runtime for a conditional jump using one dense-overlay register read. -/
def denseZeroJumpInstructionTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue source target : ℕ) : ℕ :=
  denseOverlayLookupStaticTime tapes.data.lhsLookup input.length overlay source + 1 +
    (TM.branchWorkBlankTime (setProgramCounterTime pcValue target)
      (TM.binarySuccTime pcValue) + 1 +
      TM.resetBinaryWorkTime 1
        (DenseOverlay.read input overlay source).bits.length)

end Machine
end RegisterStore
end RAM
end Complexity
