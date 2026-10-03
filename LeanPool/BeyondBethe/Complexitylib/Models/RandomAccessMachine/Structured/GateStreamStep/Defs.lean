/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Defs

/-!
# Structured RAM iterable serialized-gate step — definitions

Unlike the compact `GateStep` benchmark, this routine keeps the code cursor and
mutable wire memo physically separate. Registers `7` and `8` carry the memo base
and current wire count while the parser consumes a gate from a higher code
region. Two fixed continuation cells lie between the evaluator's control prefix
and the memo, so cursor state survives gate evaluation without aliasing either
mutable wires or unread code.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStreamStep

/-- Physical base of the mutable wire memo. -/
def memoBaseReg : ℕ := 7
/-- Number of semantic entries currently in the wire memo. -/
def wireCountMetaReg : ℕ := 8
/-- Address of the current gate's first header bit. -/
def gateStartReg : ℕ := 9
/-- First decoded reference retained across the second unary decode. -/
def savedInput0Reg : ℕ := 10
/-- Fixed spill cell for the next code pointer. -/
def spillPointerReg : ℕ := 11
/-- Fixed spill cell for the unread-code count. -/
def spillRemainingReg : ℕ := 12

/-- Initialize parser scratch and remember the current gate start. -/
def setupOps : List Basic :=
  [.imm UnaryDecode.verdictReg 0,
    .imm UnaryDecode.valueReg 0,
    .imm UnaryDecode.oneReg 1,
    .imm UnaryDecode.activeReg 1,
    .imm gateStartReg 0,
    .add gateStartReg UnaryDecode.pointerReg gateStartReg]

/-- Consume the fixed three-bit gate header without copying it. The header is
loaded from its saved code address only after both references are decoded. -/
def headerOps : List Basic :=
  [.add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg,
    .add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg,
    .add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg]

/-- Save the first reference and restart the unary accumulator. -/
def saveRestartOps : List Basic :=
  [.add savedInput0Reg UnaryDecode.valueReg UnaryDecode.activeReg,
    .imm UnaryDecode.verdictReg 0,
    .imm UnaryDecode.valueReg 0,
    .imm UnaryDecode.activeReg 1]

/-- Spill the continuation cursor, load the saved header, and marshal the gate
and independent memo metadata into `GateEval`'s calling convention. -/
def marshalOps : List Basic :=
  [.add GateEval.wireCountReg wireCountMetaReg UnaryDecode.activeReg,
    .imm wireCountMetaReg spillPointerReg,
    .store wireCountMetaReg UnaryDecode.pointerReg,
    .imm wireCountMetaReg spillRemainingReg,
    .store wireCountMetaReg UnaryDecode.remainingReg,
    .add GateEval.address1Reg UnaryDecode.valueReg UnaryDecode.activeReg,
    .add GateEval.address0Reg savedInput0Reg UnaryDecode.activeReg,
    .add GateEval.baseReg memoBaseReg UnaryDecode.activeReg,
    .imm wireCountMetaReg 1,
    .load GateEval.opReg gateStartReg,
    .add gateStartReg gateStartReg wireCountMetaReg,
    .load GateEval.negated0Reg gateStartReg,
    .add gateStartReg gateStartReg wireCountMetaReg,
    .load GateEval.negated1Reg gateStartReg]

/-- Recover the next code cursor and rebuild persistent memo metadata after the
gate kernel has appended its result. -/
def restoreOps : List Basic :=
  [.imm UnaryDecode.activeReg 0,
    .add memoBaseReg GateEval.baseReg UnaryDecode.activeReg,
    .imm wireCountMetaReg 1,
    .imm UnaryDecode.activeReg spillPointerReg,
    .load UnaryDecode.pointerReg UnaryDecode.activeReg,
    .imm UnaryDecode.activeReg spillRemainingReg,
    .load UnaryDecode.remainingReg UnaryDecode.activeReg,
    .add wireCountMetaReg GateEval.wireCountReg wireCountMetaReg]

/-- Parse and evaluate one gate while retaining an independent code cursor and
memo base for the next call. -/
def routine : Cmd := Cmd.seqList
  [.basics setupOps,
    .basics headerOps,
    UnaryDecode.mainLoop,
    .basics saveRestartOps,
    UnaryDecode.mainLoop,
    .basics marshalOps,
    GateEval.program,
    .basics restoreOps]

/-- Concrete compiled iterable gate routine. -/
def compiled : Program := routine.compile

/-- Exact transition count on one canonical gate. -/
def stepCount (gate : CircuitCode.RawGate) : ℕ :=
  10 * (gate.input₀ + gate.input₁) + 80

/-- Serialized bits beginning at the current gate and continuing with unread
code. -/
def codeBits (gate : CircuitCode.RawGate) (tail : List Bool) : List Bool :=
  gate.encode ++ tail

/-- Absolute address immediately after all code visible to this invocation. -/
def codeEnd (gateStart : ℕ) (gate : CircuitCode.RawGate)
    (tail : List Bool) : ℕ :=
  gateStart + (codeBits gate tail).length

/-- Unary-decoder input length corresponding to the absolute code region. -/
def cursorLength (gateStart : ℕ) (gate : CircuitCode.RawGate)
    (tail : List Bool) : ℕ :=
  gateStart - UnaryDecode.inputBase + (codeBits gate tail).length

/-- Calling convention at the beginning of an iterable gate invocation. -/
structure Ready (gateStart base : ℕ) (gate : CircuitCode.RawGate)
    (tail : List Bool) (wires : List Bool) (store : Store) : Prop where
  /-- The memo lies strictly above the fixed continuation cells. -/
  base_ge : spillRemainingReg < base
  /-- The append cell lies strictly before the current gate. -/
  memo_before_code : base + wires.length < gateStart
  /-- The parser cursor points at the current gate header. -/
  pointer_eq : store UnaryDecode.pointerReg = gateStart
  /-- The parser sees the complete current gate followed by unread code. -/
  remaining_eq : store UnaryDecode.remainingReg = (codeBits gate tail).length
  /-- Persistent physical memo base. -/
  memoBase_eq : store memoBaseReg = base
  /-- Persistent semantic memo length. -/
  wireCount_eq : store wireCountMetaReg = wires.length
  /-- Current gate and unread tail are encoded at the cursor. -/
  code_eq : ∀ delta,
    store (gateStart + delta) =
      match (codeBits gate tail)[delta]? with
      | some bit => Input.bitValue bit
      | none => 0
  /-- Existing memo contents. -/
  wire_eq : ∀ index,
    store (base + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0

/-- Calling convention immediately before `marshalOps`, after both references
have been decoded successfully. -/
structure Parsed (gateStart nextPointer remaining base : ℕ)
    (gate : CircuitCode.RawGate) (wires : List Bool) (store : Store) : Prop where
  /-- The memo lies strictly above the fixed continuation cells. -/
  base_ge : spillRemainingReg < base
  /-- The append cell lies strictly before unread gate code. -/
  memo_before_code : base + wires.length < gateStart
  /-- The second unary decoder recorded success. -/
  verdict_eq : store UnaryDecode.verdictReg = 1
  /-- The second decoded reference remains in the accumulator. -/
  value_eq : store UnaryDecode.valueReg = gate.input₁
  /-- The next unread code address. -/
  pointer_eq : store UnaryDecode.pointerReg = nextPointer
  /-- Number of unread code bits. -/
  remaining_eq : store UnaryDecode.remainingReg = remaining
  /-- The second unary loop is inactive. -/
  active_eq : store UnaryDecode.activeReg = 0
  /-- Persistent physical memo base. -/
  memoBase_eq : store memoBaseReg = base
  /-- Persistent semantic memo length. -/
  wireCount_eq : store wireCountMetaReg = wires.length
  /-- Saved address of the current gate header. -/
  gateStart_eq : store gateStartReg = gateStart
  /-- Retained first decoded reference. -/
  input0_eq : store savedInput0Reg = gate.input₀
  /-- Operation header bit at the saved gate address. -/
  op_eq : store gateStart = Input.bitValue gate.opBit
  /-- First-negation header bit. -/
  negated0_eq : store (gateStart + 1) = Input.bitValue gate.negated₀
  /-- Second-negation header bit. -/
  negated1_eq : store (gateStart + 2) = Input.bitValue gate.negated₁
  /-- Existing memo contents. -/
  wire_eq : ∀ index,
    store (base + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0

end GateStreamStep

end Structured

end RAM

end Complexity
