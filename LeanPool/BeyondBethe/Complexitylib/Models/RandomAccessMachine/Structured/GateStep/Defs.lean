/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Defs

/-!
# Structured RAM serialized-gate step — definitions

This program composes the terminated-unary cursor routine with the decoded-gate
kernel. Its input is one canonical gate encoding followed immediately by the
current Boolean wire memo. The fixed three-bit header is consumed directly,
the two references are decoded by two calls to the same loop, and the resulting
gate is evaluated and appended without specializing the program to the input.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStep

/-- The operation header bit is retained in the consumed input prefix. -/
def headerOpReg : ℕ := UnaryDecode.inputBase
/-- The first negation header bit is retained in the consumed input prefix. -/
def headerNegated0Reg : ℕ := UnaryDecode.inputBase + 1
/-- The second negation header bit is retained in the consumed input prefix. -/
def headerNegated1Reg : ℕ := UnaryDecode.inputBase + 2
/-- The first decoded reference is retained in the consumed input prefix. -/
def savedInput0Reg : ℕ := UnaryDecode.inputBase + 3

/-- Canonical gate code followed by its current wire memo. -/
def inputBits (gate : CircuitCode.RawGate) (wires : List Bool) : List Bool :=
  gate.encode ++ wires

/-- First physical register occupied by the wire memo. -/
def memoBase (gate : CircuitCode.RawGate) : ℕ :=
  UnaryDecode.inputBase + gate.encode.length

/-- Machine input for one serialized gate and the current wire memo. -/
def inputStore (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Input.bitStore UnaryDecode.remainingReg UnaryDecode.inputBase
    (inputBits gate wires)

/-- Consume and retain the fixed operation and negation header bits. -/
def headerOps : List Basic :=
  [.load headerOpReg UnaryDecode.pointerReg,
    .add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg,
    .load headerNegated0Reg UnaryDecode.pointerReg,
    .add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg,
    .load headerNegated1Reg UnaryDecode.pointerReg,
    .add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg,
    .sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg]

/-- Save the first reference and restart the cursor accumulator for the second. -/
def saveRestartOps : List Basic :=
  [.add savedInput0Reg UnaryDecode.valueReg UnaryDecode.activeReg,
    .imm UnaryDecode.verdictReg 0,
    .imm UnaryDecode.valueReg 0,
    .imm UnaryDecode.activeReg 1]

/-- Marshal the parsed cursor state into the decoded-gate evaluator ABI. -/
def marshalOps : List Basic :=
  [.add GateEval.wireCountReg UnaryDecode.remainingReg UnaryDecode.activeReg,
    .add GateEval.address1Reg UnaryDecode.valueReg UnaryDecode.activeReg,
    .add GateEval.address0Reg savedInput0Reg UnaryDecode.activeReg,
    .add GateEval.baseReg UnaryDecode.pointerReg UnaryDecode.activeReg,
    .add GateEval.opReg headerOpReg UnaryDecode.activeReg,
    .add GateEval.negated0Reg headerNegated0Reg UnaryDecode.activeReg,
    .add GateEval.negated1Reg headerNegated1Reg UnaryDecode.activeReg]

/-- Parse and evaluate one serialized gate, appending its result to the memo. -/
def program : Cmd := Cmd.seqList
  [UnaryDecode.setup,
    .basics headerOps,
    UnaryDecode.mainLoop,
    .basics saveRestartOps,
    UnaryDecode.mainLoop,
    .basics marshalOps,
    GateEval.program]

/-- Concrete compiled serialized-gate step. -/
def compiled : Program := program.compile

/-- Exact transition count for a canonical serialized gate. -/
def stepCount (gate : CircuitCode.RawGate) : ℕ :=
  10 * (gate.input₀ + gate.input₁) + 67

/-- Uniform envelope including the newly appended wire. -/
def storeBound (gate : CircuitCode.RawGate) (wires : List Bool) : ℕ :=
  (inputBits gate wires).length + UnaryDecode.inputBase + 1

/-- Explicit logarithmic-cost budget for one serialized-gate step. -/
def timeBound (gate : CircuitCode.RawGate) (wires : List Bool) : ℕ :=
  512 * ((inputBits gate wires).length + 1) *
    (bitlen (storeBound gate wires) + 1)

/-- Explicit peak-space budget including the appended memo cell. -/
def spaceBound (gate : CircuitCode.RawGate) (wires : List Bool) : ℕ :=
  storeBound gate wires * (2 * bitlen (storeBound gate wires))

end GateStep

end Structured

end RAM

end Complexity
