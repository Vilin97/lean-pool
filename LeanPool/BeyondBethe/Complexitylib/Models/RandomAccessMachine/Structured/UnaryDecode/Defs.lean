/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Encoding.Defs

/-!
# Structured RAM terminated-unary cursor decoder — definitions

This reusable parser consumes the first terminated-unary field of an input bit
array. It is the first nested-control component of the RAM circuit evaluator:
the loop can exit either successfully at a zero terminator or unsuccessfully at
the end of the available array.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace UnaryDecode

/-- Success verdict: one exactly when a zero terminator was consumed. -/
def verdictReg : ℕ := 0
/-- Decoded unary value. -/
def valueReg : ℕ := 1
/-- Address of the next unconsumed input bit. -/
def pointerReg : ℕ := 2
/-- Number of unconsumed input bits. -/
def remainingReg : ℕ := 3
/-- Constant-one register. -/
def oneReg : ℕ := 4
/-- Current input bit. -/
def bitReg : ℕ := 5
/-- Loop activity flag. -/
def activeReg : ℕ := 6
/-- First register occupied by input bits. -/
def inputBase : ℕ := 7

/-- Reserved-register input store for one unary field and its suffix. -/
def inputStore (bits : List Bool) : Store :=
  Input.bitStore remainingReg inputBase bits

/-- Initialize the parser cursor, accumulator, fixedValue, and activity flag. -/
def setupOps : List Basic :=
  [.imm verdictReg 0, .imm valueReg 0, .imm pointerReg inputBase,
    .imm oneReg 1, .imm activeReg 1]

/-- Parser initialization. -/
def setup : Cmd := Cmd.basics setupOps

/-- Record an unterminated field after exhausting the available input. -/
def stopTruncated : Cmd := Cmd.basics [.imm verdictReg 0, .imm activeReg 0]

/-- Record a successfully consumed zero terminator. -/
def stopSuccess : Cmd := Cmd.basics [.imm verdictReg 1, .imm activeReg 0]

/-- Consume one available bit and either stop or increment the unary value. -/
def consume : Cmd := Cmd.seqList
  [.basic (.load bitReg pointerReg),
    .basic (.add pointerReg pointerReg oneReg),
    .basic (.sub remainingReg remainingReg oneReg),
    .ifZero bitReg stopSuccess (.basic (.add valueReg valueReg oneReg))]

/-- One parser iteration, including the exhausted-input case. -/
def body : Cmd := Cmd.ifZero remainingReg stopTruncated consume

/-- Iterate until the parser records success or truncation. -/
def mainLoop : Cmd := Cmd.whileNonzero activeReg body

/-- Semantic calling convention for invoking `mainLoop` at an existing cursor.

The already-consumed prefix is represented by `offset`; `value` is the current
field's unary accumulator, and `remaining` is the still-readable suffix.
Registers at or above `inputBase` are data rather than parser scratch, so the
loop's routine theorem can frame them unchanged. -/
structure CursorReady (inputLength : ℕ) (remaining : List Bool)
    (offset value : ℕ) (store : Store) : Prop where
  /-- Consumed and remaining bits account for the original input. -/
  total_eq : offset + remaining.length = inputLength
  /-- The current field accumulator cannot exceed the absolute cursor offset. -/
  value_le_offset : value ≤ offset
  /-- No successful terminator has been recorded yet. -/
  verdict_eq : store verdictReg = 0
  /-- The accumulator contains the current field's consumed one-bits. -/
  value_eq : store valueReg = value
  /-- The cursor points to the first remaining bit. -/
  pointer_eq : store pointerReg = inputBase + offset
  /-- The remaining-length register agrees with the semantic suffix. -/
  remaining_eq : store remainingReg = remaining.length
  /-- The parser's fixedValue-one register is initialized. -/
  one_eq : store oneReg = 1
  /-- The loop is active. -/
  active_eq : store activeReg = 1
  /-- Physical input registers encode the remaining semantic suffix. -/
  input_eq : ∀ delta,
    store (inputBase + offset + delta) =
      match remaining[delta]? with
      | some bit => Input.bitValue bit
      | none => 0

/-- Exact transition count for invoking `mainLoop` at a semantic suffix. -/
def loopStepCount (remaining : List Bool) : ℕ :=
  match CircuitCode.NatCode.decodePrefix? remaining with
  | none => 10 * remaining.length + 6
  | some (value, _) => 10 * value + 11

/-- Complete terminated-unary decoder. -/
def program : Cmd := Cmd.seq setup mainLoop

/-- Concrete compiled RAM decoder. -/
def compiled : Program := program.compile

/-- Exact compiled transition count through the first terminator or exhaustion. -/
def stepCount (bits : List Bool) : ℕ :=
  match CircuitCode.NatCode.decodePrefix? bits with
  | none => 10 * bits.length + 11
  | some (value, _) => 10 * value + 16

/-- Explicit logarithmic-time budget. -/
def timeBound (inputLength : ℕ) : ℕ :=
  96 * (inputLength + 1) * (bitlen (inputLength + inputBase) + 1)

/-- Explicit peak-space budget. -/
def spaceBound (inputLength : ℕ) : ℕ :=
  (inputLength + inputBase) * (2 * bitlen (inputLength + inputBase))

/-- Shifted quasilinear comparison function. -/
def quasilinearBound (inputLength : ℕ) : ℕ :=
  (inputLength + inputBase) * (bitlen (inputLength + inputBase) + 1)

end UnaryDecode

end Structured

end RAM

end Complexity
