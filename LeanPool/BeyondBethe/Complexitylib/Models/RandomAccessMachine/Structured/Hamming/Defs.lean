/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Structured RAM Hamming-weight program — definitions

The benchmark uses a small reserved-register ABI: registers `R₀` through `R₄`
hold loop state and input bits start at `R₅`. This avoids the existing raw RAM
input convention's overlap between an unbounded input and fixed scratch registers.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Hamming

/-- Remaining input length and final-result register. -/
def lengthReg : ℕ := 0
/-- Hamming-weight accumulator register. -/
def countReg : ℕ := 1
/-- Address of the next input bit. -/
def pointerReg : ℕ := 2
/-- Constant-one register used for increments and decrements. -/
def oneReg : ℕ := 3
/-- Temporary register receiving the current input bit. -/
def scratchReg : ℕ := 4
/-- First register occupied by input data under the reserved-register ABI. -/
def inputBase : ℕ := 5

/-- Natural-number representation of one input bit. -/
@[simp]
def bitValue (bit : Bool) : ℕ := Input.bitValue bit

/-- Mathematical Hamming weight of a Boolean list. -/
def weight : List Bool → ℕ
  | [] => 0
  | bit :: rest => bitValue bit + weight rest

/-- Reserved-register input layout for the structured benchmark. -/
def inputStore (bits : List Bool) : Store :=
  Input.bitStore lengthReg inputBase bits

/-- Basic instructions that initialize the accumulator, input pointer, and
constant-one register. -/
def setupOps : List Basic :=
  [.imm countReg 0, .imm pointerReg inputBase, .imm oneReg 1]

/-- Initialize the Hamming loop registers. -/
def setup : Cmd := Cmd.basics setupOps

/-- One Hamming-weight loop iteration. -/
def body : Cmd := Cmd.seqList
  [Cmd.basic (.load scratchReg pointerReg),
    Cmd.ifZero scratchReg Cmd.skip (Cmd.basic (.add countReg countReg oneReg)),
    Cmd.basic (.add pointerReg pointerReg oneReg),
    Cmd.basic (.sub lengthReg lengthReg oneReg)]

/-- Process input bits until the remaining-length register reaches zero. -/
def mainLoop : Cmd := Cmd.whileNonzero lengthReg body

/-- Copy the accumulator to the result register `R₀`. -/
def finalize : Cmd := Cmd.seqList
  [Cmd.basic (.imm oneReg 0), Cmd.basic (.add lengthReg countReg oneReg)]

/-- Complete structured Hamming-weight program. -/
def program : Cmd := Cmd.seq setup (.seq mainLoop finalize)

/-- Concrete compiled RAM program for Hamming weight. -/
def compiled : Program := program.compile

/-- Exact number of target RAM transitions needed to reach the compiled halt
instruction. A zero bit uses six loop transitions and a one bit uses eight. -/
def stepCount (bits : List Bool) : ℕ :=
  6 + 6 * bits.length + 2 * weight bits

/-- Explicit logarithmic-cost time budget as a function of input length. The
constant is deliberately simple: the important content is the linear number
of operations, each on values of `O(bitlen n)` bits. -/
def timeBound (inputLength : ℕ) : ℕ :=
  64 * (inputLength + 1) * (bitlen (inputLength + 5) + 1)

/-- Explicit peak-space budget for the reserved-register input representation.
There are at most `inputLength + 5` nonzero registers, and both an occupied
register index and its value have at most `bitlen (inputLength + 5)` bits. -/
def spaceBound (inputLength : ℕ) : ℕ :=
  (inputLength + 5) * (2 * bitlen (inputLength + 5))

/-- A shifted `n · bitlen n` comparison function used to state the benchmark's
quasilinear time and space bounds without hiding small-input behavior. -/
def quasilinearBound (inputLength : ℕ) : ℕ :=
  (inputLength + 5) * (bitlen (inputLength + 5) + 1)

end Hamming

end Structured

end RAM

end Complexity
