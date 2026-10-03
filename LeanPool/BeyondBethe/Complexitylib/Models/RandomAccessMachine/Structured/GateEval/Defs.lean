/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Encoding.Defs

/-!
# Structured RAM decoded-gate evaluator — definitions

This kernel evaluates one already-decoded fan-in-two gate against a mutable
wire memo. It uses indirect reads for both references and an indirect write to
append the result. Boolean negation, AND, and OR are implemented arithmetically,
so the instruction count is independent of the gate and wire values.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateEval

/-- Encoded gate-operation bit: zero for AND and one for OR. -/
def opReg : ℕ := 0
/-- Negation bit for the first gate input. -/
def negated0Reg : ℕ := 1
/-- Negation bit for the second gate input. -/
def negated1Reg : ℕ := 2
/-- First gate-input index, then its physical memo address. -/
def address0Reg : ℕ := 3
/-- Second gate-input index, then the append address. -/
def address1Reg : ℕ := 4
/-- Number of wire values already present in the memo. -/
def wireCountReg : ℕ := 5
/-- Loaded and optionally negated first input value. -/
def value0Reg : ℕ := 6
/-- Loaded and optionally negated second input value. -/
def value1Reg : ℕ := 7
/-- Final gate value. -/
def outputReg : ℕ := 8
/-- Arithmetic scratch register. -/
def scratchReg : ℕ := 9
/-- Physical base address of the wire memo. -/
def baseReg : ℕ := 10
/-- First register occupied by memoized wire bits. -/
def wireBase : ℕ := 11

/-- Register representation of a decoded gate and its incoming wire memo. -/
def inputStore (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  let store := Input.bitStore wireCountReg wireBase wires
  let store := Function.update store opReg (Input.bitValue gate.opBit)
  let store := Function.update store negated0Reg (Input.bitValue gate.negated₀)
  let store := Function.update store negated1Reg (Input.bitValue gate.negated₁)
  let store := Function.update store address0Reg gate.input₀
  let store := Function.update store address1Reg gate.input₁
  Function.update store baseReg wireBase

/-- Branch-free arithmetic implementation of Boolean XOR. -/
def xorOps (value negated : ℕ) : List Basic :=
  [.add outputReg value negated,
    .mul scratchReg value negated,
    .add scratchReg scratchReg scratchReg,
    .sub value outputReg scratchReg]

/-- Convert the two absolute wire indices to physical memo addresses. -/
def addressOps : List Basic :=
  [.add address0Reg address0Reg baseReg,
    .add address1Reg address1Reg baseReg]

/-- Indirectly read the gate's two inputs. -/
def loadOps : List Basic :=
  [.load value0Reg address0Reg,
    .load value1Reg address1Reg]

/-- Branch-free AND/OR selection. Both candidate values are formed and the
operation bit arithmetically selects the result. -/
def evalOps : List Basic :=
  [.mul scratchReg value0Reg value1Reg,
    .add outputReg value0Reg value1Reg,
    .sub outputReg outputReg scratchReg,
    .sub address0Reg outputReg scratchReg,
    .mul address0Reg opReg address0Reg,
    .sub outputReg outputReg address0Reg]

/-- Compute the next memo address and append the result indirectly. -/
def appendOps : List Basic :=
  [.add address1Reg baseReg wireCountReg,
    .store address1Reg outputReg]

/-- Evaluate one gate and append its Boolean result to the wire memo. -/
def ops : List Basic :=
  addressOps ++ loadOps ++ xorOps value0Reg negated0Reg ++
    xorOps value1Reg negated1Reg ++ evalOps ++ appendOps

/-- Straight-line decoded-gate evaluator, grouped at semantic proof boundaries. -/
def program : Cmd := Cmd.seqList
  [.basics addressOps,
    .basics loadOps,
    .basics (xorOps value0Reg negated0Reg),
    .basics (xorOps value1Reg negated1Reg),
    .basics evalOps,
    .basics appendOps]

/-- Semantic calling convention for evaluating a decoded gate in an existing
store. The memo may begin at any address above the evaluator's control prefix. -/
structure ReadyAt (base : ℕ) (gate : CircuitCode.RawGate) (wires : List Bool)
    (store : Store) : Prop where
  /-- The memo is disjoint from the evaluator's control registers. -/
  base_ge : wireBase ≤ base
  /-- The operation register contains the canonical gate-operation bit. -/
  op_eq : store opReg = Input.bitValue gate.opBit
  /-- The first negation register contains its canonical bit. -/
  negated0_eq : store negated0Reg = Input.bitValue gate.negated₀
  /-- The second negation register contains its canonical bit. -/
  negated1_eq : store negated1Reg = Input.bitValue gate.negated₁
  /-- The first address register contains the first absolute wire reference. -/
  address0_eq : store address0Reg = gate.input₀
  /-- The second address register contains the second absolute wire reference. -/
  address1_eq : store address1Reg = gate.input₁
  /-- The wire-count register contains the current memo length. -/
  wireCount_eq : store wireCountReg = wires.length
  /-- The base register points to the physical memo. -/
  base_eq : store baseReg = base
  /-- Physical memo cells contain the semantic wire bits. -/
  wire_eq : ∀ index, index < wires.length →
    store (base + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0

/-- Concrete compiled RAM kernel. -/
def compiled : Program := program.compile

/-- The branch-free kernel always takes twenty source and compiled steps. -/
def stepCount : ℕ := 20

/-- Uniform logarithmic-cost budget for one gate. -/
def timeBound (wireCount : ℕ) : ℕ :=
  80 * (bitlen (wireCount + wireBase + 1) + 1)

/-- Peak-space budget including the appended wire. -/
def spaceBound (wireCount : ℕ) : ℕ :=
  (wireCount + wireBase + 1) *
    (2 * bitlen (wireCount + wireBase + 1))

/-- Shifted logarithmic comparison function for one-gate time. -/
def logarithmicBound (wireCount : ℕ) : ℕ :=
  bitlen (wireCount + wireBase + 1) + 1

/-- Shifted quasilinear comparison function for the explicit memo space. -/
def quasilinearBound (wireCount : ℕ) : ℕ :=
  (wireCount + wireBase + 1) *
    (bitlen (wireCount + wireBase + 1) + 1)

end GateEval

end Structured

end RAM

end Complexity
