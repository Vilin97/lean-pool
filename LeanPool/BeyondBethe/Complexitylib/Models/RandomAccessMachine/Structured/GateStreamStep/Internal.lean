/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Encoding.Internal.Codec
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStreamStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Internal
public import Mathlib.Tactic.IntervalCases

/-!
# Structured RAM iterable serialized-gate step — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStreamStep

open Internal

private def marshalStore (store : Store) : Store :=
  Basic.execList marshalOps store

private def marshalPrefix (store : Store) : Store :=
  Basic.execList
    [.add GateEval.wireCountReg wireCountMetaReg UnaryDecode.activeReg,
      .imm wireCountMetaReg spillPointerReg,
      .store wireCountMetaReg UnaryDecode.pointerReg,
      .imm wireCountMetaReg spillRemainingReg,
      .store wireCountMetaReg UnaryDecode.remainingReg,
      .add GateEval.address1Reg UnaryDecode.valueReg UnaryDecode.activeReg,
      .add GateEval.address0Reg savedInput0Reg UnaryDecode.activeReg,
      .add GateEval.baseReg memoBaseReg UnaryDecode.activeReg,
      .imm wireCountMetaReg 1]
    store

private def loadedOp (store : Store) : Store :=
  (Basic.load GateEval.opReg gateStartReg).exec (marshalPrefix store)

private def advanced0 (store : Store) : Store :=
  (Basic.add gateStartReg gateStartReg wireCountMetaReg).exec (loadedOp store)

private def loadedNegated0 (store : Store) : Store :=
  (Basic.load GateEval.negated0Reg gateStartReg).exec (advanced0 store)

private def advanced1 (store : Store) : Store :=
  (Basic.add gateStartReg gateStartReg wireCountMetaReg).exec
    (loadedNegated0 store)

private def loadedNegated1 (store : Store) : Store :=
  (Basic.load GateEval.negated1Reg gateStartReg).exec (advanced1 store)

private theorem marshalStore_eq (store : Store) :
    marshalStore store = loadedNegated1 store := by rfl

private theorem marshalPrefix_high (store : Store) (index : ℕ)
    (hindex : spillRemainingReg < index) :
    marshalPrefix store index = store index := by
  simp only [spillRemainingReg] at hindex
  simp (disch := omega) [marshalPrefix, Basic.execList, Basic.exec,
    Function.update_of_ne, GateEval.address0Reg, GateEval.address1Reg,
    GateEval.wireCountReg, GateEval.baseReg, memoBaseReg, wireCountMetaReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg]

private theorem marshal_high (store : Store) (index : ℕ)
    (hindex : spillRemainingReg < index) :
    marshalStore store index = store index := by
  simp only [spillRemainingReg] at hindex
  have h0 : index ≠ GateEval.opReg := by
    simp only [GateEval.opReg]
    omega
  have h1 : index ≠ GateEval.negated0Reg := by
    simp only [GateEval.negated0Reg]
    omega
  have h2 : index ≠ GateEval.negated1Reg := by
    simp only [GateEval.negated1Reg]
    omega
  have h3 : index ≠ GateEval.address0Reg := by
    simp only [GateEval.address0Reg]
    omega
  have h4 : index ≠ GateEval.address1Reg := by
    simp only [GateEval.address1Reg]
    omega
  have h5 : index ≠ GateEval.wireCountReg := by
    simp only [GateEval.wireCountReg]
    omega
  have h8 : index ≠ wireCountMetaReg := by
    simp only [wireCountMetaReg]
    omega
  have h9 : index ≠ gateStartReg := by
    simp only [gateStartReg]
    omega
  have h10 : index ≠ GateEval.baseReg := by
    simp only [GateEval.baseReg]
    omega
  have h11 : index ≠ spillPointerReg := by
    simp only [spillPointerReg]
    omega
  have h12 : index ≠ spillRemainingReg := by
    simp only [spillRemainingReg]
    omega
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    Function.update_of_ne, h0, h1, h2, h3, h4, h5, h8, h9, h10, h11,
    h12]

private theorem marshal_wireCount {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.wireCountReg = wires.length := by
  have hcount : store 8 = wires.length := by
    simpa [wireCountMetaReg] using h.wireCount_eq
  have hactive : store 6 = 0 := by
    simpa [UnaryDecode.activeReg] using h.active_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.activeReg, hcount, hactive]

private theorem marshal_address1 {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.address1Reg = gate.input₁ := by
  have hvalue : store 1 = gate.input₁ := by
    simpa [UnaryDecode.valueReg] using h.value_eq
  have hactive : store 6 = 0 := by
    simpa [UnaryDecode.activeReg] using h.active_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.valueReg, UnaryDecode.activeReg, hvalue, hactive]

private theorem marshal_address0 {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.address0Reg = gate.input₀ := by
  have hinput0 : store 10 = gate.input₀ := by
    simpa [savedInput0Reg] using h.input0_eq
  have hactive : store 6 = 0 := by
    simpa [UnaryDecode.activeReg] using h.active_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.activeReg, hinput0, hactive]

private theorem marshal_base {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.baseReg = base := by
  have hbase : store 7 = base := by
    simpa [memoBaseReg] using h.memoBase_eq
  have hactive : store 6 = 0 := by
    simpa [UnaryDecode.activeReg] using h.active_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.activeReg, hbase, hactive]

private theorem marshal_spillPointer
    {gateStart nextPointer remaining base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store spillPointerReg = nextPointer := by
  have hpointer : store 2 = nextPointer := by
    simpa [UnaryDecode.pointerReg] using h.pointer_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.pointerReg, hpointer]

private theorem marshal_spillRemaining
    {gateStart nextPointer remaining base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store spillRemainingReg = remaining := by
  have hremaining : store 3 = remaining := by
    simpa [UnaryDecode.remainingReg] using h.remaining_eq
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, memoBaseReg, wireCountMetaReg, gateStartReg,
    savedInput0Reg, spillPointerReg, spillRemainingReg,
    UnaryDecode.remainingReg, hremaining]

private theorem marshal_op {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.opReg = Input.bitValue gate.opBit := by
  have hlarge : spillRemainingReg < gateStart := by
    have hbase := h.base_ge
    have hcode := h.memo_before_code
    omega
  have hprefixStart : marshalPrefix store gateStartReg = gateStart := by
    simpa [marshalPrefix, Basic.execList, Basic.exec, Function.update_of_ne,
      GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
      GateEval.baseReg, gateStartReg, wireCountMetaReg, spillPointerReg,
      spillRemainingReg] using h.gateStart_eq
  have hprefixHeader : marshalPrefix store gateStart =
      Input.bitValue gate.opBit := by
    rw [marshalPrefix_high store gateStart hlarge, h.op_eq]
  have hloaded : loadedOp store GateEval.opReg =
      Input.bitValue gate.opBit := by
    simp [loadedOp, Basic.exec, hprefixStart, hprefixHeader]
  rw [marshalStore_eq]
  simpa [loadedNegated1, advanced1, loadedNegated0, advanced0, Basic.exec,
    Function.update_of_ne, GateEval.opReg, GateEval.negated0Reg,
    GateEval.negated1Reg, gateStartReg] using hloaded

private theorem marshal_negated0 {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.negated0Reg =
      Input.bitValue gate.negated₀ := by
  have hlarge : spillRemainingReg < gateStart + 1 := by
    have hbase := h.base_ge
    have hcode := h.memo_before_code
    omega
  have hprefixStart : marshalPrefix store gateStartReg = gateStart := by
    simpa [marshalPrefix, Basic.execList, Basic.exec, Function.update_of_ne,
      GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
      GateEval.baseReg, gateStartReg, wireCountMetaReg, spillPointerReg,
      spillRemainingReg] using h.gateStart_eq
  have hprefixOne : marshalPrefix store wireCountMetaReg = 1 := by
    simp [marshalPrefix, Basic.execList, Basic.exec, wireCountMetaReg]
  have hprefixStart' : marshalPrefix store 9 = gateStart := by
    simpa [gateStartReg] using hprefixStart
  have hprefixOne' : marshalPrefix store 8 = 1 := by
    simpa [wireCountMetaReg] using hprefixOne
  have hloadedStart : loadedOp store gateStartReg = gateStart := by
    simpa [loadedOp, Basic.exec, Function.update_of_ne, GateEval.opReg,
      gateStartReg] using hprefixStart'
  have hloadedOne : loadedOp store wireCountMetaReg = 1 := by
    simpa [loadedOp, Basic.exec, Function.update_of_ne, GateEval.opReg,
      wireCountMetaReg] using hprefixOne'
  have hadvancedStart : advanced0 store gateStartReg = gateStart + 1 := by
    change loadedOp store gateStartReg + loadedOp store wireCountMetaReg = _
    rw [hloadedStart, hloadedOne]
  have hprefixHeader : marshalPrefix store (gateStart + 1) =
      Input.bitValue gate.negated₀ := by
    rw [marshalPrefix_high store (gateStart + 1) hlarge, h.negated0_eq]
  have hloadedHeader : loadedOp store (gateStart + 1) =
      Input.bitValue gate.negated₀ := by
    rw [show loadedOp store (gateStart + 1) =
        marshalPrefix store (gateStart + 1) by
      simp [loadedOp, Basic.exec, Function.update_of_ne, GateEval.opReg]]
    exact hprefixHeader
  have hadvancedHeader : advanced0 store (gateStart + 1) =
      Input.bitValue gate.negated₀ := by
    rw [advanced0, Basic.exec, Function.update_of_ne]
    · exact hloadedHeader
    · simp only [gateStartReg, spillRemainingReg] at hlarge ⊢
      omega
  have hloaded : loadedNegated0 store GateEval.negated0Reg =
      Input.bitValue gate.negated₀ := by
    simp [loadedNegated0, Basic.exec, hadvancedStart, hadvancedHeader]
  rw [marshalStore_eq]
  simpa [loadedNegated1, advanced1, Basic.exec, Function.update_of_ne,
    GateEval.negated0Reg, GateEval.negated1Reg, gateStartReg] using hloaded

private theorem marshal_negated1 {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (h : Parsed gateStart nextPointer remaining base gate wires store) :
    marshalStore store GateEval.negated1Reg =
      Input.bitValue gate.negated₁ := by
  have hlarge : spillRemainingReg < gateStart + 2 := by
    have hbase := h.base_ge
    have hcode := h.memo_before_code
    omega
  have hprefixStart : marshalPrefix store gateStartReg = gateStart := by
    simpa [marshalPrefix, Basic.execList, Basic.exec, Function.update_of_ne,
      GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
      GateEval.baseReg, gateStartReg, wireCountMetaReg, spillPointerReg,
      spillRemainingReg] using h.gateStart_eq
  have hprefixOne : marshalPrefix store wireCountMetaReg = 1 := by
    simp [marshalPrefix, Basic.execList, Basic.exec, wireCountMetaReg]
  have hprefixStart' : marshalPrefix store 9 = gateStart := by
    simpa [gateStartReg] using hprefixStart
  have hprefixOne' : marshalPrefix store 8 = 1 := by
    simpa [wireCountMetaReg] using hprefixOne
  have hloadedStart : loadedOp store gateStartReg = gateStart := by
    simpa [loadedOp, Basic.exec, Function.update_of_ne, GateEval.opReg,
      gateStartReg] using hprefixStart'
  have hloadedOne : loadedOp store wireCountMetaReg = 1 := by
    simpa [loadedOp, Basic.exec, Function.update_of_ne, GateEval.opReg,
      wireCountMetaReg] using hprefixOne'
  have hadvanced0Start : advanced0 store gateStartReg = gateStart + 1 := by
    change loadedOp store gateStartReg + loadedOp store wireCountMetaReg = _
    rw [hloadedStart, hloadedOne]
  have hloaded0Start : loadedNegated0 store gateStartReg = gateStart + 1 := by
    simpa [loadedNegated0, Basic.exec, Function.update_of_ne,
      GateEval.negated0Reg, gateStartReg] using hadvanced0Start
  have hloaded0One : loadedNegated0 store wireCountMetaReg = 1 := by
    have hadvancedOne : advanced0 store wireCountMetaReg = 1 := by
      simpa [advanced0, Basic.exec, Function.update_of_ne, gateStartReg,
        wireCountMetaReg] using hloadedOne
    simpa [loadedNegated0, Basic.exec, Function.update_of_ne,
      GateEval.negated0Reg, wireCountMetaReg] using hadvancedOne
  have hadvanced1Start : advanced1 store gateStartReg = gateStart + 2 := by
    change loadedNegated0 store gateStartReg +
      loadedNegated0 store wireCountMetaReg = _
    rw [hloaded0Start, hloaded0One]
  have hprefixHeader : marshalPrefix store (gateStart + 2) =
      Input.bitValue gate.negated₁ := by
    rw [marshalPrefix_high store (gateStart + 2) hlarge, h.negated1_eq]
  have hadvancedHeader : advanced1 store (gateStart + 2) =
      Input.bitValue gate.negated₁ := by
    rw [advanced1, Basic.exec, Function.update_of_ne]
    · rw [loadedNegated0, Basic.exec, Function.update_of_ne]
      · rw [advanced0, Basic.exec, Function.update_of_ne]
        · rw [loadedOp, Basic.exec, Function.update_of_ne]
          · exact hprefixHeader
          · simp only [GateEval.opReg, spillRemainingReg] at hlarge ⊢
            omega
        · simp only [gateStartReg, spillRemainingReg] at hlarge ⊢
          omega
      · simp only [GateEval.negated0Reg, spillRemainingReg] at hlarge ⊢
        omega
    · simp only [gateStartReg, spillRemainingReg] at hlarge ⊢
      omega
  rw [marshalStore_eq]
  simp [loadedNegated1, Basic.exec, hadvanced1Start, hadvancedHeader]

theorem marshal_ready_internal {gateStart nextPointer remaining base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (hparsed : Parsed gateStart nextPointer remaining base gate wires store) :
    GateEval.ReadyAt base gate wires (Basic.execList marshalOps store) ∧
      Basic.execList marshalOps store spillPointerReg = nextPointer ∧
      Basic.execList marshalOps store spillRemainingReg = remaining := by
  change GateEval.ReadyAt base gate wires (marshalStore store) ∧
    marshalStore store spillPointerReg = nextPointer ∧
    marshalStore store spillRemainingReg = remaining
  refine ⟨?_, marshal_spillPointer hparsed, marshal_spillRemaining hparsed⟩
  constructor
  · have hbase := hparsed.base_ge
    simp only [GateEval.wireBase, spillRemainingReg] at hbase ⊢
    omega
  · exact marshal_op hparsed
  · exact marshal_negated0 hparsed
  · exact marshal_negated1 hparsed
  · exact marshal_address0 hparsed
  · exact marshal_address1 hparsed
  · exact marshal_wireCount hparsed
  · exact marshal_base hparsed
  · intro index hindex
    rw [marshal_high store (base + index)]
    · exact hparsed.wire_eq index
    · have hbase := hparsed.base_ge
      omega

private def setupStore (store : Store) : Store :=
  Basic.execList setupOps store

private def headerStore (store : Store) : Store :=
  Basic.execList headerOps (setupStore store)

private def saveRestartStore (store : Store) : Store :=
  Basic.execList saveRestartOps store

private def restoreStore (store : Store) : Store :=
  Basic.execList restoreOps store

private def firstRemaining (gate : CircuitCode.RawGate)
    (tail : List Bool) : List Bool :=
  CircuitCode.NatCode.encode gate.input₀ ++
    CircuitCode.NatCode.encode gate.input₁ ++ tail

private def secondRemaining (gate : CircuitCode.RawGate)
    (tail : List Bool) : List Bool :=
  CircuitCode.NatCode.encode gate.input₁ ++ tail

private def firstOffset (gateStart : ℕ) : ℕ :=
  gateStart - UnaryDecode.inputBase + 3

private def secondOffset (gateStart : ℕ)
    (gate : CircuitCode.RawGate) : ℕ :=
  gateStart - UnaryDecode.inputBase + 4 + gate.input₀

private theorem setup_high (store : Store) (index : ℕ) (hindex : 10 < index) :
    setupStore store index = store index := by
  simp (disch := omega) [setupStore, setupOps, Basic.execList, Basic.exec,
    Function.update_of_ne, gateStartReg, UnaryDecode.verdictReg,
    UnaryDecode.valueReg, UnaryDecode.pointerReg, UnaryDecode.oneReg,
    UnaryDecode.activeReg]

private theorem header_high (store : Store) (index : ℕ) (hindex : 10 < index) :
    headerStore store index = store index := by
  rw [headerStore]
  have hsetup := setup_high store index hindex
  simpa (disch := omega) [headerOps, Basic.execList, Basic.exec,
    Function.update_of_ne, UnaryDecode.pointerReg,
    UnaryDecode.remainingReg] using hsetup

private theorem first_ready {gateStart base : ℕ} {gate : CircuitCode.RawGate}
    {tail : List Bool} {wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store) :
    UnaryDecode.CursorReady (cursorLength gateStart gate tail)
      (firstRemaining gate tail) (firstOffset gateStart) 0
      (headerStore store) := by
  have hstart : UnaryDecode.inputBase ≤ gateStart := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [UnaryDecode.inputBase, spillRemainingReg] at hbase ⊢
    omega
  constructor
  · simp [cursorLength, firstOffset, firstRemaining, codeBits,
      CircuitCode.RawGate.encode]
    omega
  · omega
  · simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.verdictReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.valueReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, gateStartReg]
  · simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.valueReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.verdictReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, gateStartReg]
  · have hp : store 2 = gateStart := by
      simpa [UnaryDecode.pointerReg] using hready.pointer_eq
    simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.pointerReg, UnaryDecode.remainingReg,
      UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, gateStartReg, hp, firstOffset]
    omega
  · have hr : store 3 =
        (codeBits gate tail).length := hready.remaining_eq
    simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.pointerReg, UnaryDecode.remainingReg,
      UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, gateStartReg, hr, firstRemaining, codeBits,
      CircuitCode.RawGate.encode]
  · simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.oneReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.activeReg, gateStartReg]
  · simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
      Basic.exec, UnaryDecode.activeReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.oneReg, gateStartReg]
  · intro delta
    have haddress : UnaryDecode.inputBase + firstOffset gateStart + delta =
        gateStart + (3 + delta) := by
      simp [firstOffset]
      omega
    rw [haddress, header_high store]
    · rw [hready.code_eq (3 + delta)]
      rw [show 3 + delta = Nat.succ (Nat.succ (Nat.succ delta)) by omega]
      simp [codeBits, firstRemaining, CircuitCode.RawGate.encode]
      rfl
    · have hbase := hready.base_ge
      have hcode := hready.memo_before_code
      simp only [spillRemainingReg] at hbase
      omega

private theorem header_bound {gateStart base : ℕ}
    {gate : CircuitCode.RawGate} {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store)
    (hbound : Internal.StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) store) :
    Internal.StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) (headerStore store) := by
  have hlarge : 10 < codeEnd gateStart gate tail := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg] at hbase
    simp [codeEnd, codeBits, CircuitCode.RawGate.length_encode]
    omega
  have hheaderEnd : gateStart + 3 ≤ codeEnd gateStart gate tail := by
    simp [codeEnd, codeBits, CircuitCode.RawGate.length_encode]
    omega
  have hcodeLength : (codeBits gate tail).length ≤
      codeEnd gateStart gate tail := by
    simp [codeEnd]
  have hserialized : 5 + gate.input₀ + gate.input₁ + tail.length ≤
      codeEnd gateStart gate tail := by
    simpa [codeBits, CircuitCode.RawGate.length_encode, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hcodeLength
  have hp : store 2 = gateStart := by
    simpa [UnaryDecode.pointerReg] using hready.pointer_eq
  have hr : store 3 = (codeBits gate tail).length := by
    simpa [UnaryDecode.remainingReg] using hready.remaining_eq
  constructor
  · intro index hnonzero
    by_cases hindex : index ≤ 10
    · omega
    · rw [header_high store index (by omega)] at hnonzero
      exact hbound.index_lt index hnonzero
  · intro index
    by_cases hindex : index ≤ 10
    · interval_cases index <;>
        simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
          Basic.exec, UnaryDecode.verdictReg, UnaryDecode.valueReg,
          UnaryDecode.pointerReg, UnaryDecode.remainingReg,
          UnaryDecode.oneReg, UnaryDecode.activeReg, gateStartReg, hp, hr,
          codeBits]
      all_goals try omega
      all_goals exact hbound.value_le _
    · rw [header_high store index (by omega)]
      exact hbound.value_le index

private theorem saveRestart_high (store : Store) (index : ℕ)
    (hindex : 10 < index) :
    saveRestartStore store index = store index := by
  simp (disch := omega) [saveRestartStore, saveRestartOps, Basic.execList,
    Basic.exec, Function.update_of_ne, savedInput0Reg,
    UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.activeReg]

private theorem saveRestart_apply_of_ne (store : Store) (index : ℕ)
    (hsaved : index ≠ savedInput0Reg)
    (hverdict : index ≠ UnaryDecode.verdictReg)
    (hvalue : index ≠ UnaryDecode.valueReg)
    (hactive : index ≠ UnaryDecode.activeReg) :
    saveRestartStore store index = store index := by
  simp [saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
    Function.update_of_ne, hsaved, hverdict, hvalue, hactive]

private theorem saveRestart_bound {bound : ℕ} {store : Store}
    (hbound : Internal.StoreEnvelope bound bound store)
    (hlarge : 10 < bound) (hactive : store UnaryDecode.activeReg = 0) :
    Internal.StoreEnvelope bound bound (saveRestartStore store) := by
  let saved0 := (Basic.add savedInput0Reg UnaryDecode.valueReg
    UnaryDecode.activeReg).exec store
  have h0 : Internal.StoreEnvelope bound bound saved0 := by
    apply hbound.execBasic
    · simpa [Basic.writeIndex, savedInput0Reg] using hlarge
    · change store UnaryDecode.valueReg + store UnaryDecode.activeReg ≤ bound
      rw [hactive, Nat.add_zero]
      exact hbound.value_le UnaryDecode.valueReg
  have h1 := h0.execBasic (.imm UnaryDecode.verdictReg 0)
    (by simp [Basic.writeIndex, UnaryDecode.verdictReg]; omega)
    (by simp [Basic.writeValue])
  have h2 := h1.execBasic (.imm UnaryDecode.valueReg 0)
    (by simp [Basic.writeIndex, UnaryDecode.valueReg]; omega)
    (by simp [Basic.writeValue])
  have h3 := h2.execBasic (.imm UnaryDecode.activeReg 1)
    (by simp [Basic.writeIndex, UnaryDecode.activeReg]; omega)
    (by simp [Basic.writeValue]; omega)
  simpa [saveRestartStore, saveRestartOps, Basic.execList, saved0] using h3

private theorem header_op {gateStart base : ℕ} {gate : CircuitCode.RawGate}
    {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store) :
    headerStore store gateStart = Input.bitValue gate.opBit := by
  have hlarge : 10 < gateStart := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg] at hbase
    omega
  rw [header_high store gateStart hlarge]
  have hcode := hready.code_eq 0
  simpa [codeBits, CircuitCode.RawGate.encode] using hcode

private theorem header_negated0 {gateStart base : ℕ}
    {gate : CircuitCode.RawGate} {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store) :
    headerStore store (gateStart + 1) =
      Input.bitValue gate.negated₀ := by
  have hlarge : 10 < gateStart + 1 := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg] at hbase
    omega
  rw [header_high store (gateStart + 1) hlarge, hready.code_eq 1]
  simp [codeBits, CircuitCode.RawGate.encode]

private theorem header_negated1 {gateStart base : ℕ}
    {gate : CircuitCode.RawGate} {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store) :
    headerStore store (gateStart + 2) =
      Input.bitValue gate.negated₁ := by
  have hlarge : 10 < gateStart + 2 := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg] at hbase
    omega
  rw [header_high store (gateStart + 2) hlarge, hready.code_eq 2]
  simp [codeBits, CircuitCode.RawGate.encode]

private theorem decoders_internal {gateStart base : ℕ} {gate : CircuitCode.RawGate}
    {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store)
    (hbound : StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) store) :
    ∃ first saved second firstCost firstSpace secondCost secondSpace,
      Exec UnaryDecode.mainLoop (headerStore store) first
        (UnaryDecode.loopStepCount (firstRemaining gate tail))
        firstCost firstSpace ∧
      saved = saveRestartStore first ∧
      Exec UnaryDecode.mainLoop saved second
        (UnaryDecode.loopStepCount (secondRemaining gate tail))
        secondCost secondSpace ∧
      Parsed gateStart (gateStart + gate.encode.length) tail.length base
        gate wires second ∧
      (∀ delta, second (gateStart + gate.encode.length + delta) =
        match tail[delta]? with
        | some bit => Input.bitValue bit
        | none => 0) ∧
      StoreEnvelope (codeEnd gateStart gate tail)
        (codeEnd gateStart gate tail) second := by
  have hstart : UnaryDecode.inputBase ≤ gateStart := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg, UnaryDecode.inputBase] at hbase ⊢
    omega
  have hcursorEnd : cursorLength gateStart gate tail +
      UnaryDecode.inputBase = codeEnd gateStart gate tail := by
    simp [cursorLength, codeEnd]
    omega
  have hheaderBound : StoreEnvelope (cursorLength gateStart gate tail +
      UnaryDecode.inputBase) (cursorLength gateStart gate tail +
      UnaryDecode.inputBase) (headerStore store) := by
    rw [hcursorEnd]
    exact header_bound hready hbound
  have hfirstReady := first_ready hready
  obtain ⟨first, firstCost, firstSpace, hfirst, _hfirstCost, _hfirstSpace,
      hfirstResult, hfirstActive, hfirstOne, hfirstFrame, hfirstBound⟩ :=
    UnaryDecode.mainLoop_measured_internal hfirstReady hheaderBound
  have hdecode0 : CircuitCode.NatCode.decodePrefix?
      (firstRemaining gate tail) =
      some (gate.input₀, secondRemaining gate tail) := by
    simp [firstRemaining, secondRemaining]
  rw [hdecode0] at hfirstResult
  simp only at hfirstResult
  have hfirstValue : first UnaryDecode.valueReg = gate.input₀ :=
    by simpa using hfirstResult.2.1
  have hfirstPointer : first UnaryDecode.pointerReg =
      gateStart + 4 + gate.input₀ := by
    have hp := hfirstResult.2.2.1
    rw [hp]
    simp [firstOffset]
    omega
  have hfirstRemaining : first UnaryDecode.remainingReg =
      (secondRemaining gate tail).length := hfirstResult.2.2.2
  let saved := saveRestartStore first
  have hlarge : 10 < codeEnd gateStart gate tail := by
    have hbase := hready.base_ge
    have hcode := hready.memo_before_code
    simp only [spillRemainingReg] at hbase
    simp [codeEnd]
    omega
  have hsavedBound : StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) saved := by
    apply saveRestart_bound
    · simpa [hcursorEnd] using hfirstBound
    · exact hlarge
    · exact hfirstActive
  have hsecondReady : UnaryDecode.CursorReady
      (cursorLength gateStart gate tail) (secondRemaining gate tail)
      (secondOffset gateStart gate) 0 saved := by
    constructor
    · simp [cursorLength, secondOffset, secondRemaining, codeBits,
        CircuitCode.RawGate.length_encode]
      omega
    · omega
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList,
        Basic.exec, UnaryDecode.verdictReg, UnaryDecode.valueReg,
        UnaryDecode.activeReg]
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList,
        Basic.exec, UnaryDecode.verdictReg, UnaryDecode.valueReg,
        UnaryDecode.activeReg]
    · change saved UnaryDecode.pointerReg = _
      rw [show saved UnaryDecode.pointerReg =
          first UnaryDecode.pointerReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg,
            UnaryDecode.valueReg, UnaryDecode.pointerReg,
            UnaryDecode.activeReg]]
      rw [hfirstPointer]
      simp [secondOffset]
      omega
    · change saved UnaryDecode.remainingReg =
        (secondRemaining gate tail).length
      rw [show saved UnaryDecode.remainingReg =
          first UnaryDecode.remainingReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg,
            UnaryDecode.valueReg, UnaryDecode.remainingReg,
            UnaryDecode.activeReg]]
      exact hfirstRemaining
    · change saved UnaryDecode.oneReg = 1
      rw [show saved UnaryDecode.oneReg = first UnaryDecode.oneReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg,
            UnaryDecode.valueReg, UnaryDecode.oneReg,
            UnaryDecode.activeReg]]
      exact hfirstOne
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList,
        Basic.exec, UnaryDecode.verdictReg, UnaryDecode.valueReg,
        UnaryDecode.activeReg]
    · intro delta
      have haddress : UnaryDecode.inputBase + secondOffset gateStart gate +
          delta = UnaryDecode.inputBase + firstOffset gateStart +
            (gate.input₀ + 1 + delta) := by
        simp [secondOffset, firstOffset]
        omega
      rw [haddress]
      rw [show saved (UnaryDecode.inputBase + firstOffset gateStart +
            (gate.input₀ + 1 + delta)) =
          first (UnaryDecode.inputBase + firstOffset gateStart +
            (gate.input₀ + 1 + delta)) by
        apply saveRestart_high
        simp [firstOffset, UnaryDecode.inputBase]
        omega]
      rw [hfirstFrame _ (by simp [UnaryDecode.inputBase]; omega)]
      have hinput := hfirstReady.input_eq (gate.input₀ + 1 + delta)
      have hlookup : (firstRemaining gate tail)[gate.input₀ + 1 + delta]? =
          (secondRemaining gate tail)[delta]? := by
        rw [show firstRemaining gate tail =
            CircuitCode.NatCode.encode gate.input₀ ++
              secondRemaining gate tail by
          simp [firstRemaining, secondRemaining, List.append_assoc]]
        rw [List.getElem?_append_right (by simp)]
        simp
      rw [hlookup] at hinput
      exact hinput
  have hsavedCursorBound : StoreEnvelope
      (cursorLength gateStart gate tail + UnaryDecode.inputBase)
      (cursorLength gateStart gate tail + UnaryDecode.inputBase) saved := by
    rw [hcursorEnd]
    exact hsavedBound
  obtain ⟨second, secondCost, secondSpace, hsecond, _hsecondCost,
      _hsecondSpace, hsecondResult, hsecondActive, _hsecondOne,
      hsecondFrame, hsecondBound⟩ :=
    UnaryDecode.mainLoop_measured_internal hsecondReady hsavedCursorBound
  have hdecode1 : CircuitCode.NatCode.decodePrefix?
      (secondRemaining gate tail) = some (gate.input₁, tail) := by
    simp [secondRemaining]
  rw [hdecode1] at hsecondResult
  simp only at hsecondResult
  have hsecondValue : second UnaryDecode.valueReg = gate.input₁ :=
    by simpa using hsecondResult.2.1
  have hsecondPointer : second UnaryDecode.pointerReg =
      gateStart + gate.encode.length := by
    have hp := hsecondResult.2.2.1
    rw [hp]
    simp [secondOffset, CircuitCode.RawGate.length_encode]
    omega
  have hsecondRemaining : second UnaryDecode.remainingReg = tail.length :=
    hsecondResult.2.2.2
  have hpreserved (index : ℕ) (hindex : 10 < index) :
      second index = store index := by
    rw [hsecondFrame index (by
      simp only [UnaryDecode.inputBase]
      omega)]
    change saveRestartStore first index = store index
    rw [saveRestart_high first index hindex]
    rw [hfirstFrame index (by
      simp only [UnaryDecode.inputBase]
      omega)]
    exact header_high store index hindex
  have hmeta (index : ℕ) (h7 : UnaryDecode.inputBase ≤ index)
      (hsaved : index ≠ savedInput0Reg) :
      second index = headerStore store index := by
    rw [hsecondFrame index h7]
    change saveRestartStore first index = headerStore store index
    rw [saveRestart_apply_of_ne]
    · exact hfirstFrame index h7
    · exact hsaved
    · simp only [UnaryDecode.inputBase] at h7
      simp only [UnaryDecode.verdictReg]
      omega
    · simp only [UnaryDecode.inputBase] at h7
      simp only [UnaryDecode.valueReg]
      omega
    · simp only [UnaryDecode.inputBase] at h7
      simp only [UnaryDecode.activeReg]
      omega
  have hinput0 : second savedInput0Reg = gate.input₀ := by
    rw [hsecondFrame _ (by simp [savedInput0Reg, UnaryDecode.inputBase])]
    change saveRestartStore first savedInput0Reg = gate.input₀
    have hvalue : first 1 = gate.input₀ := by
      simpa [UnaryDecode.valueReg] using hfirstValue
    have hactive : first 6 = 0 := by
      simpa [UnaryDecode.activeReg] using hfirstActive
    simp [saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
      savedInput0Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.activeReg, hvalue, hactive]
  have hparsed : Parsed gateStart (gateStart + gate.encode.length)
      tail.length base gate wires second := by
    constructor
    · exact hready.base_ge
    · exact hready.memo_before_code
    · exact hsecondResult.1
    · exact hsecondValue
    · exact hsecondPointer
    · exact hsecondRemaining
    · exact hsecondActive
    · rw [hmeta memoBaseReg]
      · simpa [headerStore, headerOps, setupStore, setupOps, Basic.execList,
          Basic.exec, memoBaseReg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.pointerReg,
          UnaryDecode.remainingReg, UnaryDecode.oneReg,
          UnaryDecode.activeReg, gateStartReg] using hready.memoBase_eq
      · simp [memoBaseReg, UnaryDecode.inputBase]
      · simp [memoBaseReg, savedInput0Reg]
    · rw [hmeta wireCountMetaReg]
      · simpa [headerStore, headerOps, setupStore, setupOps, Basic.execList,
          Basic.exec, wireCountMetaReg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.pointerReg,
          UnaryDecode.remainingReg, UnaryDecode.oneReg,
          UnaryDecode.activeReg, gateStartReg] using hready.wireCount_eq
      · simp [wireCountMetaReg, UnaryDecode.inputBase]
      · simp [wireCountMetaReg, savedInput0Reg]
    · rw [hmeta gateStartReg]
      · simp [headerStore, headerOps, setupStore, setupOps, Basic.execList,
          Basic.exec, gateStartReg, UnaryDecode.pointerReg,
          UnaryDecode.remainingReg]
        exact hready.pointer_eq
      · simp [gateStartReg, UnaryDecode.inputBase]
      · simp [gateStartReg, savedInput0Reg]
    · exact hinput0
    · rw [hpreserved gateStart]
      · exact hready.code_eq 0 |>.trans (by
          simp [codeBits, CircuitCode.RawGate.encode])
      · have hbase := hready.base_ge
        have hcode := hready.memo_before_code
        simp only [spillRemainingReg] at hbase
        omega
    · rw [hpreserved (gateStart + 1)]
      · simpa [codeBits, CircuitCode.RawGate.encode] using
          hready.code_eq 1
      · have hbase := hready.base_ge
        have hcode := hready.memo_before_code
        simp only [spillRemainingReg] at hbase
        omega
    · rw [hpreserved (gateStart + 2)]
      · simpa [codeBits, CircuitCode.RawGate.encode] using
          hready.code_eq 2
      · have hbase := hready.base_ge
        have hcode := hready.memo_before_code
        simp only [spillRemainingReg] at hbase
        omega
    · intro index
      rw [hpreserved (base + index)]
      · exact hready.wire_eq index
      · have hbase := hready.base_ge
        simp only [spillRemainingReg] at hbase
        omega
  have hsecondCode : ∀ delta,
      second (gateStart + gate.encode.length + delta) =
        match tail[delta]? with
        | some bit => Input.bitValue bit
        | none => 0 := by
    intro delta
    rw [hpreserved (gateStart + gate.encode.length + delta)]
    · have hcode := hready.code_eq (gate.encode.length + delta)
      rw [show gateStart + (gate.encode.length + delta) =
          gateStart + gate.encode.length + delta by omega] at hcode
      rw [show (codeBits gate tail)[gate.encode.length + delta]? =
          tail[delta]? by
        rw [codeBits, List.getElem?_append_right (by simp)]
        simp] at hcode
      exact hcode
    · have hbase := hready.base_ge
      have hcode := hready.memo_before_code
      simp only [spillRemainingReg] at hbase
      omega
  refine ⟨first, saved, second, firstCost, firstSpace, secondCost,
    secondSpace, hfirst, rfl, hsecond, hparsed, hsecondCode, ?_⟩
  simpa [hcursorEnd] using hsecondBound

private theorem restore_high (store : Store) (index : ℕ)
    (hindex : spillRemainingReg < index) :
    restoreStore store index = store index := by
  simp only [spillRemainingReg] at hindex
  simp (disch := omega) [restoreStore, restoreOps, Basic.execList, Basic.exec,
    Function.update_of_ne, memoBaseReg, wireCountMetaReg, spillPointerReg,
    spillRemainingReg, GateEval.wireCountReg, GateEval.baseReg,
    UnaryDecode.pointerReg, UnaryDecode.remainingReg,
    UnaryDecode.activeReg]

theorem routine_exec_internal {gateStart base : ℕ}
    {gate : CircuitCode.RawGate} {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store)
    (hbound : StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec routine store final (stepCount gate) cost space ∧
      final UnaryDecode.pointerReg = gateStart + gate.encode.length ∧
      final UnaryDecode.remainingReg = tail.length ∧
      final memoBaseReg = base ∧
      final wireCountMetaReg = wires.length + 1 ∧
      final (base + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ delta,
        final (gateStart + gate.encode.length + delta) =
          match tail[delta]? with
          | some bit => Input.bitValue bit
          | none => 0 := by
  obtain ⟨first, saved, second, firstCost, firstSpace, secondCost,
      secondSpace, hfirst, rfl, hsecond, hparsed, hsecondCode,
      _hsecondBound⟩ :=
    decoders_internal hready hbound
  let marshaled := Basic.execList marshalOps second
  obtain ⟨hgateReady, hspillPointer, hspillRemaining⟩ :=
    marshal_ready_internal hparsed
  change GateEval.ReadyAt base gate wires marshaled at hgateReady
  change marshaled spillPointerReg = gateStart + gate.encode.length at hspillPointer
  change marshaled spillRemainingReg = tail.length at hspillRemaining
  obtain ⟨evaluated, gateCost, gateSpace, hgate, houtput, happended,
      hbase, hcount, hwires, hgateFrame⟩ :=
    GateEval.routine_exec_internal hgateReady value0 value1 hvalue0 hvalue1
  have hevalSpillPointer : evaluated spillPointerReg =
      gateStart + gate.encode.length := by
    rw [hgateFrame spillPointerReg]
    · exact hspillPointer
    · simp [GateEval.wireBase, spillPointerReg]
    · have hbaseGe := hready.base_ge
      simp only [spillPointerReg, spillRemainingReg] at hbaseGe ⊢
      omega
  have hevalSpillRemaining : evaluated spillRemainingReg = tail.length := by
    rw [hgateFrame spillRemainingReg]
    · exact hspillRemaining
    · simp [GateEval.wireBase, spillRemainingReg]
    · have hbaseGe := hready.base_ge
      simp only [spillRemainingReg] at hbaseGe ⊢
      omega
  let final := restoreStore evaluated
  have hfinalPointer : final UnaryDecode.pointerReg =
      gateStart + gate.encode.length := by
    have hbase' : evaluated 10 = base := by
      simpa [GateEval.baseReg] using hbase
    have hcount' : evaluated 5 = wires.length := by
      simpa [GateEval.wireCountReg] using hcount
    have hspillPointer' : evaluated 11 =
        gateStart + gate.encode.length := by
      simpa [spillPointerReg] using hevalSpillPointer
    have hspillRemaining' : evaluated 12 = tail.length := by
      simpa [spillRemainingReg] using hevalSpillRemaining
    simp [final, restoreStore, restoreOps, Basic.execList, Basic.exec,
      memoBaseReg, wireCountMetaReg, spillPointerReg, spillRemainingReg,
      GateEval.wireCountReg, GateEval.baseReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.activeReg, hbase', hcount',
      hspillPointer', hspillRemaining']
  have hfinalRemaining : final UnaryDecode.remainingReg = tail.length := by
    have hbase' : evaluated 10 = base := by
      simpa [GateEval.baseReg] using hbase
    have hcount' : evaluated 5 = wires.length := by
      simpa [GateEval.wireCountReg] using hcount
    have hspillPointer' : evaluated 11 =
        gateStart + gate.encode.length := by
      simpa [spillPointerReg] using hevalSpillPointer
    have hspillRemaining' : evaluated 12 = tail.length := by
      simpa [spillRemainingReg] using hevalSpillRemaining
    simp [final, restoreStore, restoreOps, Basic.execList, Basic.exec,
      memoBaseReg, wireCountMetaReg, spillPointerReg, spillRemainingReg,
      GateEval.wireCountReg, GateEval.baseReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.activeReg, hbase', hcount',
      hspillPointer', hspillRemaining']
  have hfinalBase : final memoBaseReg = base := by
    have hbase' : evaluated 10 = base := by
      simpa [GateEval.baseReg] using hbase
    simp [final, restoreStore, restoreOps, Basic.execList, Basic.exec,
      memoBaseReg, wireCountMetaReg, spillPointerReg, spillRemainingReg,
      GateEval.wireCountReg, GateEval.baseReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.activeReg, hbase']
  have hfinalCount : final wireCountMetaReg = wires.length + 1 := by
    have hcount' : evaluated 5 = wires.length := by
      simpa [GateEval.wireCountReg] using hcount
    simp [final, restoreStore, restoreOps, Basic.execList, Basic.exec,
      memoBaseReg, wireCountMetaReg, spillPointerReg, spillRemainingReg,
      GateEval.wireCountReg, GateEval.baseReg, UnaryDecode.pointerReg,
      UnaryDecode.remainingReg, UnaryDecode.activeReg, hcount']
  have hfinalAppended : final (base + wires.length) =
      Input.bitValue (gate.eval value0 value1) := by
    rw [show final (base + wires.length) =
        evaluated (base + wires.length) by
      apply restore_high
      have hbaseGe := hready.base_ge
      simp only [spillRemainingReg] at hbaseGe ⊢
      omega]
    exact happended
  have hfinalWires : ∀ index (hindex : index < wires.length),
      final (base + index) = Input.bitValue wires[index] := by
    intro index hindex
    rw [show final (base + index) = evaluated (base + index) by
      apply restore_high
      have hbaseGe := hready.base_ge
      simp only [spillRemainingReg] at hbaseGe ⊢
      omega]
    exact hwires index hindex
  have hfinalCode : ∀ delta,
      final (gateStart + gate.encode.length + delta) =
        match tail[delta]? with
        | some bit => Input.bitValue bit
        | none => 0 := by
    intro delta
    have hcodeAddress : spillRemainingReg <
        gateStart + gate.encode.length + delta := by
      have hbaseGe := hready.base_ge
      have hcode := hready.memo_before_code
      simp only [spillRemainingReg] at hbaseGe ⊢
      omega
    change restoreStore evaluated
      (gateStart + gate.encode.length + delta) = _
    rw [restore_high evaluated _ hcodeAddress]
    rw [hgateFrame _]
    · change marshalStore second
          (gateStart + gate.encode.length + delta) = _
      rw [marshal_high second _ hcodeAddress]
      exact hsecondCode delta
    · simp only [GateEval.wireBase, spillRemainingReg] at hcodeAddress ⊢
      omega
    · have hcode := hready.memo_before_code
      omega
  obtain ⟨setupCost, setupSpace, hsetup⟩ := exec_basics_exists setupOps store
  obtain ⟨headerCost, headerSpace, hheader⟩ :=
    exec_basics_exists headerOps (setupStore store)
  obtain ⟨saveCost, saveSpace, hsave⟩ := exec_basics_exists saveRestartOps first
  obtain ⟨marshalCost, marshalSpace, hmarshal⟩ :=
    exec_basics_exists marshalOps second
  obtain ⟨restoreCost, restoreSpace, hrestore⟩ :=
    exec_basics_exists restoreOps evaluated
  have hrun := hsetup.seq (hheader.seq (hfirst.seq
    (hsave.seq (hsecond.seq (hmarshal.seq (hgate.seq hrestore))))))
  have hsteps : setupOps.length +
      (headerOps.length + (UnaryDecode.loopStepCount (firstRemaining gate tail) +
        (saveRestartOps.length +
          (UnaryDecode.loopStepCount (secondRemaining gate tail) +
            (marshalOps.length + (GateEval.stepCount + restoreOps.length)))))) =
      stepCount gate := by
    simp [setupOps, headerOps, saveRestartOps, marshalOps, restoreOps,
      UnaryDecode.loopStepCount, firstRemaining, secondRemaining,
      GateEval.stepCount, stepCount]
    omega
  have hexec : ∃ cost space,
      Exec routine store final (stepCount gate) cost space := by
    refine ⟨setupCost + (headerCost + (firstCost +
        (saveCost + (secondCost + (marshalCost + (gateCost + restoreCost)))))),
      max setupSpace (max headerSpace (max firstSpace
        (max saveSpace (max secondSpace
          (max marshalSpace (max gateSpace restoreSpace)))))), ?_⟩
    rw [← hsteps]
    simpa [routine, setupStore, headerStore, saveRestartStore, marshaled,
      final, restoreStore] using! hrun
  obtain ⟨cost, space, hexec⟩ := hexec
  exact ⟨final, cost, space, hexec, hfinalPointer, hfinalRemaining,
    hfinalBase, hfinalCount, hfinalAppended, hfinalWires, hfinalCode⟩

end GateStreamStep

end Structured

end RAM

end Complexity
