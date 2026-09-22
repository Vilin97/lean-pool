/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Encoding.Internal.Codec
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Internal
public import Mathlib.Tactic.IntervalCases

/-!
# Structured RAM serialized-gate step — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStep

open Internal

private abbrev cursorBound (gate : CircuitCode.RawGate) (wires : List Bool) : ℕ :=
  (inputBits gate wires).length + UnaryDecode.inputBase

private abbrev CursorEnvelope (gate : CircuitCode.RawGate) (wires : List Bool)
    (store : Store) : Prop :=
  StoreEnvelope (cursorBound gate wires) (cursorBound gate wires) store

private def setupStore (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList UnaryDecode.setupOps (inputStore gate wires)

private def headerStore (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList headerOps (setupStore gate wires)

private def saveRestartStore (store : Store) : Store :=
  Basic.execList saveRestartOps store

private def marshalStore (store : Store) : Store :=
  Basic.execList marshalOps store

private theorem input_bound (gate : CircuitCode.RawGate) (wires : List Bool) :
    CursorEnvelope gate wires (inputStore gate wires) := by
  apply Input.bitStoreEnvelope
  · simp [cursorBound, inputBits, UnaryDecode.remainingReg,
      UnaryDecode.inputBase]
  · simp [cursorBound, UnaryDecode.inputBase]
    omega
  · simp [cursorBound, UnaryDecode.inputBase]
  · simp [cursorBound, inputBits, UnaryDecode.inputBase]

private theorem setup_measured (gate : CircuitCode.RawGate) (wires : List Bool) :
    MeasuredRuns UnaryDecode.setup (inputStore gate wires)
        (setupStore gate wires) 5
        (20 * valueWidth (cursorBound gate wires))
        (envelopeSpace (cursorBound gate wires) (cursorBound gate wires)) ∧
      CursorEnvelope gate wires (setupStore gate wires) := by
  have hinitial := input_bound gate wires
  have hpreserve : ∀ op, op ∈ UnaryDecode.setupOps → ∀ store,
      CursorEnvelope gate wires store → CursorEnvelope gate wires (op.exec store) := by
    intro op hop store hstore
    simp [UnaryDecode.setupOps] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    · apply hstore.execBasic (.imm UnaryDecode.verdictReg 0) <;>
        simp [cursorBound, inputBits, UnaryDecode.verdictReg,
          UnaryDecode.inputBase]
    · apply hstore.execBasic (.imm UnaryDecode.valueReg 0) <;>
        simp [cursorBound, inputBits, UnaryDecode.valueReg,
          UnaryDecode.inputBase]
    · apply hstore.execBasic (.imm UnaryDecode.pointerReg UnaryDecode.inputBase)
      · simp [cursorBound, inputBits, UnaryDecode.pointerReg,
          UnaryDecode.inputBase]
      · simp [Basic.writeValue, cursorBound, inputBits, UnaryDecode.inputBase]
    · apply hstore.execBasic (.imm UnaryDecode.oneReg 1) <;>
        simp [cursorBound, inputBits, UnaryDecode.oneReg, UnaryDecode.inputBase]
    · apply hstore.execBasic (.imm UnaryDecode.activeReg 1) <;>
        simp [cursorBound, inputBits, UnaryDecode.activeReg,
          UnaryDecode.inputBase]
  simpa [UnaryDecode.setup, setupStore] using!
    MeasuredRuns.basicsEnvelope UnaryDecode.setupOps (inputStore gate wires)
      hinitial hpreserve

private theorem header_high (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) (hindex : 10 ≤ index) :
    headerStore gate wires index = inputStore gate wires index := by
  have h0 : index ≠ 0 := by omega
  have h1 : index ≠ 1 := by omega
  have h2 : index ≠ 2 := by omega
  have h3 : index ≠ 3 := by omega
  have h4 : index ≠ 4 := by omega
  have h6 : index ≠ 6 := by omega
  have h7 : index ≠ 7 := by omega
  have h8 : index ≠ 8 := by omega
  have h9 : index ≠ 9 := by omega
  simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
    Basic.execList, Basic.exec, Function.update_of_ne, h0, h1, h2, h3, h4, h6,
    h7, h8, h9, headerOpReg, headerNegated0Reg, headerNegated1Reg,
    UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.pointerReg,
    UnaryDecode.remainingReg, UnaryDecode.oneReg, UnaryDecode.activeReg,
    UnaryDecode.inputBase]

private theorem header_bound (gate : CircuitCode.RawGate) (wires : List Bool) :
    CursorEnvelope gate wires (headerStore gate wires) := by
  have hinitial := input_bound gate wires
  have hlarge : 10 < cursorBound gate wires := by
    simp [cursorBound, inputBits, CircuitCode.RawGate.encode,
      UnaryDecode.inputBase]
  constructor
  · intro index hnonzero
    by_cases hindex : index < 10
    · omega
    · rw [header_high gate wires index (by omega)] at hnonzero
      exact hinitial.index_lt index hnonzero
  · intro index
    by_cases hindex : index < 10
    · interval_cases index <;>
        simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
          Basic.execList, Basic.exec, inputStore, Input.bitStore, inputBits,
          CircuitCode.RawGate.encode, cursorBound, headerOpReg,
          headerNegated0Reg, headerNegated1Reg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.pointerReg,
          UnaryDecode.remainingReg, UnaryDecode.oneReg, UnaryDecode.activeReg,
          UnaryDecode.inputBase]
      all_goals try omega
      all_goals split <;> simp
    · rw [header_high gate wires index (by omega)]
      exact hinitial.value_le index

private theorem header_measured (gate : CircuitCode.RawGate) (wires : List Bool) :
    MeasuredRuns (.basics headerOps) (setupStore gate wires)
        (headerStore gate wires) 9
        (36 * valueWidth (cursorBound gate wires))
        (envelopeSpace (cursorBound gate wires) (cursorBound gate wires)) ∧
      CursorEnvelope gate wires (headerStore gate wires) := by
  have hsetup := (setup_measured gate wires).2
  have hlarge : 10 < cursorBound gate wires := by
    simp [cursorBound, inputBits, CircuitCode.RawGate.encode,
      UnaryDecode.inputBase]
  let s1 := (Basic.load headerOpReg UnaryDecode.pointerReg).exec
    (setupStore gate wires)
  let s2 := (Basic.add UnaryDecode.pointerReg UnaryDecode.pointerReg
    UnaryDecode.oneReg).exec s1
  let s3 := (Basic.sub UnaryDecode.remainingReg UnaryDecode.remainingReg
    UnaryDecode.oneReg).exec s2
  let s4 := (Basic.load headerNegated0Reg UnaryDecode.pointerReg).exec s3
  let s5 := (Basic.add UnaryDecode.pointerReg UnaryDecode.pointerReg
    UnaryDecode.oneReg).exec s4
  let s6 := (Basic.sub UnaryDecode.remainingReg UnaryDecode.remainingReg
    UnaryDecode.oneReg).exec s5
  let s7 := (Basic.load headerNegated1Reg UnaryDecode.pointerReg).exec s6
  let s8 := (Basic.add UnaryDecode.pointerReg UnaryDecode.pointerReg
    UnaryDecode.oneReg).exec s7
  have hsetupPointer : setupStore gate wires UnaryDecode.pointerReg =
      UnaryDecode.inputBase := by
    simp [setupStore, UnaryDecode.setupOps, Basic.execList, Basic.exec,
      UnaryDecode.pointerReg, UnaryDecode.oneReg, UnaryDecode.activeReg]
  have hsetupOne : setupStore gate wires UnaryDecode.oneReg = 1 := by
    simp [setupStore, UnaryDecode.setupOps, Basic.execList, Basic.exec,
      UnaryDecode.pointerReg, UnaryDecode.oneReg, UnaryDecode.activeReg]
  have h1 : CursorEnvelope gate wires s1 := by
    apply hsetup.execBasic (.load headerOpReg UnaryDecode.pointerReg)
    · simp [headerOpReg, UnaryDecode.inputBase]
      omega
    · exact hsetup.value_le (setupStore gate wires UnaryDecode.pointerReg)
  have hs1Pointer : s1 UnaryDecode.pointerReg = UnaryDecode.inputBase := by
    rw [show s1 UnaryDecode.pointerReg =
        setupStore gate wires UnaryDecode.pointerReg by
      simp [s1, Basic.exec, Function.update_of_ne, headerOpReg,
        UnaryDecode.pointerReg, UnaryDecode.inputBase]]
    exact hsetupPointer
  have hs1One : s1 UnaryDecode.oneReg = 1 := by
    rw [show s1 UnaryDecode.oneReg = setupStore gate wires UnaryDecode.oneReg by
      simp [s1, Basic.exec, Function.update_of_ne, headerOpReg,
        UnaryDecode.oneReg, UnaryDecode.inputBase]]
    exact hsetupOne
  have h2 : CursorEnvelope gate wires s2 := by
    apply h1.execBasic (.add UnaryDecode.pointerReg UnaryDecode.pointerReg
      UnaryDecode.oneReg)
    · simp [UnaryDecode.pointerReg]
      omega
    · change s1 UnaryDecode.pointerReg + s1 UnaryDecode.oneReg ≤
        cursorBound gate wires
      have hp := hs1Pointer
      have ho := hs1One
      simp only [UnaryDecode.pointerReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase] at hp ho ⊢
      omega
  have h3 : CursorEnvelope gate wires s3 := by
    apply h2.execBasic (.sub UnaryDecode.remainingReg UnaryDecode.remainingReg
      UnaryDecode.oneReg)
    · simp [UnaryDecode.remainingReg]
      omega
    · exact le_trans (Nat.sub_le _ _) (h2.value_le UnaryDecode.remainingReg)
  have h4 : CursorEnvelope gate wires s4 := by
    apply h3.execBasic (.load headerNegated0Reg UnaryDecode.pointerReg)
    · simp [headerNegated0Reg, UnaryDecode.inputBase]
      omega
    · exact h3.value_le (s3 UnaryDecode.pointerReg)
  have hs4Pointer : s4 UnaryDecode.pointerReg = UnaryDecode.inputBase + 1 := by
    rw [show s4 UnaryDecode.pointerReg =
        s1 UnaryDecode.pointerReg + s1 UnaryDecode.oneReg by
      simp [s4, s3, s2, Basic.exec, Function.update_of_ne,
        headerNegated0Reg, UnaryDecode.pointerReg,
        UnaryDecode.remainingReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase]]
    rw [hs1Pointer, hs1One]
  have hs4One : s4 UnaryDecode.oneReg = 1 := by
    rw [show s4 UnaryDecode.oneReg = s1 UnaryDecode.oneReg by
      simp [s4, s3, s2, Basic.exec, Function.update_of_ne,
        headerNegated0Reg, UnaryDecode.pointerReg,
        UnaryDecode.remainingReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase]]
    exact hs1One
  have h5 : CursorEnvelope gate wires s5 := by
    apply h4.execBasic (.add UnaryDecode.pointerReg UnaryDecode.pointerReg
      UnaryDecode.oneReg)
    · simp [UnaryDecode.pointerReg]
      omega
    · change s4 UnaryDecode.pointerReg + s4 UnaryDecode.oneReg ≤
        cursorBound gate wires
      have hp := hs4Pointer
      have ho := hs4One
      simp only [UnaryDecode.pointerReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase] at hp ho ⊢
      omega
  have h6 : CursorEnvelope gate wires s6 := by
    apply h5.execBasic (.sub UnaryDecode.remainingReg UnaryDecode.remainingReg
      UnaryDecode.oneReg)
    · simp [UnaryDecode.remainingReg]
      omega
    · exact le_trans (Nat.sub_le _ _) (h5.value_le UnaryDecode.remainingReg)
  have h7 : CursorEnvelope gate wires s7 := by
    apply h6.execBasic (.load headerNegated1Reg UnaryDecode.pointerReg)
    · simp [headerNegated1Reg, UnaryDecode.inputBase]
      omega
    · exact h6.value_le (s6 UnaryDecode.pointerReg)
  have hs7Pointer : s7 UnaryDecode.pointerReg = UnaryDecode.inputBase + 2 := by
    rw [show s7 UnaryDecode.pointerReg =
        s4 UnaryDecode.pointerReg + s4 UnaryDecode.oneReg by
      simp [s7, s6, s5, Basic.exec, Function.update_of_ne,
        headerNegated1Reg, UnaryDecode.pointerReg,
        UnaryDecode.remainingReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase]]
    rw [hs4Pointer, hs4One]
  have hs7One : s7 UnaryDecode.oneReg = 1 := by
    rw [show s7 UnaryDecode.oneReg = s4 UnaryDecode.oneReg by
      simp [s7, s6, s5, Basic.exec, Function.update_of_ne,
        headerNegated1Reg, UnaryDecode.pointerReg,
        UnaryDecode.remainingReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase]]
    exact hs4One
  have h8 : CursorEnvelope gate wires s8 := by
    apply h7.execBasic (.add UnaryDecode.pointerReg UnaryDecode.pointerReg
      UnaryDecode.oneReg)
    · simp [UnaryDecode.pointerReg]
      omega
    · change s7 UnaryDecode.pointerReg + s7 UnaryDecode.oneReg ≤
        cursorBound gate wires
      have hp := hs7Pointer
      have ho := hs7One
      simp only [UnaryDecode.pointerReg, UnaryDecode.oneReg,
        UnaryDecode.inputBase] at hp ho ⊢
      omega
  have h9 := header_bound gate wires
  have r1 := MeasuredRuns.basicEnvelope
    (.load headerOpReg UnaryDecode.pointerReg) (setupStore gate wires) hsetup h1
  have r2 := MeasuredRuns.basicEnvelope
    (.add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg)
    s1 h1 h2
  have r3 := MeasuredRuns.basicEnvelope
    (.sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg)
    s2 h2 h3
  have r4 := MeasuredRuns.basicEnvelope
    (.load headerNegated0Reg UnaryDecode.pointerReg) s3 h3 h4
  have r5 := MeasuredRuns.basicEnvelope
    (.add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg)
    s4 h4 h5
  have r6 := MeasuredRuns.basicEnvelope
    (.sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg)
    s5 h5 h6
  have r7 := MeasuredRuns.basicEnvelope
    (.load headerNegated1Reg UnaryDecode.pointerReg) s6 h6 h7
  have r8 := MeasuredRuns.basicEnvelope
    (.add UnaryDecode.pointerReg UnaryDecode.pointerReg UnaryDecode.oneReg)
    s7 h7 h8
  have r9 := MeasuredRuns.basicEnvelope
    (.sub UnaryDecode.remainingReg UnaryDecode.remainingReg UnaryDecode.oneReg)
    s8 h8 h9
  refine ⟨?_, h9⟩
  have hrun := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq
    (r6.seq (r7.seq (r8.seq r9)))))))
  convert! hrun using 1
  ring

private theorem header_cursorReady (gate : CircuitCode.RawGate) (wires : List Bool) :
    UnaryDecode.CursorReady (inputBits gate wires).length
      (CircuitCode.NatCode.encode gate.input₀ ++
        CircuitCode.NatCode.encode gate.input₁ ++ wires)
      3 0 (headerStore gate wires) := by
  constructor
  · simp [inputBits, CircuitCode.RawGate.encode]
    omega
  · omega
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
      Basic.execList, Basic.exec, inputStore, Input.bitStore,
      inputBits, CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
      headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
      UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
      UnaryDecode.activeReg, UnaryDecode.inputBase]
  · intro delta
    have h1 : 10 + delta ≠ 1 := by omega
    have h2 : 10 + delta ≠ 2 := by omega
    have h3 : 10 + delta ≠ 3 := by omega
    have h4 : 10 + delta ≠ 4 := by omega
    have h6 : 10 + delta ≠ 6 := by omega
    have h7 : 10 + delta ≠ 7 := by omega
    have h8 : 10 + delta ≠ 8 := by omega
    have h9 : 10 + delta ≠ 9 := by omega
    have hpreserved : headerStore gate wires (10 + delta) =
        inputStore gate wires (10 + delta) := by
      simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
        Basic.execList, Basic.exec, Function.update_of_ne, h1, h2, h3, h4,
        h6, h7, h8, h9, headerOpReg, headerNegated0Reg, headerNegated1Reg,
        UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.pointerReg,
        UnaryDecode.remainingReg, UnaryDecode.oneReg, UnaryDecode.activeReg,
        UnaryDecode.inputBase]
    change headerStore gate wires (10 + delta) = _
    rw [hpreserved]
    simp only [inputStore, Input.bitStore, UnaryDecode.remainingReg,
      UnaryDecode.inputBase]
    change (if 10 + delta = 3 then (inputBits gate wires).length else
      if 7 ≤ 10 + delta then
        match (inputBits gate wires)[10 + delta - 7]? with
        | some bit => Input.bitValue bit
        | none => 0
      else 0) = _
    rw [ite_eq_right (by omega : 10 + delta ≠ 3), ite_eq_left (by omega : 7 ≤ 10 + delta)]
    have hoffset : 10 + delta - 7 = 3 + delta := by omega
    rw [hoffset]
    change
      (match (inputBits gate wires)[3 + delta]? with
      | some bit => Input.bitValue bit
      | none => 0) = _
    rw [show inputBits gate wires =
        [gate.opBit, gate.negated₀, gate.negated₁] ++
          (CircuitCode.NatCode.encode gate.input₀ ++
            CircuitCode.NatCode.encode gate.input₁ ++ wires) by
      simp [inputBits, CircuitCode.RawGate.encode, List.append_assoc]]
    rw [List.getElem?_append_right (by simp :
      [gate.opBit, gate.negated₀, gate.negated₁].length ≤ 3 + delta)]
    simp
    rfl

private theorem header_op (gate : CircuitCode.RawGate) (wires : List Bool) :
    headerStore gate wires headerOpReg = Input.bitValue gate.opBit := by
  simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
    Basic.execList, Basic.exec, inputStore, Input.bitStore, inputBits,
    CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
    headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
    UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
    UnaryDecode.activeReg, UnaryDecode.inputBase]

private theorem header_negated0 (gate : CircuitCode.RawGate) (wires : List Bool) :
    headerStore gate wires headerNegated0Reg = Input.bitValue gate.negated₀ := by
  simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
    Basic.execList, Basic.exec, inputStore, Input.bitStore, inputBits,
    CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
    headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
    UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
    UnaryDecode.activeReg, UnaryDecode.inputBase]

private theorem header_negated1 (gate : CircuitCode.RawGate) (wires : List Bool) :
    headerStore gate wires headerNegated1Reg = Input.bitValue gate.negated₁ := by
  simp [headerStore, headerOps, setupStore, UnaryDecode.setupOps,
    Basic.execList, Basic.exec, inputStore, Input.bitStore, inputBits,
    CircuitCode.RawGate.encode, headerOpReg, headerNegated0Reg,
    headerNegated1Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
    UnaryDecode.pointerReg, UnaryDecode.remainingReg, UnaryDecode.oneReg,
    UnaryDecode.activeReg, UnaryDecode.inputBase]

private theorem saveRestart_high (store : Store) (index : ℕ)
    (hindex : 11 ≤ index) : saveRestartStore store index = store index := by
  have h0 : index ≠ UnaryDecode.verdictReg := by
    simp only [UnaryDecode.verdictReg] at hindex ⊢
    omega
  have h1 : index ≠ UnaryDecode.valueReg := by
    simp only [UnaryDecode.valueReg] at hindex ⊢
    omega
  have h6 : index ≠ UnaryDecode.activeReg := by
    simp only [UnaryDecode.activeReg] at hindex ⊢
    omega
  have h10 : index ≠ savedInput0Reg := by
    simp only [savedInput0Reg, UnaryDecode.inputBase] at hindex ⊢
    omega
  simp [saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
    Function.update_of_ne, h0, h1, h6, h10]

private theorem saveRestart_apply_of_ne (store : Store) (index : ℕ)
    (hsaved : index ≠ savedInput0Reg)
    (hverdict : index ≠ UnaryDecode.verdictReg)
    (hvalue : index ≠ UnaryDecode.valueReg)
    (hactive : index ≠ UnaryDecode.activeReg) :
    saveRestartStore store index = store index := by
  simp [saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
    Function.update_of_ne, hsaved, hverdict, hvalue, hactive]

private theorem saveRestart_saved (store : Store) :
    saveRestartStore store savedInput0Reg =
      store UnaryDecode.valueReg + store UnaryDecode.activeReg := by
  simp [saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
    savedInput0Reg, UnaryDecode.inputBase, UnaryDecode.verdictReg,
    UnaryDecode.valueReg, UnaryDecode.activeReg]

private theorem marshal_high (store : Store) (index : ℕ)
    (hindex : 11 ≤ index) : marshalStore store index = store index := by
  have h0 : index ≠ GateEval.opReg := by
    simp only [GateEval.opReg] at hindex ⊢
    omega
  have h1 : index ≠ GateEval.negated0Reg := by
    simp only [GateEval.negated0Reg] at hindex ⊢
    omega
  have h2 : index ≠ GateEval.negated1Reg := by
    simp only [GateEval.negated1Reg] at hindex ⊢
    omega
  have h3 : index ≠ GateEval.address0Reg := by
    simp only [GateEval.address0Reg] at hindex ⊢
    omega
  have h4 : index ≠ GateEval.address1Reg := by
    simp only [GateEval.address1Reg] at hindex ⊢
    omega
  have h5 : index ≠ GateEval.wireCountReg := by
    simp only [GateEval.wireCountReg] at hindex ⊢
    omega
  have h10 : index ≠ GateEval.baseReg := by
    simp only [GateEval.baseReg] at hindex ⊢
    omega
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    Function.update_of_ne, h0, h1, h2, h3, h4, h5, h10]

private theorem marshal_wireCount (store : Store) :
    marshalStore store GateEval.wireCountReg =
      store UnaryDecode.remainingReg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, UnaryDecode.remainingReg, UnaryDecode.activeReg]

private theorem marshal_address1 (store : Store) :
    marshalStore store GateEval.address1Reg =
      store UnaryDecode.valueReg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, UnaryDecode.valueReg, UnaryDecode.activeReg]

private theorem marshal_address0 (store : Store) :
    marshalStore store GateEval.address0Reg =
      store savedInput0Reg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, savedInput0Reg, UnaryDecode.inputBase,
    UnaryDecode.activeReg]

private theorem marshal_base (store : Store) :
    marshalStore store GateEval.baseReg =
      store UnaryDecode.pointerReg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, UnaryDecode.pointerReg, UnaryDecode.activeReg]

private theorem marshal_op (store : Store) :
    marshalStore store GateEval.opReg =
      store headerOpReg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, headerOpReg, UnaryDecode.inputBase,
    UnaryDecode.activeReg]

private theorem marshal_negated0 (store : Store) :
    marshalStore store GateEval.negated0Reg =
      store headerNegated0Reg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, headerNegated0Reg, UnaryDecode.inputBase,
    UnaryDecode.activeReg]

private theorem marshal_negated1 (store : Store) :
    marshalStore store GateEval.negated1Reg =
      store headerNegated1Reg + store UnaryDecode.activeReg := by
  simp [marshalStore, marshalOps, Basic.execList, Basic.exec,
    GateEval.opReg, GateEval.negated0Reg, GateEval.negated1Reg,
    GateEval.address0Reg, GateEval.address1Reg, GateEval.wireCountReg,
    GateEval.baseReg, headerNegated1Reg, UnaryDecode.inputBase,
    UnaryDecode.activeReg]

private theorem copyAdd_measured {bound dst src active : ℕ} {store : Store}
    (hstore : StoreEnvelope bound bound store) (hdst : dst < bound)
    (hactive : store active = 0) (hne : dst ≠ active) :
    MeasuredRuns (.basic (.add dst src active)) store
        ((Basic.add dst src active).exec store) 1
        (4 * valueWidth bound) (envelopeSpace bound bound) ∧
      StoreEnvelope bound bound ((Basic.add dst src active).exec store) ∧
      (Basic.add dst src active).exec store active = 0 := by
  have hnext : StoreEnvelope bound bound
      ((Basic.add dst src active).exec store) := by
    apply hstore.execBasic (.add dst src active)
    · exact hdst
    · change store src + store active ≤ bound
      rw [hactive, Nat.add_zero]
      exact hstore.value_le src
  refine ⟨MeasuredRuns.basicEnvelope (.add dst src active) store hstore hnext,
    hnext, ?_⟩
  simp [Basic.exec, Function.update_of_ne (Ne.symm hne), hactive]

private theorem saveRestart_measured {bound : ℕ} {store : Store}
    (hstore : StoreEnvelope bound bound store) (hsmall : 10 < bound)
    (hactive : store UnaryDecode.activeReg = 0) :
    MeasuredRuns (.basics saveRestartOps) store (saveRestartStore store) 4
        (16 * valueWidth bound) (envelopeSpace bound bound) ∧
      StoreEnvelope bound bound (saveRestartStore store) := by
  let s1 := (Basic.add savedInput0Reg UnaryDecode.valueReg
    UnaryDecode.activeReg).exec store
  let s2 := (Basic.imm UnaryDecode.verdictReg 0).exec s1
  let s3 := (Basic.imm UnaryDecode.valueReg 0).exec s2
  have h1 := copyAdd_measured hstore
    (dst := savedInput0Reg) (src := UnaryDecode.valueReg)
    (active := UnaryDecode.activeReg)
    (by simp [savedInput0Reg, UnaryDecode.inputBase]; omega) hactive
    (by simp [savedInput0Reg, UnaryDecode.activeReg, UnaryDecode.inputBase])
  have h2 : StoreEnvelope bound bound s2 := by
    apply h1.2.1.execBasic (.imm UnaryDecode.verdictReg 0)
    · simp [UnaryDecode.verdictReg]
      omega
    · simp [Basic.writeValue]
  have h3 : StoreEnvelope bound bound s3 := by
    apply h2.execBasic (.imm UnaryDecode.valueReg 0)
    · simp [UnaryDecode.valueReg]
      omega
    · simp [Basic.writeValue]
  have h4 : StoreEnvelope bound bound (saveRestartStore store) := by
    change StoreEnvelope bound bound
      ((Basic.imm UnaryDecode.activeReg 1).exec s3)
    apply h3.execBasic (.imm UnaryDecode.activeReg 1)
    · simp [UnaryDecode.activeReg]
      omega
    · simp [Basic.writeValue]
      omega
  have r2 := MeasuredRuns.basicEnvelope (.imm UnaryDecode.verdictReg 0)
    s1 h1.2.1 h2
  have r3 := MeasuredRuns.basicEnvelope (.imm UnaryDecode.valueReg 0) s2 h2 h3
  have r4 := MeasuredRuns.basicEnvelope (.imm UnaryDecode.activeReg 1) s3 h3 h4
  refine ⟨?_, h4⟩
  have hrun := h1.1.seq (r2.seq (r3.seq r4))
  convert! hrun using 1
  ring

private theorem marshal_measured {bound : ℕ} {store : Store}
    (hstore : StoreEnvelope bound bound store) (hsmall : 10 < bound)
    (hactive : store UnaryDecode.activeReg = 0) :
    MeasuredRuns (.basics marshalOps) store (marshalStore store) 7
        (28 * valueWidth bound) (envelopeSpace bound bound) ∧
      StoreEnvelope bound bound (marshalStore store) := by
  let s1 := (Basic.add GateEval.wireCountReg UnaryDecode.remainingReg
    UnaryDecode.activeReg).exec store
  let s2 := (Basic.add GateEval.address1Reg UnaryDecode.valueReg
    UnaryDecode.activeReg).exec s1
  let s3 := (Basic.add GateEval.address0Reg savedInput0Reg
    UnaryDecode.activeReg).exec s2
  let s4 := (Basic.add GateEval.baseReg UnaryDecode.pointerReg
    UnaryDecode.activeReg).exec s3
  let s5 := (Basic.add GateEval.opReg headerOpReg
    UnaryDecode.activeReg).exec s4
  let s6 := (Basic.add GateEval.negated0Reg headerNegated0Reg
    UnaryDecode.activeReg).exec s5
  have r1 := copyAdd_measured hstore
    (dst := GateEval.wireCountReg) (src := UnaryDecode.remainingReg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.wireCountReg]; omega)
    hactive (by simp [GateEval.wireCountReg, UnaryDecode.activeReg])
  have r2 := copyAdd_measured r1.2.1
    (dst := GateEval.address1Reg) (src := UnaryDecode.valueReg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.address1Reg]; omega)
    r1.2.2 (by simp [GateEval.address1Reg, UnaryDecode.activeReg])
  have r3 := copyAdd_measured r2.2.1
    (dst := GateEval.address0Reg) (src := savedInput0Reg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.address0Reg]; omega)
    r2.2.2 (by simp [GateEval.address0Reg, UnaryDecode.activeReg])
  have r4 := copyAdd_measured r3.2.1
    (dst := GateEval.baseReg) (src := UnaryDecode.pointerReg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.baseReg]; omega)
    r3.2.2 (by simp [GateEval.baseReg, UnaryDecode.activeReg])
  have r5 := copyAdd_measured r4.2.1
    (dst := GateEval.opReg) (src := headerOpReg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.opReg]; omega)
    r4.2.2 (by simp [GateEval.opReg, UnaryDecode.activeReg])
  have r6 := copyAdd_measured r5.2.1
    (dst := GateEval.negated0Reg) (src := headerNegated0Reg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.negated0Reg]; omega)
    r5.2.2 (by simp [GateEval.negated0Reg, UnaryDecode.activeReg])
  have r7 := copyAdd_measured r6.2.1
    (dst := GateEval.negated1Reg) (src := headerNegated1Reg)
    (active := UnaryDecode.activeReg) (by simp [GateEval.negated1Reg]; omega)
    r6.2.2 (by simp [GateEval.negated1Reg, UnaryDecode.activeReg])
  refine ⟨?_, ?_⟩
  · have hrun := r1.1.seq (r2.1.seq (r3.1.seq
      (r4.1.seq (r5.1.seq (r6.1.seq r7.1)))))
    convert! hrun using 1
    ring
  · simpa [marshalStore, marshalOps, s1, s2, s3, s4, s5, s6] using! r7.2.1

private theorem input_wire (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) :
    inputStore gate wires (memoBase gate + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0 := by
  have hbase : UnaryDecode.inputBase ≤ memoBase gate + index := by
    simp [memoBase]
    omega
  have hlength : memoBase gate + index ≠ UnaryDecode.remainingReg := by
    simp only [memoBase, UnaryDecode.inputBase, UnaryDecode.remainingReg]
    omega
  simp only [inputStore, Input.bitStore]
  rw [ite_eq_right hlength, ite_eq_left hbase]
  have hoffset : memoBase gate + index - UnaryDecode.inputBase =
      gate.encode.length + index := by
    simp [memoBase]
    omega
  rw [hoffset, inputBits, List.getElem?_append_right (by omega)]
  simp
  rfl

theorem program_measured_internal (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      cost ≤ timeBound gate wires ∧ space ≤ spaceBound gate wires ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] := by
  let firstRemaining := CircuitCode.NatCode.encode gate.input₀ ++
    CircuitCode.NatCode.encode gate.input₁ ++ wires
  let secondRemaining := CircuitCode.NatCode.encode gate.input₁ ++ wires
  have hheaderReady : UnaryDecode.CursorReady (inputBits gate wires).length
      firstRemaining 3 0 (headerStore gate wires) := by
    simpa [firstRemaining] using header_cursorReady gate wires
  have hheaderBound : StoreEnvelope
      ((inputBits gate wires).length + UnaryDecode.inputBase)
      ((inputBits gate wires).length + UnaryDecode.inputBase)
      (headerStore gate wires) := by
    simpa [cursorBound] using header_bound gate wires
  obtain ⟨first, firstCost, firstSpace, hfirst, hfirstCost, hfirstSpace,
      hfirstResult, hfirstActive, hfirstOne, hfirstFrame, hfirstBound⟩ :=
    UnaryDecode.mainLoop_measured_internal hheaderReady hheaderBound
  have hdecode0 : CircuitCode.NatCode.decodePrefix? firstRemaining =
      some (gate.input₀, secondRemaining) := by
    simp [firstRemaining, secondRemaining, List.append_assoc]
  rw [hdecode0] at hfirstResult
  simp only at hfirstResult
  have hfirstVerdict : first UnaryDecode.verdictReg = 1 := hfirstResult.1
  have hfirstValue : first UnaryDecode.valueReg = gate.input₀ := by
    simpa using hfirstResult.2.1
  have hfirstPointer : first UnaryDecode.pointerReg =
      UnaryDecode.inputBase + 3 + gate.input₀ + 1 := hfirstResult.2.2.1
  have hfirstRemaining : first UnaryDecode.remainingReg = secondRemaining.length :=
    hfirstResult.2.2.2
  let saved := saveRestartStore first
  have hlarge : 10 < cursorBound gate wires := by
    simp [cursorBound, inputBits, CircuitCode.RawGate.encode,
      UnaryDecode.inputBase]
  have hsaved0 : CursorEnvelope gate wires
      ((Basic.add savedInput0Reg UnaryDecode.valueReg
        UnaryDecode.activeReg).exec first) := by
    apply hfirstBound.execBasic
    · simpa [savedInput0Reg, UnaryDecode.inputBase] using! hlarge
    · change first UnaryDecode.valueReg + first UnaryDecode.activeReg ≤
        cursorBound gate wires
      rw [hfirstValue, hfirstActive]
      simp [cursorBound, inputBits, CircuitCode.RawGate.encode,
        UnaryDecode.inputBase]
      omega
  have hsaved1 := hsaved0.execBasic (.imm UnaryDecode.verdictReg 0)
    (by simpa [Basic.writeIndex, UnaryDecode.verdictReg] using
      (lt_trans (by decide : 0 < 10) hlarge)) (by simp [Basic.writeValue])
  have hsaved2 := hsaved1.execBasic (.imm UnaryDecode.valueReg 0)
    (by simpa [Basic.writeIndex, UnaryDecode.valueReg] using
      (lt_trans (by decide : 1 < 10) hlarge)) (by simp [Basic.writeValue])
  have hsavedBound : CursorEnvelope gate wires saved := by
    have hsaved3 := hsaved2.execBasic (.imm UnaryDecode.activeReg 1)
      (by simpa [Basic.writeIndex, UnaryDecode.activeReg] using
        (lt_trans (by decide : 6 < 10) hlarge)) (by
        have h := hlarge
        simp only [Basic.writeValue]
        omega)
    simpa [saved, saveRestartStore, saveRestartOps, Basic.execList] using hsaved3
  have hsecondReady : UnaryDecode.CursorReady (inputBits gate wires).length
      secondRemaining (4 + gate.input₀) 0 saved := by
    constructor
    · simp [secondRemaining, inputBits, CircuitCode.RawGate.encode]
      omega
    · omega
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
        UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.activeReg]
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
        UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.activeReg]
    · change saved UnaryDecode.pointerReg = _
      rw [show saved UnaryDecode.pointerReg = first UnaryDecode.pointerReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
            UnaryDecode.pointerReg, UnaryDecode.activeReg,
            UnaryDecode.inputBase]]
      rw [hfirstPointer]
      omega
    · change saved UnaryDecode.remainingReg = secondRemaining.length
      rw [show saved UnaryDecode.remainingReg = first UnaryDecode.remainingReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
            UnaryDecode.remainingReg, UnaryDecode.activeReg,
            UnaryDecode.inputBase]]
      exact hfirstRemaining
    · change saved UnaryDecode.oneReg = 1
      rw [show saved UnaryDecode.oneReg = first UnaryDecode.oneReg by
        apply saveRestart_apply_of_ne <;>
          simp [savedInput0Reg, UnaryDecode.verdictReg, UnaryDecode.valueReg,
            UnaryDecode.oneReg, UnaryDecode.activeReg,
            UnaryDecode.inputBase]]
      exact hfirstOne
    · simp [saved, saveRestartStore, saveRestartOps, Basic.execList, Basic.exec,
        UnaryDecode.verdictReg, UnaryDecode.valueReg, UnaryDecode.activeReg]
    · intro delta
      have hsavedHigh : saved
          (UnaryDecode.inputBase + (4 + gate.input₀) + delta) =
          first (UnaryDecode.inputBase + (4 + gate.input₀) + delta) := by
        apply saveRestart_high
        simp [UnaryDecode.inputBase]
        omega
      rw [hsavedHigh, hfirstFrame _ (by
        simp [UnaryDecode.inputBase]
        omega)]
      have hinput := hheaderReady.input_eq (gate.input₀ + 1 + delta)
      have hlookup : firstRemaining[gate.input₀ + 1 + delta]? =
          secondRemaining[delta]? := by
        rw [show firstRemaining = CircuitCode.NatCode.encode gate.input₀ ++
            secondRemaining by simp [firstRemaining, secondRemaining,
              List.append_assoc]]
        rw [List.getElem?_append_right (by simp)]
        simp
      rw [hlookup] at hinput
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hinput
  have hsecondBound : StoreEnvelope
      ((inputBits gate wires).length + UnaryDecode.inputBase)
      ((inputBits gate wires).length + UnaryDecode.inputBase) saved := by
    simpa [cursorBound] using hsavedBound
  obtain ⟨second, secondCost, secondSpace, hsecond, hsecondCost, hsecondSpace,
      hsecondResult, hsecondActive, _hsecondOne, hsecondFrame, hsecondFinalBound⟩ :=
    UnaryDecode.mainLoop_measured_internal hsecondReady hsecondBound
  have hdecode1 : CircuitCode.NatCode.decodePrefix? secondRemaining =
      some (gate.input₁, wires) := by
    simp [secondRemaining]
  rw [hdecode1] at hsecondResult
  simp only at hsecondResult
  have hsecondValue : second UnaryDecode.valueReg = gate.input₁ := by
    simpa using hsecondResult.2.1
  have hsecondPointer : second UnaryDecode.pointerReg = memoBase gate := by
    have hp := hsecondResult.2.2.1
    rw [hp]
    simp [memoBase, CircuitCode.RawGate.length_encode,
      UnaryDecode.inputBase]
    omega
  have hsecondRemaining : second UnaryDecode.remainingReg = wires.length :=
    hsecondResult.2.2.2
  have hsecondOp : second headerOpReg = Input.bitValue gate.opBit := by
    rw [hsecondFrame _ (by simp [headerOpReg, UnaryDecode.inputBase])]
    rw [show saved headerOpReg = first headerOpReg by
      apply saveRestart_apply_of_ne <;>
        simp [headerOpReg, savedInput0Reg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.activeReg, UnaryDecode.inputBase]]
    rw [hfirstFrame _ (by simp [headerOpReg, UnaryDecode.inputBase])]
    exact header_op gate wires
  have hsecondNegated0 : second headerNegated0Reg =
      Input.bitValue gate.negated₀ := by
    rw [hsecondFrame _ (by simp [headerNegated0Reg, UnaryDecode.inputBase])]
    rw [show saved headerNegated0Reg = first headerNegated0Reg by
      apply saveRestart_apply_of_ne <;>
        simp [headerNegated0Reg, savedInput0Reg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.activeReg, UnaryDecode.inputBase]]
    rw [hfirstFrame _ (by simp [headerNegated0Reg, UnaryDecode.inputBase])]
    exact header_negated0 gate wires
  have hsecondNegated1 : second headerNegated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [hsecondFrame _ (by simp [headerNegated1Reg, UnaryDecode.inputBase])]
    rw [show saved headerNegated1Reg = first headerNegated1Reg by
      apply saveRestart_apply_of_ne <;>
        simp [headerNegated1Reg, savedInput0Reg, UnaryDecode.verdictReg,
          UnaryDecode.valueReg, UnaryDecode.activeReg, UnaryDecode.inputBase]]
    rw [hfirstFrame _ (by simp [headerNegated1Reg, UnaryDecode.inputBase])]
    exact header_negated1 gate wires
  have hsecondInput0 : second savedInput0Reg = gate.input₀ := by
    rw [hsecondFrame _ (by simp [savedInput0Reg, UnaryDecode.inputBase])]
    rw [show saved savedInput0Reg =
        first UnaryDecode.valueReg + first UnaryDecode.activeReg by
      exact saveRestart_saved first]
    rw [hfirstValue, hfirstActive]
    omega
  let marshaled := marshalStore second
  have hready : GateEval.ReadyAt (memoBase gate) gate wires marshaled := by
    constructor
    · simp [memoBase, CircuitCode.RawGate.length_encode, GateEval.wireBase,
        UnaryDecode.inputBase]
      omega
    · change marshalStore second GateEval.opReg = _
      rw [marshal_op, hsecondOp, hsecondActive]
      omega
    · change marshalStore second GateEval.negated0Reg = _
      rw [marshal_negated0, hsecondNegated0, hsecondActive]
      omega
    · change marshalStore second GateEval.negated1Reg = _
      rw [marshal_negated1, hsecondNegated1, hsecondActive]
      omega
    · change marshalStore second GateEval.address0Reg = gate.input₀
      rw [marshal_address0, hsecondInput0, hsecondActive]
      omega
    · change marshalStore second GateEval.address1Reg = gate.input₁
      rw [marshal_address1, hsecondValue, hsecondActive]
      omega
    · change marshalStore second GateEval.wireCountReg = wires.length
      rw [marshal_wireCount, hsecondRemaining, hsecondActive]
      omega
    · change marshalStore second GateEval.baseReg = memoBase gate
      rw [marshal_base, hsecondPointer, hsecondActive]
      omega
    · intro index hindex
      change marshalStore second (memoBase gate + index) = _
      rw [marshal_high second _ (by
        simp [memoBase, CircuitCode.RawGate.length_encode,
          UnaryDecode.inputBase]
        omega)]
      rw [hsecondFrame _ (by
        simp [memoBase, CircuitCode.RawGate.length_encode,
          UnaryDecode.inputBase]
        omega)]
      change saveRestartStore first (memoBase gate + index) = _
      rw [saveRestart_high first _ (by
        simp [memoBase, CircuitCode.RawGate.length_encode,
          UnaryDecode.inputBase]
        omega)]
      rw [hfirstFrame _ (by
        simp [memoBase, CircuitCode.RawGate.length_encode,
          UnaryDecode.inputBase]
        omega)]
      rw [header_high gate wires _ (by
        simp [memoBase, CircuitCode.RawGate.length_encode,
          UnaryDecode.inputBase]
        omega)]
      exact input_wire gate wires index
  have hcursorLe : cursorBound gate wires ≤ storeBound gate wires := by
    simp [cursorBound, storeBound]
  have hwidthLe : valueWidth (cursorBound gate wires) ≤
      valueWidth (storeBound gate wires) := by
    have hsize := Nat.size_le_size hcursorLe
    simpa [valueWidth, bitlen] using Nat.add_le_add_right hsize 1
  have hspaceLe : envelopeSpace (cursorBound gate wires)
      (cursorBound gate wires) ≤
      envelopeSpace (storeBound gate wires) (storeBound gate wires) := by
    unfold envelopeSpace
    have hsize := Nat.size_le_size hcursorLe
    apply Nat.mul_le_mul hcursorLe
    simpa [bitlen] using Nat.add_le_add hsize hsize
  have hsetup := (setup_measured gate wires).1
  have hheader := (header_measured gate wires).1
  have hsave := (saveRestart_measured hfirstBound hlarge hfirstActive).1
  have hmarshal :=
    (marshal_measured hsecondFinalBound hlarge hsecondActive).1
  have hmarshaledBound : StoreEnvelope (storeBound gate wires)
      (storeBound gate wires) marshaled := by
    apply (marshal_measured hsecondFinalBound hlarge hsecondActive).2.mono
    · exact hcursorLe
    · exact hcursorLe
  have happendAddress : memoBase gate + wires.length <
      storeBound gate wires := by
    simp [memoBase, storeBound, inputBits, CircuitCode.RawGate.length_encode,
      UnaryDecode.inputBase]
    omega
  obtain ⟨final, hgate, hfinalBound, houtput, happended, _hbase, _hcount,
      hpreserved, _hframe⟩ :=
    GateEval.routine_measured_internal hready hmarshaledBound
      value0 value1 hvalue0 hvalue1 happendAddress
  have hsetup' := hsetup.weaken
    (Nat.mul_le_mul_left 20 hwidthLe) hspaceLe
  have hheader' := hheader.weaken
    (Nat.mul_le_mul_left 36 hwidthLe) hspaceLe
  have hfirstCost' : UnaryDecode.timeBound (inputBits gate wires).length ≤
      96 * ((inputBits gate wires).length + 1) *
        valueWidth (storeBound gate wires) := by
    rw [UnaryDecode.timeBound]
    apply Nat.mul_le_mul_left
    exact hwidthLe
  have hfirst' : MeasuredRuns UnaryDecode.mainLoop (headerStore gate wires)
      first (UnaryDecode.loopStepCount firstRemaining)
      (96 * ((inputBits gate wires).length + 1) *
        valueWidth (storeBound gate wires))
      (envelopeSpace (storeBound gate wires) (storeBound gate wires)) :=
    ⟨firstCost, firstSpace, hfirst, le_trans hfirstCost hfirstCost',
      le_trans hfirstSpace (by
        simpa [UnaryDecode.spaceBound, envelopeSpace, cursorBound, two_mul]
          using hspaceLe)⟩
  have hsave' := hsave.weaken
    (Nat.mul_le_mul_left 16 hwidthLe) hspaceLe
  have hsecond' : MeasuredRuns UnaryDecode.mainLoop saved
      second (UnaryDecode.loopStepCount secondRemaining)
      (96 * ((inputBits gate wires).length + 1) *
        valueWidth (storeBound gate wires))
      (envelopeSpace (storeBound gate wires) (storeBound gate wires)) :=
    ⟨secondCost, secondSpace, hsecond, le_trans hsecondCost hfirstCost',
      le_trans hsecondSpace (by
        simpa [UnaryDecode.spaceBound, envelopeSpace, cursorBound, two_mul]
          using hspaceLe)⟩
  have hmarshal' := hmarshal.weaken
    (Nat.mul_le_mul_left 28 hwidthLe) hspaceLe
  have hrun := hsetup'.seq (hheader'.seq (hfirst'.seq
    (hsave'.seq (hsecond'.seq (hmarshal'.seq hgate)))))
  have hsteps :
      UnaryDecode.setupOps.length +
          (headerOps.length + (UnaryDecode.loopStepCount firstRemaining +
            (saveRestartOps.length +
              (UnaryDecode.loopStepCount secondRemaining +
                (marshalOps.length + GateEval.stepCount))))) =
        stepCount gate := by
    simp [UnaryDecode.setupOps, headerOps, saveRestartOps, marshalOps,
      UnaryDecode.loopStepCount, hdecode0, hdecode1, GateEval.stepCount,
      stepCount]
    omega
  have hrun' : MeasuredRuns program (inputStore gate wires) final
      (UnaryDecode.setupOps.length +
        (headerOps.length + (UnaryDecode.loopStepCount firstRemaining +
          (saveRestartOps.length +
            (UnaryDecode.loopStepCount secondRemaining +
              (marshalOps.length + GateEval.stepCount))))))
      (20 * valueWidth (storeBound gate wires) +
        (36 * valueWidth (storeBound gate wires) +
          (96 * ((inputBits gate wires).length + 1) *
            valueWidth (storeBound gate wires) +
            (16 * valueWidth (storeBound gate wires) +
              (96 * ((inputBits gate wires).length + 1) *
                valueWidth (storeBound gate wires) +
                (28 * valueWidth (storeBound gate wires) +
                  80 * valueWidth (storeBound gate wires)))))))
      (envelopeSpace (storeBound gate wires) (storeBound gate wires)) := by
    simpa [program, UnaryDecode.setup, setupStore, saved, marshaled,
      saveRestartStore, marshalStore] using! hrun
  have hcostLe :
      20 * valueWidth (storeBound gate wires) +
          (36 * valueWidth (storeBound gate wires) +
            (96 * ((inputBits gate wires).length + 1) *
              valueWidth (storeBound gate wires) +
              (16 * valueWidth (storeBound gate wires) +
                (96 * ((inputBits gate wires).length + 1) *
                  valueWidth (storeBound gate wires) +
                  (28 * valueWidth (storeBound gate wires) +
                    80 * valueWidth (storeBound gate wires)))))) ≤
        timeBound gate wires := by
    rw [timeBound]
    change _ ≤ 512 * ((inputBits gate wires).length + 1) *
      valueWidth (storeBound gate wires)
    calc
      _ = (192 * ((inputBits gate wires).length + 1) + 180) *
          valueWidth (storeBound gate wires) := by ring
      _ ≤ (512 * ((inputBits gate wires).length + 1)) *
          valueWidth (storeBound gate wires) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hprogram : MeasuredRuns program (inputStore gate wires) final
      (stepCount gate) (timeBound gate wires)
      (envelopeSpace (storeBound gate wires) (storeBound gate wires)) := by
    rw [← hsteps]
    exact hrun'.weakenCost hcostLe
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hprogram
  have hspaceBound : space ≤ spaceBound gate wires := by
    simpa [spaceBound, envelopeSpace, two_mul] using hspace
  exact ⟨final, cost, space, hexec, hcost, hspaceBound,
    houtput, happended, hpreserved⟩

theorem program_exec_internal (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final (stepCount gate) cost space ∧
      final GateEval.outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (memoBase gate + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (memoBase gate + index) = Input.bitValue wires[index] := by
  obtain ⟨final, cost, space, hexec, _hcost, _hspace,
      houtput, happended, hpreserved⟩ :=
    program_measured_internal gate wires value0 value1 hvalue0 hvalue1
  exact ⟨final, cost, space, hexec, houtput, happended, hpreserved⟩

end GateStep

end Structured

end RAM

end Complexity
