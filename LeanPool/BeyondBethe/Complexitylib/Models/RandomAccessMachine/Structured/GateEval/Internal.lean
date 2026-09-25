/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import Mathlib.Algebra.Order.Sub.Basic
public import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Structured RAM decoded-gate evaluator — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateEval

open Internal

private abbrev StoreBound (wireCount : ℕ) (store : Store) : Prop :=
  StoreEnvelope (wireCount + wireBase + 1) (wireCount + wireBase + 1) store

private abbrev width (wireCount : ℕ) : ℕ :=
  valueWidth (wireCount + wireBase + 1)

private abbrev resourceSpace (wireCount : ℕ) : ℕ :=
  envelopeSpace (wireCount + wireBase + 1) (wireCount + wireBase + 1)

private theorem envelopeSpace_eq_spaceBound (wireCount : ℕ) :
    resourceSpace wireCount = spaceBound wireCount := by
  simp [resourceSpace, envelopeSpace, spaceBound, two_mul]

private theorem inputStore_bound (gate : CircuitCode.RawGate) (wires : List Bool)
    (hgate : gate.WellFormedAt wires.length) :
    StoreBound wires.length (inputStore gate wires) := by
  have hbits : StoreBound wires.length
      (Input.bitStore wireCountReg wireBase wires) := by
    apply Input.bitStoreEnvelope
    · simp [wireCountReg, wireBase]
    · simp [wireBase]
      omega
    · omega
    · simp [wireBase]
  have hop := hbits.update (index := opReg) (value := Input.bitValue gate.opBit)
    (by simp [opReg, wireBase]) (by cases gate.opBit <;> simp [wireBase])
  have hneg0 := hop.update (index := negated0Reg)
    (value := Input.bitValue gate.negated₀) (by simp [negated0Reg, wireBase])
    (by cases gate.negated₀ <;> simp [wireBase])
  have hneg1 := hneg0.update (index := negated1Reg)
    (value := Input.bitValue gate.negated₁) (by simp [negated1Reg, wireBase])
    (by cases gate.negated₁ <;> simp [wireBase])
  have haddress0 := hneg1.update (index := address0Reg) (value := gate.input₀)
    (by simp [address0Reg, wireBase]) (by
      have hinput := hgate.1
      simp [wireBase]
      omega)
  have haddress1 := haddress0.update (index := address1Reg) (value := gate.input₁)
    (by simp [address1Reg, wireBase]) (by
      have hinput := hgate.2
      simp [wireBase]
      omega)
  have hbase := haddress1.update (index := baseReg) (value := wireBase)
    (by simp [baseReg, wireBase]) (by simp [wireBase])
  simpa [inputStore] using hbase

private def addressed0 (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add address0Reg address0Reg baseReg).exec (inputStore gate wires)

private def addressed (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList addressOps (inputStore gate wires)

private def loaded0 (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.load value0Reg address0Reg).exec (addressed gate wires)

private def loaded (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList loadOps (addressed gate wires)

private def negated0Sum (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add outputReg value0Reg negated0Reg).exec (loaded gate wires)

private def negated0Product (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.mul scratchReg value0Reg negated0Reg).exec (negated0Sum gate wires)

private def negated0Twice (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add scratchReg scratchReg scratchReg).exec (negated0Product gate wires)

private def negated0 (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList (xorOps value0Reg negated0Reg) (loaded gate wires)

private def negated1Sum (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add outputReg value1Reg negated1Reg).exec (negated0 gate wires)

private def negated1Product (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.mul scratchReg value1Reg negated1Reg).exec (negated1Sum gate wires)

private def negated1Twice (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add scratchReg scratchReg scratchReg).exec (negated1Product gate wires)

private def negated1 (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList (xorOps value1Reg negated1Reg) (negated0 gate wires)

private def evalProduct (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.mul scratchReg value0Reg value1Reg).exec (negated1 gate wires)

private def evalSum (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add outputReg value0Reg value1Reg).exec (evalProduct gate wires)

private def evalOr (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.sub outputReg outputReg scratchReg).exec (evalSum gate wires)

private def evalDelta (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.sub address0Reg outputReg scratchReg).exec (evalOr gate wires)

private def evalSelected (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.mul address0Reg opReg address0Reg).exec (evalDelta gate wires)

private def evaluated (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  Basic.execList evalOps (negated1 gate wires)

private def appendAddressed (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.add address1Reg baseReg wireCountReg).exec (evaluated gate wires)

private def finalStore (gate : CircuitCode.RawGate) (wires : List Bool) : Store :=
  (Basic.store address1Reg outputReg).exec (appendAddressed gate wires)

private def routineAddressed (store : Store) : Store :=
  Basic.execList addressOps store

private def routineLoaded (store : Store) : Store :=
  Basic.execList loadOps (routineAddressed store)

private def routineNegated0 (store : Store) : Store :=
  Basic.execList (xorOps value0Reg negated0Reg) (routineLoaded store)

private def routineNegated1 (store : Store) : Store :=
  Basic.execList (xorOps value1Reg negated1Reg) (routineNegated0 store)

private def routineEvaluated (store : Store) : Store :=
  Basic.execList evalOps (routineNegated1 store)

private def routineFinal (store : Store) : Store :=
  Basic.execList appendOps (routineEvaluated store)

private theorem inputStore_wire (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) :
    inputStore gate wires (wireBase + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0 := by
  have h1 : 11 + index ≠ 1 := by omega
  have h2 : 11 + index ≠ 2 := by omega
  have h3 : 11 + index ≠ 3 := by omega
  have h4 : 11 + index ≠ 4 := by omega
  have h5 : 11 + index ≠ 5 := by omega
  have h10 : 11 + index ≠ 10 := by omega
  simp [inputStore, h1, h2, h3, h4, h5, h10, Input.bitStore,
    wireBase, wireCountReg, opReg, negated0Reg, negated1Reg, address0Reg,
    address1Reg, baseReg]
  rfl

private theorem addressed_address0 (gate : CircuitCode.RawGate)
    (wires : List Bool) :
    addressed gate wires address0Reg = gate.input₀ + wireBase := by
  simp [addressed, addressOps, Basic.execList, Basic.exec, inputStore,
    address0Reg, address1Reg, baseReg, wireBase]

private theorem addressed_address1 (gate : CircuitCode.RawGate)
    (wires : List Bool) :
    addressed gate wires address1Reg = gate.input₁ + wireBase := by
  simp [addressed, addressOps, Basic.execList, Basic.exec, inputStore,
    address0Reg, address1Reg, baseReg, wireBase]

private theorem addressed_apply_of_ne (gate : CircuitCode.RawGate)
    (wires : List Bool) (index : ℕ) (h0 : index ≠ address0Reg)
    (h1 : index ≠ address1Reg) :
    addressed gate wires index = inputStore gate wires index := by
  simp [addressed, addressOps, Basic.execList, Basic.exec,
    Function.update_of_ne, h0, h1]

private theorem loaded_value0 (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    loaded gate wires value0Reg = Input.bitValue value := by
  have hwire := inputStore_wire gate wires gate.input₀
  have hphysical : inputStore gate wires (gate.input₀ + wireBase) =
      Input.bitValue value := by
    rw [Nat.add_comm]
    simpa [hvalue] using hwire
  have haddress : addressed gate wires 3 = gate.input₀ + 11 := by
    simpa [address0Reg, wireBase] using addressed_address0 gate wires
  have hread : addressed gate wires (gate.input₀ + 11) =
      Input.bitValue value := by
    rw [addressed_apply_of_ne gate wires]
    · simpa [wireBase] using hphysical
    · simp [address0Reg]
    · simp [address1Reg]
  simp [loaded, loadOps, Basic.execList, Basic.exec, value0Reg, value1Reg,
    address0Reg, address1Reg, haddress, hread]

private theorem loaded_value1 (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₁]? = some value) :
    loaded gate wires value1Reg = Input.bitValue value := by
  have hwire := inputStore_wire gate wires gate.input₁
  have hphysical : inputStore gate wires (gate.input₁ + wireBase) =
      Input.bitValue value := by
    rw [Nat.add_comm]
    simpa [hvalue] using hwire
  have haddress : addressed gate wires 4 = gate.input₁ + 11 := by
    simpa [address1Reg, wireBase] using addressed_address1 gate wires
  have hread : addressed gate wires (gate.input₁ + 11) =
      Input.bitValue value := by
    rw [addressed_apply_of_ne gate wires]
    · simpa [wireBase] using hphysical
    · simp [address0Reg]
    · simp [address1Reg]
  simp [loaded, loadOps, Basic.execList, Basic.exec, value0Reg, value1Reg,
    address0Reg, address1Reg, haddress, hread]

private theorem inputStore_op (gate : CircuitCode.RawGate) (wires : List Bool) :
    inputStore gate wires opReg = Input.bitValue gate.opBit := by
  simp [inputStore, opReg, negated0Reg, negated1Reg, address0Reg, address1Reg,
    baseReg, Input.bitValue]

private theorem inputStore_negated0 (gate : CircuitCode.RawGate)
    (wires : List Bool) :
    inputStore gate wires negated0Reg = Input.bitValue gate.negated₀ := by
  simp [inputStore, opReg, negated0Reg, negated1Reg, address0Reg, address1Reg,
    baseReg, Input.bitValue]

private theorem inputStore_negated1 (gate : CircuitCode.RawGate)
    (wires : List Bool) :
    inputStore gate wires negated1Reg = Input.bitValue gate.negated₁ := by
  simp [inputStore, opReg, negated0Reg, negated1Reg, address0Reg, address1Reg,
    baseReg, Input.bitValue]

private theorem address_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics addressOps) (inputStore gate wires)
        (addressed gate wires) 2 (8 * width wires.length)
        (resourceSpace wires.length) ∧
      StoreBound wires.length (addressed gate wires) := by
  have hinitial := inputStore_bound gate wires hgate
  have hfirst : StoreBound wires.length (addressed0 gate wires) := by
    apply hinitial.execBasic (.add address0Reg address0Reg baseReg)
    · simp [address0Reg, wireBase]
    · have hinput := hgate.1
      simp [Internal.Basic.writeValue, inputStore, address0Reg, address1Reg,
        baseReg, wireBase, opReg, negated0Reg, negated1Reg]
      omega
  have hfinal : StoreBound wires.length (addressed gate wires) := by
    have heq : addressed gate wires =
        (Basic.add address1Reg address1Reg baseReg).exec (addressed0 gate wires) := by
      rfl
    rw [heq]
    apply hfirst.execBasic (.add address1Reg address1Reg baseReg)
    · simp [address1Reg, wireBase]
    · have hinput := hgate.2
      simp [Internal.Basic.writeValue, addressed0, Basic.exec, inputStore,
        address0Reg, address1Reg, baseReg, wireBase, opReg, negated0Reg,
        negated1Reg]
      omega
  have hrun0 := MeasuredRuns.basicEnvelope
    (.add address0Reg address0Reg baseReg) (inputStore gate wires) hinitial hfirst
  have hrun1 := MeasuredRuns.basicEnvelope
    (.add address1Reg address1Reg baseReg) (addressed0 gate wires) hfirst (by
      simpa only [addressed, addressOps, Basic.execList] using! hfinal)
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq hrun1
  convert! hrun using 1
  ring

private theorem load_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics loadOps) (addressed gate wires) (loaded gate wires)
        2 (8 * width wires.length) (resourceSpace wires.length) ∧
      StoreBound wires.length (loaded gate wires) := by
  have hinitial := (address_measured gate wires hgate).2
  have hfirst : StoreBound wires.length (loaded0 gate wires) := by
    apply hinitial.execBasic (.load value0Reg address0Reg)
    · simp [value0Reg, wireBase]
    · simpa [Internal.Basic.writeValue] using
        hinitial.value_le (addressed gate wires address0Reg)
  have hfinal : StoreBound wires.length (loaded gate wires) := by
    have heq : loaded gate wires =
        (Basic.load value1Reg address1Reg).exec (loaded0 gate wires) := by rfl
    rw [heq]
    apply hfirst.execBasic (.load value1Reg address1Reg)
    · simp [value1Reg, wireBase]
    · simpa [Internal.Basic.writeValue] using
        hfirst.value_le (loaded0 gate wires address1Reg)
  have hrun0 := MeasuredRuns.basicEnvelope (.load value0Reg address0Reg)
    (addressed gate wires) hinitial hfirst
  have hrun1 := MeasuredRuns.basicEnvelope (.load value1Reg address1Reg)
    (loaded0 gate wires) hfirst (by
      simpa only [loaded, loadOps, Basic.execList] using! hfinal)
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq hrun1
  convert! hrun using 1
  ring

private theorem negated0_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics (xorOps value0Reg negated0Reg)) (loaded gate wires)
        (negated0 gate wires) 4 (16 * width wires.length)
        (resourceSpace wires.length) ∧
      StoreBound wires.length (negated0 gate wires) := by
  have hinitial := (load_measured gate wires hgate).2
  have hvalueEq := loaded_value0 gate wires value hvalue
  have hnegatedEq : loaded gate wires negated0Reg =
      Input.bitValue gate.negated₀ := by
    rw [show loaded gate wires negated0Reg = addressed gate wires negated0Reg by
      simp [loaded, loadOps, Basic.execList, Basic.exec, negated0Reg,
        value0Reg, value1Reg]]
    rw [addressed_apply_of_ne gate wires]
    · exact inputStore_negated0 gate wires
    · simp [negated0Reg, address0Reg]
    · simp [negated0Reg, address1Reg]
  have hvalueEq' : loaded gate wires 6 = Input.bitValue value := by
    simpa [value0Reg] using hvalueEq
  have hnegatedEq' : loaded gate wires 1 = Input.bitValue gate.negated₀ := by
    simpa [negated0Reg] using hnegatedEq
  have hsum : StoreBound wires.length (negated0Sum gate wires) := by
    apply hinitial.execBasic (.add outputReg value0Reg negated0Reg)
    · simp [outputReg, wireBase]
    · change loaded gate wires 6 + loaded gate wires 1 ≤
        wires.length + wireBase + 1
      rw [hvalueEq', hnegatedEq']
      cases value <;> cases gate.negated₀ <;> simp [wireBase]
  have hproduct : StoreBound wires.length (negated0Product gate wires) := by
    apply hsum.execBasic (.mul scratchReg value0Reg negated0Reg)
    · simp [scratchReg, wireBase]
    · change negated0Sum gate wires value0Reg *
          negated0Sum gate wires negated0Reg ≤ wires.length + wireBase + 1
      simp [negated0Sum, Basic.exec, value0Reg, negated0Reg, outputReg,
        hvalueEq', hnegatedEq']
      cases value <;> cases gate.negated₀ <;> simp [wireBase]
  have htwice : StoreBound wires.length (negated0Twice gate wires) := by
    apply hproduct.execBasic (.add scratchReg scratchReg scratchReg)
    · simp [scratchReg, wireBase]
    · change negated0Product gate wires scratchReg +
          negated0Product gate wires scratchReg ≤ wires.length + wireBase + 1
      simp [negated0Product, negated0Sum, Basic.exec, value0Reg, negated0Reg,
        outputReg, scratchReg, hvalueEq', hnegatedEq']
      cases value <;> cases gate.negated₀ <;> simp [wireBase]
  have hfinal : StoreBound wires.length (negated0 gate wires) := by
    have heq : negated0 gate wires =
        (Basic.sub value0Reg outputReg scratchReg).exec
          (negated0Twice gate wires) := by rfl
    rw [heq]
    apply htwice.execBasic (.sub value0Reg outputReg scratchReg)
    · simp [value0Reg, wireBase]
    · exact Nat.le_trans (Nat.sub_le _ _) (htwice.value_le outputReg)
  have hrun0 := MeasuredRuns.basicEnvelope (.add outputReg value0Reg negated0Reg)
    (loaded gate wires) hinitial hsum
  have hrun1 := MeasuredRuns.basicEnvelope (.mul scratchReg value0Reg negated0Reg)
    (negated0Sum gate wires) hsum hproduct
  have hrun2 := MeasuredRuns.basicEnvelope (.add scratchReg scratchReg scratchReg)
    (negated0Product gate wires) hproduct htwice
  have hrun3 := MeasuredRuns.basicEnvelope (.sub value0Reg outputReg scratchReg)
    (negated0Twice gate wires) htwice (by
      simpa only [negated0, xorOps, Basic.execList] using! hfinal)
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq (hrun1.seq (hrun2.seq hrun3))
  convert! hrun using 1
  ring

private theorem loaded_apply_of_ne (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) (h0 : index ≠ value0Reg) (h1 : index ≠ value1Reg)
    (ha0 : index ≠ address0Reg) (ha1 : index ≠ address1Reg) :
    loaded gate wires index = inputStore gate wires index := by
  rw [show loaded gate wires index = addressed gate wires index by
    simp [loaded, loadOps, Basic.execList, Basic.exec, Function.update_of_ne,
      h0, h1]]
  exact addressed_apply_of_ne gate wires index ha0 ha1

private theorem negated0_value (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    negated0 gate wires value0Reg =
      Input.bitValue (gate.negated₀.xor value) := by
  have hloadedValue := loaded_value0 gate wires value hvalue
  have hloadedNegated : loaded gate wires negated0Reg =
      Input.bitValue gate.negated₀ := by
    rw [loaded_apply_of_ne gate wires]
    · exact inputStore_negated0 gate wires
    · simp [negated0Reg, value0Reg]
    · simp [negated0Reg, value1Reg]
    · simp [negated0Reg, address0Reg]
    · simp [negated0Reg, address1Reg]
  have hloadedValue' : loaded gate wires 6 = Input.bitValue value := by
    simpa [value0Reg] using hloadedValue
  have hloadedNegated' : loaded gate wires 1 = Input.bitValue gate.negated₀ := by
    simpa [negated0Reg] using hloadedNegated
  generalize hnegated : gate.negated₀ = negated
  cases negated <;> cases value <;>
    simp [negated0, xorOps, Basic.execList, Basic.exec, Input.bitValue,
      value0Reg, outputReg, scratchReg, negated0Reg, hnegated,
      hloadedValue', hloadedNegated']

private theorem negated0_apply_of_ne (gate : CircuitCode.RawGate)
    (wires : List Bool) (index : ℕ) (hvalue : index ≠ value0Reg)
    (houtput : index ≠ outputReg) (hscratch : index ≠ scratchReg) :
    negated0 gate wires index = loaded gate wires index := by
  simp [negated0, xorOps, Basic.execList, Basic.exec, Function.update_of_ne,
    hvalue, houtput, hscratch]

private theorem negated1_value (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₁]? = some value) :
    negated1 gate wires value1Reg =
      Input.bitValue (gate.negated₁.xor value) := by
  have hloadedValue := loaded_value1 gate wires value hvalue
  have hnegated0Value : negated0 gate wires value1Reg = Input.bitValue value := by
    rw [negated0_apply_of_ne gate wires]
    · exact hloadedValue
    · simp [value0Reg, value1Reg]
    · simp [value1Reg, outputReg]
    · simp [value1Reg, scratchReg]
  have hloadedNegated : loaded gate wires negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [loaded_apply_of_ne gate wires]
    · exact inputStore_negated1 gate wires
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, value1Reg]
    · simp [negated1Reg, address0Reg]
    · simp [negated1Reg, address1Reg]
  have hnegatedBit : negated0 gate wires negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [negated0_apply_of_ne gate wires]
    · exact hloadedNegated
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, outputReg]
    · simp [negated1Reg, scratchReg]
  have hnegated0Value' : negated0 gate wires 7 = Input.bitValue value := by
    simpa [value1Reg] using hnegated0Value
  have hnegatedBit' : negated0 gate wires 2 = Input.bitValue gate.negated₁ := by
    simpa [negated1Reg] using hnegatedBit
  generalize hnegated : gate.negated₁ = negated
  cases negated <;> cases value <;>
    simp [negated1, xorOps, Basic.execList, Basic.exec, Input.bitValue,
      value1Reg, outputReg, scratchReg, negated1Reg, hnegated,
      hnegated0Value', hnegatedBit']

private theorem negated1_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics (xorOps value1Reg negated1Reg)) (negated0 gate wires)
        (negated1 gate wires) 4 (16 * width wires.length)
        (resourceSpace wires.length) ∧
      StoreBound wires.length (negated1 gate wires) := by
  have hinitial := (negated0_measured gate wires value0 hvalue0 hgate).2
  have hloadedValue := loaded_value1 gate wires value1 hvalue1
  have hvalueEq : negated0 gate wires value1Reg = Input.bitValue value1 := by
    rw [negated0_apply_of_ne gate wires]
    · exact hloadedValue
    · simp [value1Reg, value0Reg]
    · simp [value1Reg, outputReg]
    · simp [value1Reg, scratchReg]
  have hloadedNegated : loaded gate wires negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [loaded_apply_of_ne gate wires]
    · exact inputStore_negated1 gate wires
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, value1Reg]
    · simp [negated1Reg, address0Reg]
    · simp [negated1Reg, address1Reg]
  have hnegatedEq : negated0 gate wires negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [negated0_apply_of_ne gate wires]
    · exact hloadedNegated
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, outputReg]
    · simp [negated1Reg, scratchReg]
  have hvalueEq' : negated0 gate wires 7 = Input.bitValue value1 := by
    simpa [value1Reg] using hvalueEq
  have hnegatedEq' : negated0 gate wires 2 = Input.bitValue gate.negated₁ := by
    simpa [negated1Reg] using hnegatedEq
  have hsum : StoreBound wires.length (negated1Sum gate wires) := by
    apply hinitial.execBasic (.add outputReg value1Reg negated1Reg)
    · simp [outputReg, wireBase]
    · change negated0 gate wires 7 + negated0 gate wires 2 ≤
        wires.length + wireBase + 1
      rw [hvalueEq', hnegatedEq']
      cases value1 <;> cases gate.negated₁ <;> simp [wireBase]
  have hproduct : StoreBound wires.length (negated1Product gate wires) := by
    apply hsum.execBasic (.mul scratchReg value1Reg negated1Reg)
    · simp [scratchReg, wireBase]
    · change negated1Sum gate wires value1Reg *
          negated1Sum gate wires negated1Reg ≤ wires.length + wireBase + 1
      simp [negated1Sum, Basic.exec, value1Reg, negated1Reg, outputReg,
        hvalueEq', hnegatedEq']
      cases value1 <;> cases gate.negated₁ <;> simp [wireBase]
  have htwice : StoreBound wires.length (negated1Twice gate wires) := by
    apply hproduct.execBasic (.add scratchReg scratchReg scratchReg)
    · simp [scratchReg, wireBase]
    · change negated1Product gate wires scratchReg +
          negated1Product gate wires scratchReg ≤ wires.length + wireBase + 1
      simp [negated1Product, negated1Sum, Basic.exec, value1Reg, negated1Reg,
        outputReg, scratchReg, hvalueEq', hnegatedEq']
      cases value1 <;> cases gate.negated₁ <;> simp [wireBase]
  have hfinal : StoreBound wires.length (negated1 gate wires) := by
    have heq : negated1 gate wires =
        (Basic.sub value1Reg outputReg scratchReg).exec
          (negated1Twice gate wires) := by rfl
    rw [heq]
    apply htwice.execBasic (.sub value1Reg outputReg scratchReg)
    · simp [value1Reg, wireBase]
    · exact Nat.le_trans (Nat.sub_le _ _) (htwice.value_le outputReg)
  have hrun0 := MeasuredRuns.basicEnvelope (.add outputReg value1Reg negated1Reg)
    (negated0 gate wires) hinitial hsum
  have hrun1 := MeasuredRuns.basicEnvelope (.mul scratchReg value1Reg negated1Reg)
    (negated1Sum gate wires) hsum hproduct
  have hrun2 := MeasuredRuns.basicEnvelope (.add scratchReg scratchReg scratchReg)
    (negated1Product gate wires) hproduct htwice
  have hrun3 := MeasuredRuns.basicEnvelope (.sub value1Reg outputReg scratchReg)
    (negated1Twice gate wires) htwice (by
      simpa only [negated1, xorOps, Basic.execList] using! hfinal)
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq (hrun1.seq (hrun2.seq hrun3))
  convert! hrun using 1
  ring

private theorem negated1_value0 (gate : CircuitCode.RawGate) (wires : List Bool)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    negated1 gate wires value0Reg =
      Input.bitValue (gate.negated₀.xor value) := by
  rw [show negated1 gate wires value0Reg = negated0 gate wires value0Reg by
    simp [negated1, xorOps, Basic.execList, Basic.exec, value0Reg, value1Reg,
      outputReg, scratchReg]]
  exact negated0_value gate wires value hvalue

private theorem negated1_apply_of_ne (gate : CircuitCode.RawGate)
    (wires : List Bool) (index : ℕ) (hvalue : index ≠ value1Reg)
    (houtput : index ≠ outputReg) (hscratch : index ≠ scratchReg) :
    negated1 gate wires index = negated0 gate wires index := by
  simp [negated1, xorOps, Basic.execList, Basic.exec, Function.update_of_ne,
    hvalue, houtput, hscratch]

private theorem negated1_op (gate : CircuitCode.RawGate) (wires : List Bool) :
    negated1 gate wires opReg = Input.bitValue gate.opBit := by
  rw [negated1_apply_of_ne gate wires]
  · rw [negated0_apply_of_ne gate wires]
    · rw [loaded_apply_of_ne gate wires]
      · exact inputStore_op gate wires
      · simp [opReg, value0Reg]
      · simp [opReg, value1Reg]
      · simp [opReg, address0Reg]
      · simp [opReg, address1Reg]
    · simp [opReg, value0Reg]
    · simp [opReg, outputReg]
    · simp [opReg, scratchReg]
  · simp [opReg, value1Reg]
  · simp [opReg, outputReg]
  · simp [opReg, scratchReg]

private theorem evaluated_output (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    evaluated gate wires outputReg = Input.bitValue (gate.eval value0 value1) := by
  have hvalue0' := negated1_value0 gate wires value0 hvalue0
  have hvalue1' := negated1_value gate wires value1 hvalue1
  have hop := negated1_op gate wires
  have hvalue0'' : negated1 gate wires 6 =
      Input.bitValue (gate.negated₀.xor value0) := by
    simpa [value0Reg] using hvalue0'
  have hvalue1'' : negated1 gate wires 7 =
      Input.bitValue (gate.negated₁.xor value1) := by
    simpa [value1Reg] using hvalue1'
  have hop' : negated1 gate wires 0 = Input.bitValue gate.opBit := by
    simpa [opReg] using hop
  rcases gate with ⟨op, input0, input1, negated0, negated1⟩
  cases op <;> cases negated0 <;> cases negated1 <;>
    cases value0 <;> cases value1 <;>
    simp [evaluated, evalOps, Basic.execList, Basic.exec, Input.bitValue,
      CircuitCode.RawGate.eval, CircuitCode.RawGate.opBit, opReg, value0Reg,
      value1Reg, outputReg, scratchReg, address0Reg, hvalue0'', hvalue1'', hop']

private theorem eval_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics evalOps) (negated1 gate wires) (evaluated gate wires)
        6 (24 * width wires.length) (resourceSpace wires.length) ∧
      StoreBound wires.length (evaluated gate wires) := by
  have hinitial :=
    (negated1_measured gate wires value0 value1 hvalue0 hvalue1 hgate).2
  have hvalue0Eq := negated1_value0 gate wires value0 hvalue0
  have hvalue1Eq := negated1_value gate wires value1 hvalue1
  have hopEq := negated1_op gate wires
  have hvalue0Eq' : negated1 gate wires 6 =
      Input.bitValue (gate.negated₀.xor value0) := by
    simpa [value0Reg] using hvalue0Eq
  have hvalue1Eq' : negated1 gate wires 7 =
      Input.bitValue (gate.negated₁.xor value1) := by
    simpa [value1Reg] using hvalue1Eq
  have hopEq' : negated1 gate wires 0 = Input.bitValue gate.opBit := by
    simpa [opReg] using hopEq
  have hproduct : StoreBound wires.length (evalProduct gate wires) := by
    apply hinitial.execBasic (.mul scratchReg value0Reg value1Reg)
    · simp [scratchReg, wireBase]
    · change negated1 gate wires value0Reg * negated1 gate wires value1Reg ≤
        wires.length + wireBase + 1
      rw [hvalue0Eq, hvalue1Eq]
      cases gate.negated₀ <;> cases gate.negated₁ <;>
        cases value0 <;> cases value1 <;> simp [wireBase]
  have hsum : StoreBound wires.length (evalSum gate wires) := by
    apply hproduct.execBasic (.add outputReg value0Reg value1Reg)
    · simp [outputReg, wireBase]
    · change evalProduct gate wires value0Reg + evalProduct gate wires value1Reg ≤
        wires.length + wireBase + 1
      simp [evalProduct, Basic.exec, value0Reg, value1Reg, scratchReg,
        hvalue0Eq', hvalue1Eq']
      cases gate.negated₀ <;> cases gate.negated₁ <;>
        cases value0 <;> cases value1 <;> simp [wireBase]
  have hsumOutput : evalSum gate wires outputReg ≤ 2 := by
    simp [evalSum, evalProduct, Basic.exec, outputReg, value0Reg, value1Reg,
      scratchReg, hvalue0Eq', hvalue1Eq']
    cases gate.negated₀ <;> cases gate.negated₁ <;>
      cases value0 <;> cases value1 <;> simp
  have hor : StoreBound wires.length (evalOr gate wires) := by
    apply hsum.execBasic (.sub outputReg outputReg scratchReg)
    · simp [outputReg, wireBase]
    · exact le_trans (Nat.sub_le _ _) (le_trans hsumOutput (by simp [wireBase]))
  have horOutput : evalOr gate wires outputReg ≤ 2 := by
    exact le_trans (Nat.sub_le _ _) hsumOutput
  have hdelta : StoreBound wires.length (evalDelta gate wires) := by
    apply hor.execBasic (.sub address0Reg outputReg scratchReg)
    · simp [address0Reg, wireBase]
    · exact le_trans (Nat.sub_le _ _) (le_trans horOutput (by simp [wireBase]))
  have hdeltaValue : evalDelta gate wires address0Reg ≤ 2 := by
    exact le_trans (Nat.sub_le _ _) horOutput
  have hselected : StoreBound wires.length (evalSelected gate wires) := by
    apply hdelta.execBasic (.mul address0Reg opReg address0Reg)
    · simp [address0Reg, wireBase]
    · have hop : evalDelta gate wires opReg = Input.bitValue gate.opBit := by
        simp [evalDelta, evalOr, evalSum, evalProduct, Basic.exec, opReg,
          address0Reg, outputReg, scratchReg, value0Reg, value1Reg, hopEq']
      change evalDelta gate wires opReg * evalDelta gate wires address0Reg ≤
        wires.length + wireBase + 1
      rw [hop]
      cases gate.opBit <;> simp [Input.bitValue]
      exact le_trans hdeltaValue (by simp [wireBase])
  have hfinal : StoreBound wires.length (evaluated gate wires) := by
    have heq : evaluated gate wires =
        (Basic.sub outputReg outputReg address0Reg).exec
          (evalSelected gate wires) := by rfl
    rw [heq]
    apply hselected.execBasic (.sub outputReg outputReg address0Reg)
    · simp [outputReg, wireBase]
    · exact Nat.le_trans (Nat.sub_le _ _) (hselected.value_le outputReg)
  have hrun0 := MeasuredRuns.basicEnvelope (.mul scratchReg value0Reg value1Reg)
    (negated1 gate wires) hinitial hproduct
  have hrun1 := MeasuredRuns.basicEnvelope (.add outputReg value0Reg value1Reg)
    (evalProduct gate wires) hproduct hsum
  have hrun2 := MeasuredRuns.basicEnvelope (.sub outputReg outputReg scratchReg)
    (evalSum gate wires) hsum hor
  have hrun3 := MeasuredRuns.basicEnvelope (.sub address0Reg outputReg scratchReg)
    (evalOr gate wires) hor hdelta
  have hrun4 := MeasuredRuns.basicEnvelope (.mul address0Reg opReg address0Reg)
    (evalDelta gate wires) hdelta hselected
  have hrun5 := MeasuredRuns.basicEnvelope (.sub outputReg outputReg address0Reg)
    (evalSelected gate wires) hselected (by
      simpa only [evaluated, evalOps, Basic.execList] using! hfinal)
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq (hrun1.seq (hrun2.seq (hrun3.seq (hrun4.seq hrun5))))
  convert! hrun using 1
  ring

private theorem evaluated_apply_of_ne (gate : CircuitCode.RawGate)
    (wires : List Bool) (index : ℕ) (haddress : index ≠ address0Reg)
    (houtput : index ≠ outputReg) (hscratch : index ≠ scratchReg) :
    evaluated gate wires index = negated1 gate wires index := by
  simp [evaluated, evalOps, Basic.execList, Basic.exec, Function.update_of_ne,
    haddress, houtput, hscratch]

private theorem inputStore_wireCount (gate : CircuitCode.RawGate)
    (wires : List Bool) : inputStore gate wires wireCountReg = wires.length := by
  simp [inputStore, opReg, negated0Reg, negated1Reg, address0Reg, address1Reg,
    wireCountReg, baseReg, wireBase, Input.bitStore]

private theorem inputStore_base (gate : CircuitCode.RawGate) (wires : List Bool) :
    inputStore gate wires baseReg = wireBase := by
  simp [inputStore, baseReg]

private theorem evaluated_stable (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) (ha0 : index ≠ address0Reg) (ha1 : index ≠ address1Reg)
    (hv0 : index ≠ value0Reg) (hv1 : index ≠ value1Reg)
    (hout : index ≠ outputReg) (hscratch : index ≠ scratchReg) :
    evaluated gate wires index = inputStore gate wires index := by
  rw [evaluated_apply_of_ne gate wires index ha0 hout hscratch]
  rw [negated1_apply_of_ne gate wires index hv1 hout hscratch]
  rw [negated0_apply_of_ne gate wires index hv0 hout hscratch]
  exact loaded_apply_of_ne gate wires index hv0 hv1 ha0 ha1

private theorem evaluated_wireCount (gate : CircuitCode.RawGate)
    (wires : List Bool) : evaluated gate wires wireCountReg = wires.length := by
  rw [evaluated_stable gate wires]
  · exact inputStore_wireCount gate wires
  · simp [wireCountReg, address0Reg]
  · simp [wireCountReg, address1Reg]
  · simp [wireCountReg, value0Reg]
  · simp [wireCountReg, value1Reg]
  · simp [wireCountReg, outputReg]
  · simp [wireCountReg, scratchReg]

private theorem evaluated_base (gate : CircuitCode.RawGate) (wires : List Bool) :
    evaluated gate wires baseReg = wireBase := by
  rw [evaluated_stable gate wires]
  · exact inputStore_base gate wires
  · simp [baseReg, address0Reg]
  · simp [baseReg, address1Reg]
  · simp [baseReg, value0Reg]
  · simp [baseReg, value1Reg]
  · simp [baseReg, outputReg]
  · simp [baseReg, scratchReg]

private theorem finalStore_output (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    finalStore gate wires outputReg = Input.bitValue (gate.eval value0 value1) := by
  have houtput := evaluated_output gate wires value0 value1 hvalue0 hvalue1
  have hcount := evaluated_wireCount gate wires
  have hbase := evaluated_base gate wires
  have houtput' : evaluated gate wires 8 = Input.bitValue (gate.eval value0 value1) := by
    simpa [outputReg] using houtput
  have hcount' : evaluated gate wires 5 = wires.length := by
    simpa [wireCountReg] using hcount
  have hbase' : evaluated gate wires 10 = 11 := by
    simpa [baseReg, wireBase] using hbase
  have happendAddress : appendAddressed gate wires 4 = 11 + wires.length := by
    simp [appendAddressed, Basic.exec, address1Reg, baseReg, wireCountReg,
      hcount', hbase']
  have happendOutput : appendAddressed gate wires 8 =
      Input.bitValue (gate.eval value0 value1) := by
    simpa [appendAddressed, Basic.exec, address1Reg, outputReg] using houtput'
  rw [finalStore, Basic.exec]
  change Function.update (appendAddressed gate wires)
      (appendAddressed gate wires 4) (appendAddressed gate wires 8) 8 = _
  rw [happendAddress, happendOutput]
  rw [Function.update_of_ne (by omega : 8 ≠ 11 + wires.length)]
  exact happendOutput

private theorem finalStore_appended (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    finalStore gate wires (wireBase + wires.length) =
      Input.bitValue (gate.eval value0 value1) := by
  have houtput := evaluated_output gate wires value0 value1 hvalue0 hvalue1
  have hbase' : evaluated gate wires 10 = 11 := by
    simpa [baseReg, wireBase] using evaluated_base gate wires
  have hcount' : evaluated gate wires 5 = wires.length := by
    simpa [wireCountReg] using evaluated_wireCount gate wires
  have haddress : appendAddressed gate wires address1Reg =
      wireBase + wires.length := by
    simp [appendAddressed, Basic.exec, address1Reg, baseReg, wireCountReg]
    rw [hbase', hcount']
    simp [wireBase, Nat.add_comm]
  have hsource : appendAddressed gate wires outputReg =
      Input.bitValue (gate.eval value0 value1) := by
    simpa [appendAddressed, Basic.exec, address1Reg, outputReg] using houtput
  rw [finalStore, Basic.exec]
  change Function.update (appendAddressed gate wires)
      (appendAddressed gate wires address1Reg)
      (appendAddressed gate wires outputReg) (wireBase + wires.length) = _
  rw [haddress, hsource, Function.update_self]

private theorem finalStore_wire (gate : CircuitCode.RawGate) (wires : List Bool)
    (index : ℕ) (hindex : index < wires.length) :
    finalStore gate wires (wireBase + index) = Input.bitValue wires[index] := by
  have hbase' : evaluated gate wires 10 = 11 := by
    simpa [baseReg, wireBase] using evaluated_base gate wires
  have hcount' : evaluated gate wires 5 = wires.length := by
    simpa [wireCountReg] using evaluated_wireCount gate wires
  have haddress : appendAddressed gate wires address1Reg =
      wireBase + wires.length := by
    simp [appendAddressed, Basic.exec, address1Reg, baseReg, wireCountReg]
    rw [hbase', hcount']
    simp [wireBase, Nat.add_comm]
  have hne : wireBase + index ≠ wireBase + wires.length := by omega
  rw [finalStore, Basic.exec]
  change Function.update (appendAddressed gate wires)
      (appendAddressed gate wires address1Reg)
      (appendAddressed gate wires outputReg) (wireBase + index) = _
  rw [haddress, Function.update_of_ne hne]
  have happend : appendAddressed gate wires (wireBase + index) =
      evaluated gate wires (wireBase + index) := by
    rw [appendAddressed, Basic.exec]
    simp only [wireBase, address1Reg]
    rw [Function.update_of_ne (by omega : 11 + index ≠ 4)]
  rw [happend]
  rw [evaluated_stable gate wires]
  · have hwire := inputStore_wire gate wires index
    rw [List.getElem?_eq_getElem hindex] at hwire
    exact hwire
  all_goals simp only [wireBase, address0Reg, address1Reg, value0Reg, value1Reg,
    outputReg, scratchReg]
  all_goals omega

private theorem append_measured (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    MeasuredRuns (.basics appendOps) (evaluated gate wires) (finalStore gate wires)
        2 (8 * width wires.length) (resourceSpace wires.length) ∧
      StoreBound wires.length (finalStore gate wires) := by
  have hinitial := (eval_measured gate wires value0 value1 hvalue0 hvalue1 hgate).2
  have hfirst : StoreBound wires.length (appendAddressed gate wires) := by
    apply hinitial.execBasic (.add address1Reg baseReg wireCountReg)
    · simp [address1Reg, wireBase]
    · change evaluated gate wires baseReg + evaluated gate wires wireCountReg ≤
        wires.length + wireBase + 1
      rw [evaluated_base, evaluated_wireCount]
      omega
  have hbase' : evaluated gate wires 10 = 11 := by
    simpa [baseReg, wireBase] using evaluated_base gate wires
  have hcount' : evaluated gate wires 5 = wires.length := by
    simpa [wireCountReg] using evaluated_wireCount gate wires
  have hfinal : StoreBound wires.length (finalStore gate wires) := by
    apply hfirst.execBasic (.store address1Reg outputReg)
    · change appendAddressed gate wires address1Reg <
        wires.length + wireBase + 1
      change evaluated gate wires 10 + evaluated gate wires 5 <
        wires.length + wireBase + 1
      rw [hbase', hcount']
      simp [wireBase]
      omega
    · exact hfirst.value_le outputReg
  have hrun0 := MeasuredRuns.basicEnvelope (.add address1Reg baseReg wireCountReg)
    (evaluated gate wires) hinitial hfirst
  have hrun1 := MeasuredRuns.basicEnvelope (.store address1Reg outputReg)
    (appendAddressed gate wires) hfirst hfinal
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq hrun1
  convert! hrun using 1
  ring

private theorem routineAddressed_address0 {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineAddressed store address0Reg = gate.input₀ + base := by
  change store address0Reg + store baseReg = gate.input₀ + base
  rw [hready.address0_eq, hready.base_eq]

private theorem routineAddressed_address1 {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineAddressed store address1Reg = gate.input₁ + base := by
  change store address1Reg + store baseReg = gate.input₁ + base
  rw [hready.address1_eq, hready.base_eq]

private theorem routineAddressed_apply_of_ne (store : Store) (index : ℕ)
    (h0 : index ≠ address0Reg) (h1 : index ≠ address1Reg) :
    routineAddressed store index = store index := by
  simp [routineAddressed, addressOps, Basic.execList, Basic.exec,
    Function.update_of_ne, h0, h1]

private theorem routineLoaded_value0 {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    routineLoaded store value0Reg = Input.bitValue value := by
  have hindex := List.getElem?_eq_some_iff.mp hvalue |>.1
  have hread := hready.wire_eq gate.input₀ hindex
  simp [hvalue] at hread
  have haddress := routineAddressed_address0 hready
  have hbase : wireBase ≤ base := hready.base_ge
  have hphysical : routineAddressed store (gate.input₀ + base) =
      Input.bitValue value := by
    rw [routineAddressed_apply_of_ne]
    · simpa [Nat.add_comm] using hread
    · simp only [address0Reg, wireBase] at hbase ⊢
      omega
    · simp only [address1Reg, wireBase] at hbase ⊢
      omega
  have haddress' : routineAddressed store 3 = gate.input₀ + base := by
    simpa [address0Reg] using haddress
  have hphysical' : routineAddressed store (gate.input₀ + base) =
      Input.bitValue value := hphysical
  simp [routineLoaded, loadOps, Basic.execList, Basic.exec, value0Reg,
    value1Reg, address0Reg, address1Reg, haddress', hphysical']

private theorem routineLoaded_value1 {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value : Bool) (hvalue : wires[gate.input₁]? = some value) :
    routineLoaded store value1Reg = Input.bitValue value := by
  have hindex := List.getElem?_eq_some_iff.mp hvalue |>.1
  have hread := hready.wire_eq gate.input₁ hindex
  simp [hvalue] at hread
  have haddress := routineAddressed_address1 hready
  have hbase : wireBase ≤ base := hready.base_ge
  have hphysical : routineAddressed store (gate.input₁ + base) =
      Input.bitValue value := by
    rw [routineAddressed_apply_of_ne]
    · simpa [Nat.add_comm] using hread
    · simp only [address0Reg, wireBase] at hbase ⊢
      omega
    · simp only [address1Reg, wireBase] at hbase ⊢
      omega
  have haddress' : routineAddressed store 4 = gate.input₁ + base := by
    simpa [address1Reg] using haddress
  have hphysical' : routineAddressed store (gate.input₁ + base) =
      Input.bitValue value := hphysical
  let after0 := (Basic.load value0Reg address0Reg).exec (routineAddressed store)
  have hafterAddress : after0 address1Reg = gate.input₁ + base := by
    simp [after0, Basic.exec, value0Reg, address1Reg, haddress']
  have hafterPhysical : after0 (gate.input₁ + base) = Input.bitValue value := by
    have hne : gate.input₁ + base ≠ value0Reg := by
      simp only [value0Reg, wireBase] at hbase ⊢
      omega
    simp [after0, Basic.exec, Function.update_of_ne hne, hphysical']
  change (Basic.load value1Reg address1Reg).exec after0 value1Reg =
    Input.bitValue value
  simp [Basic.exec, hafterAddress, hafterPhysical]

private theorem routineLoaded_apply_of_ne (store : Store) (index : ℕ)
    (h0 : index ≠ value0Reg) (h1 : index ≠ value1Reg)
    (ha0 : index ≠ address0Reg) (ha1 : index ≠ address1Reg) :
    routineLoaded store index = store index := by
  rw [show routineLoaded store index = routineAddressed store index by
    simp [routineLoaded, loadOps, Basic.execList, Basic.exec,
      Function.update_of_ne, h0, h1]]
  exact routineAddressed_apply_of_ne store index ha0 ha1

private theorem xor_measured {bound value negated : ℕ} {store : Store}
    (hstore : StoreEnvelope bound bound store) (hbound : 2 ≤ bound)
    (hvalue : value < bound) (houtput : outputReg < bound)
    (hscratch : scratchReg < bound)
    (hvalueOutput : value ≠ outputReg)
    (hnegatedOutput : negated ≠ outputReg)
    (valueBit negatedBit : Bool)
    (hvalueEq : store value = Input.bitValue valueBit)
    (hnegatedEq : store negated = Input.bitValue negatedBit) :
    MeasuredRuns (.basics (xorOps value negated)) store
        (Basic.execList (xorOps value negated) store) 4
        (16 * valueWidth bound) (envelopeSpace bound bound) ∧
      StoreEnvelope bound bound (Basic.execList (xorOps value negated) store) := by
  let sum := (Basic.add outputReg value negated).exec store
  let product := (Basic.mul scratchReg value negated).exec sum
  let twice := (Basic.add scratchReg scratchReg scratchReg).exec product
  have hsum : StoreEnvelope bound bound sum := by
    apply hstore.execBasic (.add outputReg value negated)
    · exact houtput
    · change store value + store negated ≤ bound
      rw [hvalueEq, hnegatedEq]
      cases valueBit <;> cases negatedBit <;> simp [Input.bitValue] <;> omega
  have hproduct : StoreEnvelope bound bound product := by
    apply hsum.execBasic (.mul scratchReg value negated)
    · exact hscratch
    · change sum value * sum negated ≤ bound
      cases valueBit <;> cases negatedBit <;>
        simp [sum, Basic.exec, Function.update_of_ne, hvalueOutput,
          hnegatedOutput, hvalueEq, hnegatedEq, Input.bitValue]
      all_goals omega
  have htwice : StoreEnvelope bound bound twice := by
    apply hproduct.execBasic (.add scratchReg scratchReg scratchReg)
    · exact hscratch
    · change product scratchReg + product scratchReg ≤ bound
      cases valueBit <;> cases negatedBit <;>
        simp [product, sum, Basic.exec, Function.update_of_ne,
          hvalueOutput, hnegatedOutput, hvalueEq, hnegatedEq,
          Input.bitValue]
      all_goals omega
  have hfinal : StoreEnvelope bound bound
      (Basic.execList (xorOps value negated) store) := by
    change StoreEnvelope bound bound
      ((Basic.sub value outputReg scratchReg).exec twice)
    apply htwice.execBasic (.sub value outputReg scratchReg)
    · exact hvalue
    · exact le_trans (Nat.sub_le _ _) (htwice.value_le outputReg)
  have hrun0 := MeasuredRuns.basicEnvelope (.add outputReg value negated)
    store hstore hsum
  have hrun1 := MeasuredRuns.basicEnvelope (.mul scratchReg value negated)
    sum hsum hproduct
  have hrun2 := MeasuredRuns.basicEnvelope (.add scratchReg scratchReg scratchReg)
    product hproduct htwice
  have hrun3 := MeasuredRuns.basicEnvelope (.sub value outputReg scratchReg)
    twice htwice hfinal
  refine ⟨?_, hfinal⟩
  have hrun := hrun0.seq (hrun1.seq (hrun2.seq hrun3))
  convert! hrun using 1
  ring

private theorem routineNegated0_value {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    routineNegated0 store value0Reg =
      Input.bitValue (gate.negated₀.xor value) := by
  have hloadedValue := routineLoaded_value0 hready value hvalue
  have hloadedNegated : routineLoaded store negated0Reg =
      Input.bitValue gate.negated₀ := by
    rw [routineLoaded_apply_of_ne]
    · exact hready.negated0_eq
    · simp [negated0Reg, value0Reg]
    · simp [negated0Reg, value1Reg]
    · simp [negated0Reg, address0Reg]
    · simp [negated0Reg, address1Reg]
  have hloadedValue' : routineLoaded store 6 = Input.bitValue value := by
    simpa [value0Reg] using hloadedValue
  have hloadedNegated' : routineLoaded store 1 =
      Input.bitValue gate.negated₀ := by
    simpa [negated0Reg] using hloadedNegated
  generalize hnegated : gate.negated₀ = negated
  cases negated <;> cases value <;>
    simp [routineNegated0, xorOps, Basic.execList, Basic.exec, Input.bitValue,
      value0Reg, outputReg, scratchReg, negated0Reg, hnegated,
      hloadedValue', hloadedNegated']

private theorem routineNegated0_apply_of_ne (store : Store) (index : ℕ)
    (hvalue : index ≠ value0Reg) (houtput : index ≠ outputReg)
    (hscratch : index ≠ scratchReg) :
    routineNegated0 store index = routineLoaded store index := by
  simp [routineNegated0, xorOps, Basic.execList, Basic.exec,
    Function.update_of_ne, hvalue, houtput, hscratch]

private theorem routineNegated1_value {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value : Bool) (hvalue : wires[gate.input₁]? = some value) :
    routineNegated1 store value1Reg =
      Input.bitValue (gate.negated₁.xor value) := by
  have hloadedValue := routineLoaded_value1 hready value hvalue
  have hnegated0Value : routineNegated0 store value1Reg = Input.bitValue value := by
    rw [routineNegated0_apply_of_ne]
    · exact hloadedValue
    · simp [value0Reg, value1Reg]
    · simp [value1Reg, outputReg]
    · simp [value1Reg, scratchReg]
  have hloadedNegated : routineLoaded store negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [routineLoaded_apply_of_ne]
    · exact hready.negated1_eq
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, value1Reg]
    · simp [negated1Reg, address0Reg]
    · simp [negated1Reg, address1Reg]
  have hnegatedBit : routineNegated0 store negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [routineNegated0_apply_of_ne]
    · exact hloadedNegated
    · simp [negated1Reg, value0Reg]
    · simp [negated1Reg, outputReg]
    · simp [negated1Reg, scratchReg]
  have hvalue' : routineNegated0 store 7 = Input.bitValue value := by
    simpa [value1Reg] using hnegated0Value
  have hnegated' : routineNegated0 store 2 = Input.bitValue gate.negated₁ := by
    simpa [negated1Reg] using hnegatedBit
  generalize hnegatedEq : gate.negated₁ = negated
  cases negated <;> cases value <;>
    simp [routineNegated1, xorOps, Basic.execList, Basic.exec, Input.bitValue,
      value1Reg, outputReg, scratchReg, negated1Reg, hnegatedEq,
      hvalue', hnegated']

private theorem routineNegated1_apply_of_ne (store : Store) (index : ℕ)
    (hvalue : index ≠ value1Reg) (houtput : index ≠ outputReg)
    (hscratch : index ≠ scratchReg) :
    routineNegated1 store index = routineNegated0 store index := by
  simp [routineNegated1, xorOps, Basic.execList, Basic.exec,
    Function.update_of_ne, hvalue, houtput, hscratch]

private theorem routineNegated1_value0 {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value : Bool) (hvalue : wires[gate.input₀]? = some value) :
    routineNegated1 store value0Reg =
      Input.bitValue (gate.negated₀.xor value) := by
  rw [routineNegated1_apply_of_ne]
  · exact routineNegated0_value hready value hvalue
  · simp [value0Reg, value1Reg]
  · simp [value0Reg, outputReg]
  · simp [value0Reg, scratchReg]

private theorem routineNegated1_op {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineNegated1 store opReg = Input.bitValue gate.opBit := by
  rw [routineNegated1_apply_of_ne]
  · rw [routineNegated0_apply_of_ne]
    · rw [routineLoaded_apply_of_ne]
      · exact hready.op_eq
      · simp [opReg, value0Reg]
      · simp [opReg, value1Reg]
      · simp [opReg, address0Reg]
      · simp [opReg, address1Reg]
    · simp [opReg, value0Reg]
    · simp [opReg, outputReg]
    · simp [opReg, scratchReg]
  · simp [opReg, value1Reg]
  · simp [opReg, outputReg]
  · simp [opReg, scratchReg]

private theorem routineEvaluated_output {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    routineEvaluated store outputReg =
      Input.bitValue (gate.eval value0 value1) := by
  have hvalue0' := routineNegated1_value0 hready value0 hvalue0
  have hvalue1' := routineNegated1_value hready value1 hvalue1
  have hop := routineNegated1_op hready
  have hvalue0'' : routineNegated1 store 6 =
      Input.bitValue (gate.negated₀.xor value0) := by
    simpa [value0Reg] using hvalue0'
  have hvalue1'' : routineNegated1 store 7 =
      Input.bitValue (gate.negated₁.xor value1) := by
    simpa [value1Reg] using hvalue1'
  have hop' : routineNegated1 store 0 = Input.bitValue gate.opBit := by
    simpa [opReg] using hop
  rcases gate with ⟨op, input0, input1, negated0, negated1⟩
  cases op <;> cases negated0 <;> cases negated1 <;>
    cases value0 <;> cases value1 <;>
    simp [routineEvaluated, evalOps, Basic.execList, Basic.exec, Input.bitValue,
      CircuitCode.RawGate.eval, CircuitCode.RawGate.opBit, opReg, value0Reg,
      value1Reg, outputReg, scratchReg, address0Reg, hvalue0'', hvalue1'', hop']

private theorem routineEvaluated_stable (store : Store) (index : ℕ)
    (ha0 : index ≠ address0Reg) (ha1 : index ≠ address1Reg)
    (hv0 : index ≠ value0Reg) (hv1 : index ≠ value1Reg)
    (hout : index ≠ outputReg) (hscratch : index ≠ scratchReg) :
    routineEvaluated store index = store index := by
  rw [show routineEvaluated store index = routineNegated1 store index by
    simp [routineEvaluated, evalOps, Basic.execList, Basic.exec,
      Function.update_of_ne, ha0, hout, hscratch]]
  rw [routineNegated1_apply_of_ne store index hv1 hout hscratch]
  rw [routineNegated0_apply_of_ne store index hv0 hout hscratch]
  exact routineLoaded_apply_of_ne store index hv0 hv1 ha0 ha1

private theorem routineEvaluated_wireCount {base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (hready : ReadyAt base gate wires store) :
    routineEvaluated store wireCountReg = wires.length := by
  rw [routineEvaluated_stable]
  · exact hready.wireCount_eq
  all_goals simp [wireCountReg, address0Reg, address1Reg, value0Reg, value1Reg,
    outputReg, scratchReg]

private theorem routineEvaluated_base {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineEvaluated store baseReg = base := by
  rw [routineEvaluated_stable]
  · exact hready.base_eq
  all_goals simp [baseReg, address0Reg, address1Reg, value0Reg, value1Reg,
    outputReg, scratchReg]

private theorem routineEvaluated_wire {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (index : ℕ) (hindex : index < wires.length) :
    routineEvaluated store (base + index) =
      match wires[index]? with
      | some bit => Input.bitValue bit
      | none => 0 := by
  rw [routineEvaluated_stable]
  · exact hready.wire_eq index hindex
  all_goals have hbase := hready.base_ge
  all_goals simp only [wireBase, address0Reg, address1Reg, value0Reg, value1Reg,
    outputReg, scratchReg] at hbase ⊢
  all_goals omega

private theorem routineFinal_output {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    routineFinal store outputReg = Input.bitValue (gate.eval value0 value1) := by
  have houtput := routineEvaluated_output hready value0 value1 hvalue0 hvalue1
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  have hbase' : routineEvaluated store 10 = base := by
    simpa [baseReg] using hbase
  have hcount' : routineEvaluated store 5 = wires.length := by
    simpa [wireCountReg] using hcount
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, baseReg, wireCountReg,
      hbase', hcount']
  have hsource : addressed outputReg =
      Input.bitValue (gate.eval value0 value1) := by
    simpa [addressed, Basic.exec, address1Reg, outputReg] using houtput
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) outputReg = _
  rw [haddress, hsource, Function.update_of_ne]
  · exact hsource
  · have hbaseGe := hready.base_ge
    simp only [outputReg, wireBase] at hbaseGe ⊢
    omega

private theorem routineFinal_appended {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    routineFinal store (base + wires.length) =
      Input.bitValue (gate.eval value0 value1) := by
  have houtput := routineEvaluated_output hready value0 value1 hvalue0 hvalue1
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  have hbase' : routineEvaluated store 10 = base := by
    simpa [baseReg] using hbase
  have hcount' : routineEvaluated store 5 = wires.length := by
    simpa [wireCountReg] using hcount
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, baseReg, wireCountReg,
      hbase', hcount']
  have hsource : addressed outputReg =
      Input.bitValue (gate.eval value0 value1) := by
    simpa [addressed, Basic.exec, address1Reg, outputReg] using houtput
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) (base + wires.length) = _
  rw [haddress, hsource, Function.update_self]

private theorem routineFinal_wire {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (index : ℕ) (hindex : index < wires.length) :
    routineFinal store (base + index) = Input.bitValue wires[index] := by
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  have hwire := routineEvaluated_wire hready index hindex
  rw [List.getElem?_eq_getElem hindex] at hwire
  have hbase' : routineEvaluated store 10 = base := by
    simpa [baseReg] using hbase
  have hcount' : routineEvaluated store 5 = wires.length := by
    simpa [wireCountReg] using hcount
  have hne : base + index ≠ base + wires.length := by omega
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, baseReg, wireCountReg,
      hbase', hcount']
  have hpreserved : addressed (base + index) =
      routineEvaluated store (base + index) := by
    have hbaseGe := hready.base_ge
    have hnotAddress : base + index ≠ address1Reg := by
      simp only [address1Reg, wireBase] at hbaseGe ⊢
      omega
    simp [addressed, Basic.exec, Function.update_of_ne hnotAddress]
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) (base + index) = _
  rw [haddress, Function.update_of_ne hne, hpreserved, hwire]

private theorem routineFinal_base {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineFinal store baseReg = base := by
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, hbase, hcount]
  have hpreserved : addressed baseReg = routineEvaluated store baseReg := by
    simp [addressed, Basic.exec, Function.update_of_ne, address1Reg, baseReg]
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) baseReg = base
  rw [haddress, Function.update_of_ne, hpreserved, hbase]
  have hbaseGe := hready.base_ge
  simp only [baseReg, wireBase] at hbaseGe ⊢
  omega

private theorem routineFinal_wireCount {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store) :
    routineFinal store wireCountReg = wires.length := by
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, hbase, hcount]
  have hpreserved : addressed wireCountReg =
      routineEvaluated store wireCountReg := by
    simp [addressed, Basic.exec, Function.update_of_ne, address1Reg,
      wireCountReg]
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) wireCountReg = wires.length
  rw [haddress, Function.update_of_ne, hpreserved, hcount]
  have hbaseGe := hready.base_ge
  simp only [wireCountReg, wireBase] at hbaseGe ⊢
  omega

private theorem routineFinal_frame {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (index : ℕ) (hhigh : wireBase ≤ index)
    (happend : index ≠ base + wires.length) :
    routineFinal store index = store index := by
  have hevaluated : routineEvaluated store index = store index := by
    rw [routineEvaluated_stable]
    all_goals simp only [wireBase, address0Reg, address1Reg, value0Reg,
      value1Reg, outputReg, scratchReg] at hhigh ⊢
    all_goals omega
  have hbase := routineEvaluated_base hready
  have hcount := routineEvaluated_wireCount hready
  let addressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have haddress : addressed address1Reg = base + wires.length := by
    simp [addressed, Basic.exec, address1Reg, hbase, hcount]
  have haddressed : addressed index = routineEvaluated store index := by
    have hne : index ≠ address1Reg := by
      simp only [wireBase, address1Reg] at hhigh ⊢
      omega
    simp [addressed, Basic.exec, Function.update_of_ne hne]
  rw [routineFinal, appendOps, Basic.execList]
  change Function.update addressed (addressed address1Reg)
      (addressed outputReg) index = store index
  rw [haddress, Function.update_of_ne happend, haddressed, hevaluated]

theorem routine_measured_internal {bound base : ℕ}
    {gate : CircuitCode.RawGate} {wires : List Bool} {store : Store}
    (hready : ReadyAt base gate wires store)
    (hstore : StoreEnvelope bound bound store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (happend : base + wires.length < bound) :
    ∃ final,
      MeasuredRuns program store final stepCount (80 * valueWidth bound)
        (envelopeSpace bound bound) ∧
      StoreEnvelope bound bound final ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (base + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      final baseReg = base ∧ final wireCountReg = wires.length ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ index, wireBase ≤ index → index ≠ base + wires.length →
        final index = store index := by
  have hinput0 : gate.input₀ < wires.length :=
    List.getElem?_eq_some_iff.mp hvalue0 |>.1
  have hinput1 : gate.input₁ < wires.length :=
    List.getElem?_eq_some_iff.mp hvalue1 |>.1
  have hsmall : 10 < bound := by
    have hbase := hready.base_ge
    simp only [wireBase] at hbase
    omega
  have htwo : 2 ≤ bound := by omega
  let addressed0 := (Basic.add address0Reg address0Reg baseReg).exec store
  have haddressed0 : StoreEnvelope bound bound addressed0 := by
    apply hstore.execBasic (.add address0Reg address0Reg baseReg)
    · simp [address0Reg]
      omega
    · change store address0Reg + store baseReg ≤ bound
      rw [hready.address0_eq, hready.base_eq]
      omega
  have haddressed : StoreEnvelope bound bound (routineAddressed store) := by
    change StoreEnvelope bound bound
      ((Basic.add address1Reg address1Reg baseReg).exec addressed0)
    apply haddressed0.execBasic (.add address1Reg address1Reg baseReg)
    · simp [address1Reg]
      omega
    · change addressed0 address1Reg + addressed0 baseReg ≤ bound
      have haddress1 : addressed0 address1Reg = gate.input₁ := by
        simp [addressed0, Basic.exec, Function.update_of_ne, address0Reg,
          address1Reg]
        exact hready.address1_eq
      have hbase : addressed0 baseReg = base := by
        simp [addressed0, Basic.exec, Function.update_of_ne, address0Reg,
          baseReg]
        exact hready.base_eq
      rw [haddress1, hbase]
      omega
  have haddressRun0 := MeasuredRuns.basicEnvelope
    (.add address0Reg address0Reg baseReg) store hstore haddressed0
  have haddressRun1 := MeasuredRuns.basicEnvelope
    (.add address1Reg address1Reg baseReg) addressed0 haddressed0 haddressed
  have haddressRun : MeasuredRuns (.basics addressOps) store
      (routineAddressed store) 2 (8 * valueWidth bound)
      (envelopeSpace bound bound) := by
    have hrun := haddressRun0.seq haddressRun1
    convert! hrun using 1
    ring
  let loaded0 := (Basic.load value0Reg address0Reg).exec (routineAddressed store)
  have hloaded0 : StoreEnvelope bound bound loaded0 := by
    apply haddressed.execBasic (.load value0Reg address0Reg)
    · simp [value0Reg]
      omega
    · exact haddressed.value_le (routineAddressed store address0Reg)
  have hloaded : StoreEnvelope bound bound (routineLoaded store) := by
    change StoreEnvelope bound bound
      ((Basic.load value1Reg address1Reg).exec loaded0)
    apply hloaded0.execBasic (.load value1Reg address1Reg)
    · simp [value1Reg]
      omega
    · exact hloaded0.value_le (loaded0 address1Reg)
  have hloadRun0 := MeasuredRuns.basicEnvelope (.load value0Reg address0Reg)
    (routineAddressed store) haddressed hloaded0
  have hloadRun1 := MeasuredRuns.basicEnvelope (.load value1Reg address1Reg)
    loaded0 hloaded0 hloaded
  have hloadRun : MeasuredRuns (.basics loadOps) (routineAddressed store)
      (routineLoaded store) 2 (8 * valueWidth bound)
      (envelopeSpace bound bound) := by
    have hrun := hloadRun0.seq hloadRun1
    convert! hrun using 1
    ring
  have hloadedValue0 := routineLoaded_value0 hready value0 hvalue0
  have hloadedNegated0 : routineLoaded store negated0Reg =
      Input.bitValue gate.negated₀ := by
    rw [routineLoaded_apply_of_ne]
    · exact hready.negated0_eq
    all_goals simp [negated0Reg, value0Reg, value1Reg, address0Reg, address1Reg]
  have hxor0 := xor_measured hloaded htwo
    (value := value0Reg) (negated := negated0Reg)
    (by simp [value0Reg]; omega) (by simp [outputReg]; omega)
    (by simp [scratchReg]; omega) (by simp [value0Reg, outputReg])
    (by simp [negated0Reg, outputReg]) value0 gate.negated₀
    hloadedValue0 hloadedNegated0
  have hnegated0 := hxor0.2
  have hnegated0Run : MeasuredRuns (.basics (xorOps value0Reg negated0Reg))
      (routineLoaded store) (routineNegated0 store) 4
      (16 * valueWidth bound) (envelopeSpace bound bound) := by
    simpa [routineNegated0] using hxor0.1
  have hnegated0Value1 : routineNegated0 store value1Reg =
      Input.bitValue value1 := by
    rw [routineNegated0_apply_of_ne]
    · exact routineLoaded_value1 hready value1 hvalue1
    all_goals simp [value0Reg, value1Reg, outputReg, scratchReg]
  have hnegated0Negated1 : routineNegated0 store negated1Reg =
      Input.bitValue gate.negated₁ := by
    rw [routineNegated0_apply_of_ne]
    · rw [routineLoaded_apply_of_ne]
      · exact hready.negated1_eq
      all_goals simp [negated1Reg, value0Reg, value1Reg, address0Reg, address1Reg]
    all_goals simp [negated1Reg, value0Reg, outputReg, scratchReg]
  have hxor1 := xor_measured hnegated0 htwo
    (value := value1Reg) (negated := negated1Reg)
    (by simp [value1Reg]; omega) (by simp [outputReg]; omega)
    (by simp [scratchReg]; omega) (by simp [value1Reg, outputReg])
    (by simp [negated1Reg, outputReg]) value1 gate.negated₁
    hnegated0Value1 hnegated0Negated1
  have hnegated1 := hxor1.2
  have hnegated1Run : MeasuredRuns (.basics (xorOps value1Reg negated1Reg))
      (routineNegated0 store) (routineNegated1 store) 4
      (16 * valueWidth bound) (envelopeSpace bound bound) := by
    simpa [routineNegated1] using! hxor1.1
  have hvalue0Eq := routineNegated1_value0 hready value0 hvalue0
  have hvalue1Eq := routineNegated1_value hready value1 hvalue1
  have hopEq := routineNegated1_op hready
  let product := (Basic.mul scratchReg value0Reg value1Reg).exec
    (routineNegated1 store)
  let sum := (Basic.add outputReg value0Reg value1Reg).exec product
  let orStore := (Basic.sub outputReg outputReg scratchReg).exec sum
  let delta := (Basic.sub address0Reg outputReg scratchReg).exec orStore
  let selected := (Basic.mul address0Reg opReg address0Reg).exec delta
  have hproduct : StoreEnvelope bound bound product := by
    apply hnegated1.execBasic (.mul scratchReg value0Reg value1Reg)
    · simp [scratchReg]
      omega
    · change routineNegated1 store value0Reg *
        routineNegated1 store value1Reg ≤ bound
      rw [hvalue0Eq, hvalue1Eq]
      cases gate.negated₀ <;> cases gate.negated₁ <;>
        cases value0 <;> cases value1 <;> simp [Input.bitValue] <;> omega
  have hproductValue0 : product value0Reg =
      Input.bitValue (gate.negated₀.xor value0) := by
    rw [show product value0Reg = routineNegated1 store value0Reg by
      simp [product, Basic.exec, Function.update_of_ne, value0Reg, scratchReg]]
    exact hvalue0Eq
  have hproductValue1 : product value1Reg =
      Input.bitValue (gate.negated₁.xor value1) := by
    rw [show product value1Reg = routineNegated1 store value1Reg by
      simp [product, Basic.exec, Function.update_of_ne, value1Reg, scratchReg]]
    exact hvalue1Eq
  have hsum : StoreEnvelope bound bound sum := by
    apply hproduct.execBasic (.add outputReg value0Reg value1Reg)
    · simp [outputReg]
      omega
    · change product value0Reg + product value1Reg ≤ bound
      rw [hproductValue0, hproductValue1]
      cases gate.negated₀ <;> cases gate.negated₁ <;>
        cases value0 <;> cases value1 <;> simp [Input.bitValue] <;> omega
  have hsumOutput : sum outputReg ≤ 2 := by
    change product value0Reg + product value1Reg ≤ 2
    rw [hproductValue0, hproductValue1]
    cases gate.negated₀ <;> cases gate.negated₁ <;>
      cases value0 <;> cases value1 <;> simp [Input.bitValue]
  have hor : StoreEnvelope bound bound orStore := by
    apply hsum.execBasic (.sub outputReg outputReg scratchReg)
    · simp [outputReg]
      omega
    · exact le_trans (Nat.sub_le _ _) (le_trans hsumOutput htwo)
  have horOutput : orStore outputReg ≤ 2 :=
    le_trans (Nat.sub_le _ _) hsumOutput
  have hdelta : StoreEnvelope bound bound delta := by
    apply hor.execBasic (.sub address0Reg outputReg scratchReg)
    · simp [address0Reg]
      omega
    · exact le_trans (Nat.sub_le _ _) (le_trans horOutput htwo)
  have hdeltaValue : delta address0Reg ≤ 2 :=
    le_trans (Nat.sub_le _ _) horOutput
  have hselected : StoreEnvelope bound bound selected := by
    apply hdelta.execBasic (.mul address0Reg opReg address0Reg)
    · simp [address0Reg]
      omega
    · have hop : delta opReg = Input.bitValue gate.opBit := by
        rw [show delta opReg = routineNegated1 store opReg by
          simp [delta, orStore, sum, product, Basic.exec,
            Function.update_of_ne, opReg, address0Reg, outputReg, scratchReg,
            value0Reg, value1Reg]]
        exact hopEq
      change delta opReg * delta address0Reg ≤ bound
      rw [hop]
      cases gate.opBit <;> simp [Input.bitValue]
      exact le_trans hdeltaValue htwo
  have hevaluated : StoreEnvelope bound bound (routineEvaluated store) := by
    change StoreEnvelope bound bound
      ((Basic.sub outputReg outputReg address0Reg).exec selected)
    apply hselected.execBasic (.sub outputReg outputReg address0Reg)
    · simp [outputReg]
      omega
    · exact le_trans (Nat.sub_le _ _) (hselected.value_le outputReg)
  have hevalRun0 := MeasuredRuns.basicEnvelope
    (.mul scratchReg value0Reg value1Reg) (routineNegated1 store)
    hnegated1 hproduct
  have hevalRun1 := MeasuredRuns.basicEnvelope
    (.add outputReg value0Reg value1Reg) product hproduct hsum
  have hevalRun2 := MeasuredRuns.basicEnvelope
    (.sub outputReg outputReg scratchReg) sum hsum hor
  have hevalRun3 := MeasuredRuns.basicEnvelope
    (.sub address0Reg outputReg scratchReg) orStore hor hdelta
  have hevalRun4 := MeasuredRuns.basicEnvelope
    (.mul address0Reg opReg address0Reg) delta hdelta hselected
  have hevalRun5 := MeasuredRuns.basicEnvelope
    (.sub outputReg outputReg address0Reg) selected hselected hevaluated
  have hevalRun : MeasuredRuns (.basics evalOps) (routineNegated1 store)
      (routineEvaluated store) 6 (24 * valueWidth bound)
      (envelopeSpace bound bound) := by
    have hrun := hevalRun0.seq (hevalRun1.seq (hevalRun2.seq
      (hevalRun3.seq (hevalRun4.seq hevalRun5))))
    convert! hrun using 1
    ring
  let appendAddressed :=
    (Basic.add address1Reg baseReg wireCountReg).exec (routineEvaluated store)
  have happendAddressed : StoreEnvelope bound bound appendAddressed := by
    apply hevaluated.execBasic (.add address1Reg baseReg wireCountReg)
    · simp [address1Reg]
      omega
    · change routineEvaluated store baseReg +
        routineEvaluated store wireCountReg ≤ bound
      rw [routineEvaluated_base hready, routineEvaluated_wireCount hready]
      omega
  have hfinal : StoreEnvelope bound bound (routineFinal store) := by
    change StoreEnvelope bound bound
      ((Basic.store address1Reg outputReg).exec appendAddressed)
    apply happendAddressed.execBasic (.store address1Reg outputReg)
    · change appendAddressed address1Reg < bound
      change routineEvaluated store baseReg +
        routineEvaluated store wireCountReg < bound
      rw [routineEvaluated_base hready, routineEvaluated_wireCount hready]
      exact happend
    · exact happendAddressed.value_le outputReg
  have happendRun0 := MeasuredRuns.basicEnvelope
    (.add address1Reg baseReg wireCountReg) (routineEvaluated store)
    hevaluated happendAddressed
  have happendRun1 := MeasuredRuns.basicEnvelope
    (.store address1Reg outputReg) appendAddressed happendAddressed hfinal
  have happendRun : MeasuredRuns (.basics appendOps) (routineEvaluated store)
      (routineFinal store) 2 (8 * valueWidth bound)
      (envelopeSpace bound bound) := by
    have hrun := happendRun0.seq happendRun1
    convert! hrun using 1
    ring
  have hrun := haddressRun.seq (hloadRun.seq
    (hnegated0Run.seq (hnegated1Run.seq (hevalRun.seq happendRun))))
  have hprogram : MeasuredRuns program store (routineFinal store) stepCount
      (80 * valueWidth bound) (envelopeSpace bound bound) := by
    convert! hrun using 1
    all_goals ring
  exact ⟨routineFinal store, hprogram, hfinal,
    routineFinal_output hready value0 value1 hvalue0 hvalue1,
    routineFinal_appended hready value0 value1 hvalue0 hvalue1,
    routineFinal_base hready, routineFinal_wireCount hready,
    routineFinal_wire hready, routineFinal_frame hready⟩

theorem routine_exec_internal {base : ℕ} {gate : CircuitCode.RawGate}
    {wires : List Bool} {store : Store} (hready : ReadyAt base gate wires store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program store final stepCount cost space ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (base + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      final baseReg = base ∧ final wireCountReg = wires.length ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ index, wireBase ≤ index → index ≠ base + wires.length →
        final index = store index := by
  obtain ⟨addressCost, addressSpace, haddress⟩ :=
    exec_basics_exists addressOps store
  obtain ⟨loadCost, loadSpace, hload⟩ :=
    exec_basics_exists loadOps (routineAddressed store)
  obtain ⟨negated0Cost, negated0Space, hnegated0⟩ :=
    exec_basics_exists (xorOps value0Reg negated0Reg) (routineLoaded store)
  obtain ⟨negated1Cost, negated1Space, hnegated1⟩ :=
    exec_basics_exists (xorOps value1Reg negated1Reg) (routineNegated0 store)
  obtain ⟨evalCost, evalSpace, heval⟩ :=
    exec_basics_exists evalOps (routineNegated1 store)
  obtain ⟨appendCost, appendSpace, happend⟩ :=
    exec_basics_exists appendOps (routineEvaluated store)
  have hrun := haddress.seq (hload.seq
    (hnegated0.seq (hnegated1.seq (heval.seq happend))))
  refine ⟨routineFinal store,
    addressCost + (loadCost + (negated0Cost +
      (negated1Cost + (evalCost + appendCost)))),
    max addressSpace (max loadSpace (max negated0Space
      (max negated1Space (max evalSpace appendSpace)))), ?_,
    routineFinal_output hready value0 value1 hvalue0 hvalue1,
    routineFinal_appended hready value0 value1 hvalue0 hvalue1,
    routineFinal_base hready, routineFinal_wireCount hready, ?_,
    routineFinal_frame hready⟩
  · rw [program]
    convert! hrun using 1
  · intro index hindex
    exact routineFinal_wire hready index hindex

private theorem finalStore_output_internal (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    finalStore gate wires outputReg = Input.bitValue (gate.eval value0 value1) :=
  finalStore_output gate wires value0 value1 hvalue0 hvalue1

theorem program_exec_internal (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final stepCount cost space ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) := by
  obtain ⟨addressCost, addressSpace, haddress⟩ :=
    exec_basics_exists addressOps (inputStore gate wires)
  obtain ⟨loadCost, loadSpace, hload⟩ :=
    exec_basics_exists loadOps (addressed gate wires)
  obtain ⟨negated0Cost, negated0Space, hnegated0⟩ :=
    exec_basics_exists (xorOps value0Reg negated0Reg) (loaded gate wires)
  obtain ⟨negated1Cost, negated1Space, hnegated1⟩ :=
    exec_basics_exists (xorOps value1Reg negated1Reg) (negated0 gate wires)
  obtain ⟨evalCost, evalSpace, heval⟩ :=
    exec_basics_exists evalOps (negated1 gate wires)
  obtain ⟨appendCost, appendSpace, happend⟩ :=
    exec_basics_exists appendOps (evaluated gate wires)
  have hrun := haddress.seq (hload.seq
    (hnegated0.seq (hnegated1.seq (heval.seq happend))))
  refine ⟨finalStore gate wires,
    addressCost + (loadCost + (negated0Cost +
      (negated1Cost + (evalCost + appendCost)))),
    max addressSpace (max loadSpace (max negated0Space
      (max negated1Space (max evalSpace appendSpace)))), ?_, ?_⟩
  · rw [program]
    convert! hrun using 1
  · exact finalStore_output gate wires value0 value1 hvalue0 hvalue1

theorem program_measured_internal (gate : CircuitCode.RawGate) (wires : List Bool)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1)
    (hgate : gate.WellFormedAt wires.length) :
    ∃ final cost space,
      Exec program (inputStore gate wires) final stepCount cost space ∧
      cost ≤ timeBound wires.length ∧ space ≤ spaceBound wires.length ∧
      final outputReg = Input.bitValue (gate.eval value0 value1) ∧
      final (wireBase + wires.length) = Input.bitValue (gate.eval value0 value1) ∧
      ∀ index (hindex : index < wires.length),
        final (wireBase + index) = Input.bitValue wires[index] := by
  have haddress := (address_measured gate wires hgate).1
  have hload := (load_measured gate wires hgate).1
  have hnegated0 := (negated0_measured gate wires value0 hvalue0 hgate).1
  have hnegated1 :=
    (negated1_measured gate wires value0 value1 hvalue0 hvalue1 hgate).1
  have heval := (eval_measured gate wires value0 value1 hvalue0 hvalue1 hgate).1
  have happend :=
    (append_measured gate wires value0 value1 hvalue0 hvalue1 hgate).1
  have hrun := haddress.seq (hload.seq
    (hnegated0.seq (hnegated1.seq (heval.seq happend))))
  have hprogram : MeasuredRuns program (inputStore gate wires)
      (finalStore gate wires) stepCount (timeBound wires.length)
      (resourceSpace wires.length) := by
    convert! hrun using 1
    simp [timeBound, width, valueWidth]
    ring
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hprogram
  have hspace' : space ≤ spaceBound wires.length := by
    rw [← envelopeSpace_eq_spaceBound]
    exact hspace
  exact ⟨finalStore gate wires, cost, space, hexec, hcost, hspace',
    finalStore_output gate wires value0 value1 hvalue0 hvalue1,
    finalStore_appended gate wires value0 value1 hvalue0 hvalue1,
    finalStore_wire gate wires⟩

end GateEval

end Structured

end RAM

end Complexity
