/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode.Defs

/-!
# Structured RAM terminated-unary decoder — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace UnaryDecode

open Internal

private abbrev StoreBound (inputLength : ℕ) (store : Store) : Prop :=
  StoreEnvelope (inputLength + inputBase) (inputLength + inputBase) store

private abbrev width (inputLength : ℕ) : ℕ :=
  valueWidth (inputLength + inputBase)

private abbrev resourceSpace (inputLength : ℕ) : ℕ :=
  envelopeSpace (inputLength + inputBase) (inputLength + inputBase)

private theorem envelopeSpace_eq_spaceBound (inputLength : ℕ) :
    resourceSpace inputLength = spaceBound inputLength := by
  simp [resourceSpace, envelopeSpace, spaceBound, two_mul]

private theorem inputStore_bound (bits : List Bool) :
    StoreBound bits.length (inputStore bits) := by
  apply Internal.Input.bitStoreEnvelope
  · simp [remainingReg, inputBase]
  · simp [inputBase, Nat.add_comm]
  · omega
  · simp [inputBase]

private def setupStore (bits : List Bool) : Store :=
  Basic.execList setupOps (inputStore bits)

private theorem setup_measured (bits : List Bool) :
    MeasuredRuns setup (inputStore bits) (setupStore bits) 5
        (20 * width bits.length) (resourceSpace bits.length) ∧
      StoreBound bits.length (setupStore bits) := by
  have hinitial := inputStore_bound bits
  have hpreserve : ∀ op, op ∈ setupOps → ∀ store,
      StoreBound bits.length store → StoreBound bits.length (op.exec store) := by
    intro op hop store hstore
    simp [setupOps] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    · apply hstore.execBasic (.imm verdictReg 0) <;> simp [verdictReg, inputBase]
    · apply hstore.execBasic (.imm valueReg 0) <;> simp [valueReg, inputBase]
    · apply hstore.execBasic (.imm pointerReg inputBase)
      · simp [pointerReg, inputBase]
      · simp [Internal.Basic.writeValue, inputBase]
    · apply hstore.execBasic (.imm oneReg 1) <;> simp [oneReg, inputBase]
    · apply hstore.execBasic (.imm activeReg 1) <;> simp [activeReg, inputBase]
  simpa [setup, setupStore, setupOps] using
    MeasuredRuns.basicsEnvelope setupOps (inputStore bits) hinitial hpreserve

private structure LoopInv (inputLength : ℕ) (remaining : List Bool)
    (offset value : ℕ) (store : Store) : Prop where
  total_eq : offset + remaining.length = inputLength
  value_le_offset : value ≤ offset
  store_bound : StoreBound inputLength store
  verdict_eq : store verdictReg = 0
  value_eq : store valueReg = value
  pointer_eq : store pointerReg = inputBase + offset
  remaining_eq : store remainingReg = remaining.length
  one_eq : store oneReg = 1
  active_eq : store activeReg = 1
  input_eq : ∀ delta,
    store (inputBase + offset + delta) =
      match remaining[delta]? with
      | some bit => Input.bitValue bit
      | none => 0

private theorem loopInv_of_cursorReady {inputLength offset value : ℕ}
    {remaining : List Bool} {store : Store}
    (hready : CursorReady inputLength remaining offset value store)
    (hbound : StoreBound inputLength store) :
    LoopInv inputLength remaining offset value store where
  total_eq := hready.total_eq
  value_le_offset := hready.value_le_offset
  store_bound := hbound
  verdict_eq := hready.verdict_eq
  value_eq := hready.value_eq
  pointer_eq := hready.pointer_eq
  remaining_eq := hready.remaining_eq
  one_eq := hready.one_eq
  active_eq := hready.active_eq
  input_eq := hready.input_eq

private theorem setup_inv (bits : List Bool)
    (hbound : StoreBound bits.length (setupStore bits)) :
    LoopInv bits.length bits 0 0 (setupStore bits) := by
  constructor
  · simp
  · simp
  · exact hbound
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, oneReg, activeReg]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, oneReg, activeReg]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, oneReg, activeReg, inputBase]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, remainingReg, oneReg, activeReg,
      inputStore, Input.bitStore]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, oneReg, activeReg]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, verdictReg,
      valueReg, pointerReg, oneReg, activeReg]
  · intro offset
    have h1 : 7 + offset ≠ 1 := by omega
    have h2 : 7 + offset ≠ 2 := by omega
    have h3 : 7 + offset ≠ 3 := by omega
    have h4 : 7 + offset ≠ 4 := by omega
    have h6 : 7 + offset ≠ 6 := by omega
    simp [setupStore, setupOps, Basic.execList, Basic.exec, Function.update_of_ne,
      h1, h2, h3, h4, h6, inputStore, Input.bitStore,
      inputBase, verdictReg, valueReg, pointerReg, remainingReg, oneReg,
      activeReg]
    rfl

private def truncatedStore (store : Store) : Store :=
  Basic.execList [.imm verdictReg 0, .imm activeReg 0] store

private def loaded (store : Store) : Store :=
  (Basic.load bitReg pointerReg).exec store

private def moved (store : Store) : Store :=
  (Basic.add pointerReg pointerReg oneReg).exec (loaded store)

private def decremented (store : Store) : Store :=
  (Basic.sub remainingReg remainingReg oneReg).exec (moved store)

private def successStore (store : Store) : Store :=
  Basic.execList [.imm verdictReg 1, .imm activeReg 0] (decremented store)

private def continuedStore (store : Store) : Store :=
  (Basic.add valueReg valueReg oneReg).exec (decremented store)

private theorem loaded_bound {inputLength : ℕ} {store : Store}
    (hstore : StoreBound inputLength store) :
    StoreBound inputLength (loaded store) := by
  apply hstore.execBasic (.load bitReg pointerReg)
  · simp [bitReg, inputBase]
  · simpa [Internal.Basic.writeValue] using hstore.value_le (store pointerReg)

private theorem loaded_bit {bit : Bool} {rest : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) offset value store) :
    loaded store bitReg = Input.bitValue bit := by
  simp only [loaded, Basic.exec, Function.update_self]
  rw [hinv.pointer_eq]
  simpa using hinv.input_eq 0

private theorem moved_bound {bit : Bool} {rest : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) offset value store) :
    StoreBound inputLength (moved store) := by
  have hloaded := loaded_bound hinv.store_bound
  apply hloaded.execBasic (.add pointerReg pointerReg oneReg)
  · simp [pointerReg, inputBase]
  · have hpointer : loaded store pointerReg = inputBase + offset := by
      simpa [loaded, Basic.exec, bitReg, pointerReg] using hinv.pointer_eq
    have hone : loaded store oneReg = 1 := by
      simpa [loaded, Basic.exec, bitReg, oneReg] using hinv.one_eq
    change loaded store pointerReg + loaded store oneReg ≤ inputLength + inputBase
    rw [hpointer, hone]
    have htotal := hinv.total_eq
    simp only [List.length_cons] at htotal
    omega

private theorem decremented_bound {bit : Bool} {rest : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) offset value store) :
    StoreBound inputLength (decremented store) := by
  have hmoved := moved_bound hinv
  apply hmoved.execBasic (.sub remainingReg remainingReg oneReg)
  · simp [remainingReg, inputBase]
  · exact Nat.le_trans (Nat.sub_le _ _) (hmoved.value_le remainingReg)

private theorem success_bound {rest : List Bool} {inputLength offset value : ℕ}
    {store : Store}
    (hinv : LoopInv inputLength (false :: rest) offset value store) :
    StoreBound inputLength (successStore store) := by
  have hdecremented := decremented_bound hinv
  have hverdict := hdecremented.execBasic (.imm verdictReg 1)
    (by simp [verdictReg, inputBase]) (by simp [Internal.Basic.writeValue, inputBase])
  apply hverdict.execBasic (.imm activeReg 0) <;>
    simp [activeReg, inputBase]

private theorem continued_bound {rest : List Bool} {inputLength offset value : ℕ}
    {store : Store}
    (hinv : LoopInv inputLength (true :: rest) offset value store) :
    StoreBound inputLength (continuedStore store) := by
  have hdecremented := decremented_bound hinv
  apply hdecremented.execBasic (.add valueReg valueReg oneReg)
  · simp [valueReg, inputBase]
  · have hvalue : decremented store valueReg = value := by
      simpa [decremented, moved, loaded, Basic.exec, remainingReg, pointerReg,
        bitReg, valueReg] using hinv.value_eq
    have hone : decremented store oneReg = 1 := by
      simpa [decremented, moved, loaded, Basic.exec, remainingReg, pointerReg,
        bitReg, valueReg, oneReg] using hinv.one_eq
    change decremented store valueReg + decremented store oneReg ≤
      inputLength + inputBase
    rw [hvalue, hone]
    have hvalueLe := hinv.value_le_offset
    have htotal := hinv.total_eq
    simp only [List.length_cons] at htotal
    simp only [inputBase]
    omega

private theorem continued_high (store : Store) (index : ℕ)
    (hindex : inputBase ≤ index) : continuedStore store index = store index := by
  have hvalue : index ≠ valueReg := by
    simp only [inputBase, valueReg] at hindex ⊢
    omega
  have hpointer : index ≠ pointerReg := by
    simp only [inputBase, pointerReg] at hindex ⊢
    omega
  have hremaining : index ≠ remainingReg := by
    simp only [inputBase, remainingReg] at hindex ⊢
    omega
  have hbit : index ≠ bitReg := by
    simp only [inputBase, bitReg] at hindex ⊢
    omega
  simp [continuedStore, decremented, moved, loaded, Basic.exec,
    Function.update_of_ne, hvalue, hpointer, hremaining, hbit]

private theorem truncated_high (store : Store) (index : ℕ)
    (hindex : inputBase ≤ index) : truncatedStore store index = store index := by
  have hverdict : index ≠ verdictReg := by
    simp only [inputBase, verdictReg] at hindex ⊢
    omega
  have hactive : index ≠ activeReg := by
    simp only [inputBase, activeReg] at hindex ⊢
    omega
  simp [truncatedStore, Basic.execList, Basic.exec, Function.update_of_ne,
    hverdict, hactive]

private theorem success_high (store : Store) (index : ℕ)
    (hindex : inputBase ≤ index) : successStore store index = store index := by
  have hverdict : index ≠ verdictReg := by
    simp only [inputBase, verdictReg] at hindex ⊢
    omega
  have hpointer : index ≠ pointerReg := by
    simp only [inputBase, pointerReg] at hindex ⊢
    omega
  have hremaining : index ≠ remainingReg := by
    simp only [inputBase, remainingReg] at hindex ⊢
    omega
  have hbit : index ≠ bitReg := by
    simp only [inputBase, bitReg] at hindex ⊢
    omega
  have hactive : index ≠ activeReg := by
    simp only [inputBase, activeReg] at hindex ⊢
    omega
  simp [successStore, decremented, moved, loaded, Basic.execList, Basic.exec,
    Function.update_of_ne, hverdict, hpointer, hremaining, hbit, hactive]

private theorem truncated_measured {inputLength : ℕ} {store : Store}
    (hstore : StoreBound inputLength store) :
    MeasuredRuns stopTruncated store (truncatedStore store) 2
      (8 * width inputLength) (resourceSpace inputLength) ∧
    StoreBound inputLength (truncatedStore store) := by
  have hpreserve : ∀ op, op ∈ ([Basic.imm verdictReg 0,
      Basic.imm activeReg 0] : List Basic) →
      ∀ current, StoreBound inputLength current →
        StoreBound inputLength (op.exec current) := by
    intro op hop current hcurrent
    simp at hop
    rcases hop with rfl | rfl
    · apply hcurrent.execBasic (.imm verdictReg 0) <;>
        simp [verdictReg, inputBase]
    · apply hcurrent.execBasic (.imm activeReg 0) <;>
        simp [activeReg, inputBase]
  simpa [stopTruncated, truncatedStore] using
    MeasuredRuns.basicsEnvelope [.imm verdictReg 0, .imm activeReg 0]
      store hstore hpreserve

private theorem false_body_measured {rest : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength (false :: rest) offset value store) :
    MeasuredRuns body store (successStore store) 8
      (32 * width inputLength) (resourceSpace inputLength) ∧
    StoreBound inputLength (successStore store) := by
  have hloaded := loaded_bound hinv.store_bound
  have hmoved := moved_bound hinv
  have hdecremented := decremented_bound hinv
  have hsuccess := success_bound hinv
  have hload := MeasuredRuns.basicEnvelope (.load bitReg pointerReg) store
    hinv.store_bound hloaded
  have hmove := MeasuredRuns.basicEnvelope (.add pointerReg pointerReg oneReg)
    (loaded store) hloaded hmoved
  have hdecrement := MeasuredRuns.basicEnvelope
    (.sub remainingReg remainingReg oneReg) (moved store) hmoved hdecremented
  have hstop : MeasuredRuns stopSuccess (decremented store) (successStore store) 2
      (8 * width inputLength) (resourceSpace inputLength) := by
    have hpreserve : ∀ op, op ∈ ([Basic.imm verdictReg 1,
        Basic.imm activeReg 0] : List Basic) →
        ∀ current, StoreBound inputLength current →
          StoreBound inputLength (op.exec current) := by
      intro op hop current hcurrent
      simp at hop
      rcases hop with rfl | rfl
      · apply hcurrent.execBasic (.imm verdictReg 1) <;>
          simp [verdictReg, inputBase]
      · apply hcurrent.execBasic (.imm activeReg 0) <;>
          simp [activeReg, inputBase]
    exact (by simpa [stopSuccess, successStore] using
      (MeasuredRuns.basicsEnvelope [Basic.imm verdictReg 1,
        Basic.imm activeReg 0] (decremented store) hdecremented hpreserve).1)
  have hbit : decremented store bitReg = 0 := by
    have hloadedBit := loaded_bit hinv
    simpa [decremented, moved, Basic.exec, remainingReg, pointerReg, bitReg,
      oneReg, Input.bitValue] using hloadedBit
  have hbranch := MeasuredRuns.ifZeroEnvelope (onNonzero :=
    .basic (.add valueReg valueReg oneReg)) hbit hdecremented hstop
  have hconsume := hload.seq (hmove.seq (hdecrement.seq hbranch))
  have hremaining : store remainingReg ≠ 0 := by
    rw [hinv.remaining_eq]
    simp
  have hrun := MeasuredRuns.ifNonzeroEnvelope (onZero := stopTruncated)
    hremaining hinv.store_bound (by
      simpa [consume, Cmd.seqList] using hconsume)
  refine ⟨?_, hsuccess⟩
  apply MeasuredRuns.weakenCost (by simpa [body] using! hrun)
  change 3 * width inputLength +
      (4 * width inputLength +
        (4 * width inputLength +
          (4 * width inputLength +
            (width inputLength + 8 * width inputLength)))) ≤
    32 * width inputLength
  omega

private theorem true_body_measured {rest : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength (true :: rest) offset value store) :
    MeasuredRuns body store (continuedStore store) 8
      (32 * width inputLength) (resourceSpace inputLength) ∧
    LoopInv inputLength rest (offset + 1) (value + 1) (continuedStore store) := by
  have hloaded := loaded_bound hinv.store_bound
  have hmoved := moved_bound hinv
  have hdecremented := decremented_bound hinv
  have hcontinued := continued_bound hinv
  have hload := MeasuredRuns.basicEnvelope (.load bitReg pointerReg) store
    hinv.store_bound hloaded
  have hmove := MeasuredRuns.basicEnvelope (.add pointerReg pointerReg oneReg)
    (loaded store) hloaded hmoved
  have hdecrement := MeasuredRuns.basicEnvelope
    (.sub remainingReg remainingReg oneReg) (moved store) hmoved hdecremented
  have hadd := MeasuredRuns.basicEnvelope (.add valueReg valueReg oneReg)
    (decremented store) hdecremented hcontinued
  have hbit : decremented store bitReg ≠ 0 := by
    have hloadedBit := loaded_bit hinv
    have heq : decremented store bitReg = 1 := by
      simpa [decremented, moved, Basic.exec, remainingReg, pointerReg, bitReg,
        oneReg, Input.bitValue] using hloadedBit
    omega
  have hbranch := MeasuredRuns.ifNonzeroEnvelope (onZero := stopSuccess)
    hbit hdecremented hadd
  have hconsume := hload.seq (hmove.seq (hdecrement.seq hbranch))
  have hremaining : store remainingReg ≠ 0 := by
    rw [hinv.remaining_eq]
    simp
  have hrun := MeasuredRuns.ifNonzeroEnvelope (onZero := stopTruncated)
    hremaining hinv.store_bound (by
      simpa [consume, Cmd.seqList] using hconsume)
  constructor
  · apply MeasuredRuns.weakenCost (by simpa [body] using! hrun)
    change 3 * width inputLength +
        (4 * width inputLength +
          (4 * width inputLength +
            (4 * width inputLength +
              (3 * width inputLength + 4 * width inputLength)))) ≤
      32 * width inputLength
    omega
  · constructor
    · have htotal := hinv.total_eq
      simp only [List.length_cons] at htotal
      omega
    · have hvalueLe := hinv.value_le_offset
      omega
    · exact hcontinued
    · simpa [continuedStore, decremented, moved, loaded, Basic.exec,
        verdictReg, valueReg, pointerReg, remainingReg, oneReg, bitReg,
        activeReg] using hinv.verdict_eq
    · have hvalue : store valueReg = value := hinv.value_eq
      have hone : store oneReg = 1 := hinv.one_eq
      simp [continuedStore, decremented, moved, loaded, Basic.exec,
        valueReg, pointerReg, remainingReg, oneReg, bitReg]
      have hvalue' : store 1 = value := by simpa [valueReg] using hvalue
      have hone' : store 4 = 1 := by simpa [oneReg] using hone
      omega
    · have hpointer : store pointerReg = inputBase + offset := hinv.pointer_eq
      have hone : store oneReg = 1 := hinv.one_eq
      simp [continuedStore, decremented, moved, loaded, Basic.exec,
        valueReg, pointerReg, remainingReg, oneReg, bitReg]
      have hpointer' : store 2 = inputBase + offset := by
        simpa [pointerReg] using hpointer
      have hone' : store 4 = 1 := by simpa [oneReg] using hone
      omega
    · have hremaining : store remainingReg = rest.length + 1 := by
        simpa using hinv.remaining_eq
      have hone : store oneReg = 1 := hinv.one_eq
      simp [continuedStore, decremented, moved, loaded, Basic.exec,
        valueReg, pointerReg, remainingReg, oneReg, bitReg]
      have hremaining' : store 3 = rest.length + 1 := by
        simpa [remainingReg] using hremaining
      have hone' : store 4 = 1 := by simpa [oneReg] using hone
      omega
    · simpa [continuedStore, decremented, moved, loaded, Basic.exec,
        verdictReg, valueReg, pointerReg, remainingReg, oneReg, bitReg,
        activeReg] using hinv.one_eq
    · simpa [continuedStore, decremented, moved, loaded, Basic.exec,
        verdictReg, valueReg, pointerReg, remainingReg, oneReg, bitReg,
        activeReg] using hinv.active_eq
    · intro offset
      rw [continued_high store _ (by simp [inputBase]; omega)]
      have hinput := hinv.input_eq (offset + 1)
      convert! hinput using 1
      all_goals simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem decodeAux?_eq_map (bits : List Bool) (acc : ℕ) :
    CircuitCode.NatCode.decodeAux? bits acc =
      (CircuitCode.NatCode.decodePrefix? bits).map fun result =>
        (acc + result.1, result.2) := by
  induction bits generalizing acc with
  | nil => simp [CircuitCode.NatCode.decodeAux?, CircuitCode.NatCode.decodePrefix?]
  | cons bit rest ih =>
      cases bit with
      | false =>
          simp [CircuitCode.NatCode.decodeAux?, CircuitCode.NatCode.decodePrefix?]
      | true =>
          rw [CircuitCode.NatCode.decodeAux?]
          rw [ih (acc + 1)]
          have htrue : CircuitCode.NatCode.decodePrefix? (true :: rest) =
              CircuitCode.NatCode.decodeAux? rest 1 := rfl
          rw [htrue]
          rw [ih 1]
          cases hdecode : CircuitCode.NatCode.decodePrefix? rest with
          | none => simp
          | some result =>
              rcases result with ⟨value, suffix⟩
              simp [Nat.add_assoc]

private theorem decodePrefix?_true (rest : List Bool) :
    CircuitCode.NatCode.decodePrefix? (true :: rest) =
      (CircuitCode.NatCode.decodePrefix? rest).map fun result =>
        (result.1 + 1, result.2) := by
  rw [CircuitCode.NatCode.decodePrefix?, CircuitCode.NatCode.decodeAux?]
  rw [decodeAux?_eq_map]
  cases hdecode : CircuitCode.NatCode.decodePrefix? rest with
  | none => simp
  | some result =>
      rcases result with ⟨value, suffix⟩
      simp [Nat.add_comm]

private theorem loop_measured {remaining : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hinv : LoopInv inputLength remaining offset value store) :
    ∃ final,
      MeasuredRuns mainLoop store final
        (match CircuitCode.NatCode.decodePrefix? remaining with
          | none => 10 * remaining.length + 6
          | some (value, _) => 10 * value + 11)
        (64 * (remaining.length + 1) * width inputLength)
        (resourceSpace inputLength) ∧
      (match CircuitCode.NatCode.decodePrefix? remaining with
      | none =>
          final verdictReg = 0 ∧ final valueReg = value + remaining.length ∧
          final pointerReg = inputBase + inputLength ∧ final remainingReg = 0
      | some (decoded, rest) =>
          final verdictReg = 1 ∧ final valueReg = value + decoded ∧
          final pointerReg = inputBase + offset + decoded + 1 ∧
          final remainingReg = rest.length) ∧
      final activeReg = 0 ∧
      final oneReg = 1 ∧
      (∀ index, inputBase ≤ index → final index = store index) ∧
      StoreBound inputLength final := by
  induction remaining generalizing offset value store with
  | nil =>
      have hremaining : store remainingReg = 0 := by
        simpa using hinv.remaining_eq
      obtain ⟨hbody, htruncatedBound⟩ := truncated_measured hinv.store_bound
      have hbodyRun := MeasuredRuns.ifZeroEnvelope (onNonzero := consume)
        hremaining hinv.store_bound hbody
      have hactive : store activeReg ≠ 0 := by rw [hinv.active_eq]; decide
      have hfinalActive : truncatedStore store activeReg = 0 := by
        simp [truncatedStore, Basic.execList, Basic.exec, activeReg, verdictReg]
      have hstop := MeasuredRuns.whileZeroEnvelope (body := body)
        hfinalActive htruncatedBound
      have hrun := MeasuredRuns.whileNonzeroEnvelope hactive hinv.store_bound
        (by simpa [body] using hbodyRun) hstop
      refine ⟨truncatedStore store, ?_, ?_, ?_, ?_, ?_, htruncatedBound⟩
      · apply MeasuredRuns.weakenCost (by simpa [mainLoop] using! hrun)
        change 3 * width inputLength +
            (width inputLength + 8 * width inputLength) +
            width inputLength ≤
          64 * ([].length + 1) * width inputLength
        simp only [List.length_nil, zero_add]
        omega
      · simp only [CircuitCode.NatCode.decodePrefix?,
          CircuitCode.NatCode.decodeAux?]
        have htotal := hinv.total_eq
        have hvalue := hinv.value_eq
        have hpointer := hinv.pointer_eq
        have hremainingStore := hinv.remaining_eq
        simp only [List.length_nil, Nat.add_zero] at htotal
        have hvalue' : store 1 = value := by simpa [valueReg] using hvalue
        have hpointer' : store 2 = inputBase + offset := by
          simpa [pointerReg] using hpointer
        have hremaining' : store 3 = 0 := by
          simpa [remainingReg] using hremainingStore
        simp [truncatedStore, Basic.execList, Basic.exec, verdictReg, valueReg,
          pointerReg, remainingReg, activeReg, hvalue', hpointer', hremaining']
        omega
      · simp [truncatedStore, Basic.execList, Basic.exec, activeReg, verdictReg]
      · simpa [truncatedStore, Basic.execList, Basic.exec, oneReg, activeReg,
          verdictReg] using hinv.one_eq
      · intro index hindex
        exact truncated_high store index hindex
  | cons bit rest ih =>
      cases bit with
      | false =>
          obtain ⟨hbody, hsuccessBound⟩ := false_body_measured hinv
          have hactive : store activeReg ≠ 0 := by rw [hinv.active_eq]; decide
          have hfinalActive : successStore store activeReg = 0 := by
            simp [successStore, Basic.execList, Basic.exec, activeReg, verdictReg,
              decremented, moved, loaded, remainingReg, pointerReg, bitReg]
          have hstop := MeasuredRuns.whileZeroEnvelope (body := body)
            hfinalActive hsuccessBound
          have hrun := MeasuredRuns.whileNonzeroEnvelope hactive hinv.store_bound
            hbody hstop
          refine ⟨successStore store, ?_, ?_, ?_, ?_, ?_, hsuccessBound⟩
          · apply MeasuredRuns.weakenCost (by simpa [mainLoop] using! hrun)
            change 3 * width inputLength + 32 * width inputLength +
                width inputLength ≤
              64 * ((false :: rest).length + 1) * width inputLength
            calc
              _ = 36 * width inputLength := by ring
              _ ≤ (64 * (rest.length + 2)) * width inputLength :=
                Nat.mul_le_mul_right _ (by omega)
              _ = _ := by simp only [List.length_cons]
          · simp only [CircuitCode.NatCode.decodePrefix?,
              CircuitCode.NatCode.decodeAux?]
            have hvalue := hinv.value_eq
            have hpointer := hinv.pointer_eq
            have hremaining : store remainingReg = rest.length + 1 := by
              simpa using hinv.remaining_eq
            have hone := hinv.one_eq
            simp [successStore, Basic.execList, decremented, moved, loaded,
              Basic.exec, verdictReg, valueReg, pointerReg, remainingReg, oneReg,
              bitReg, activeReg]
            have hvalue' : store 1 = value := by simpa [valueReg] using hvalue
            have hpointer' : store 2 = inputBase + offset := by
              simpa [pointerReg] using hpointer
            have hremaining' : store 3 = rest.length + 1 := by
              simpa [remainingReg] using hremaining
            have hone' : store 4 = 1 := by simpa [oneReg] using hone
            omega
          · simp [successStore, Basic.execList, Basic.exec, activeReg,
              verdictReg, decremented, moved, loaded, remainingReg, pointerReg,
              bitReg]
          · simpa [successStore, Basic.execList, Basic.exec, oneReg, activeReg,
              verdictReg, decremented, moved, loaded, remainingReg, pointerReg,
              bitReg] using hinv.one_eq
          · intro index hindex
            exact success_high store index hindex
      | true =>
          obtain ⟨hbody, hnextInv⟩ := true_body_measured hinv
          obtain ⟨final, hloop, hfinal, hactiveFinal, honeFinal, hframe,
              hfinalBound⟩ := ih hnextInv
          have hactive : store activeReg ≠ 0 := by rw [hinv.active_eq]; decide
          have hrun := MeasuredRuns.whileNonzeroEnvelope hactive hinv.store_bound
            hbody hloop
          refine ⟨final, ?_, ?_, hactiveFinal, honeFinal, ?_, hfinalBound⟩
          · rw [decodePrefix?_true]
            cases hdecode : CircuitCode.NatCode.decodePrefix? rest with
            | none =>
                rw [hdecode] at hrun
                simp only at hrun
                have hrun' : MeasuredRuns mainLoop store final
                    (10 * (rest.length + 1) + 6)
                    (3 * width inputLength + 32 * width inputLength +
                      64 * (rest.length + 1) * width inputLength)
                    (resourceSpace inputLength) := by
                  rw [mainLoop]
                  convert! hrun using 1
                  all_goals omega
                apply MeasuredRuns.weakenCost hrun'
                change 3 * width inputLength + 32 * width inputLength +
                    (64 * (rest.length + 1) * width inputLength) ≤
                  64 * ((true :: rest).length + 1) * width inputLength
                calc
                  _ = (64 * (rest.length + 1) + 35) * width inputLength := by ring
                  _ ≤ (64 * (rest.length + 2)) * width inputLength :=
                    Nat.mul_le_mul_right _ (by omega)
                  _ = _ := by simp only [List.length_cons]
            | some result =>
                rcases result with ⟨value, suffix⟩
                rw [hdecode] at hrun
                simp only at hrun
                have hrun' : MeasuredRuns mainLoop store final
                    (10 * (value + 1) + 11)
                    (3 * width inputLength + 32 * width inputLength +
                      64 * (rest.length + 1) * width inputLength)
                    (resourceSpace inputLength) := by
                  rw [mainLoop]
                  convert! hrun using 1
                  all_goals omega
                apply MeasuredRuns.weakenCost hrun'
                change 3 * width inputLength + 32 * width inputLength +
                    (64 * (rest.length + 1) * width inputLength) ≤
                  64 * ((true :: rest).length + 1) * width inputLength
                calc
                  _ = (64 * (rest.length + 1) + 35) * width inputLength := by ring
                  _ ≤ (64 * (rest.length + 2)) * width inputLength :=
                    Nat.mul_le_mul_right _ (by omega)
                  _ = _ := by simp only [List.length_cons]
          · rw [decodePrefix?_true]
            cases hdecode : CircuitCode.NatCode.decodePrefix? rest with
            | none =>
                simpa [hdecode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hfinal
            | some result =>
                rcases result with ⟨decoded, suffix⟩
                rw [hdecode] at hfinal
                simp only [Option.map_some]
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal
          · intro index hindex
            rw [hframe index hindex]
            exact continued_high store index hindex

theorem mainLoop_measured_internal {remaining : List Bool}
    {inputLength offset value : ℕ} {store : Store}
    (hready : CursorReady inputLength remaining offset value store)
    (hbound : Internal.StoreEnvelope (inputLength + inputBase)
      (inputLength + inputBase) store) :
    ∃ final cost space,
      Exec mainLoop store final (loopStepCount remaining) cost space ∧
      cost ≤ timeBound inputLength ∧ space ≤ spaceBound inputLength ∧
      (match CircuitCode.NatCode.decodePrefix? remaining with
      | none =>
          final verdictReg = 0 ∧ final valueReg = value + remaining.length ∧
          final pointerReg = inputBase + inputLength ∧ final remainingReg = 0
      | some (decoded, rest) =>
          final verdictReg = 1 ∧ final valueReg = value + decoded ∧
          final pointerReg = inputBase + offset + decoded + 1 ∧
          final remainingReg = rest.length) ∧
      final activeReg = 0 ∧
      final oneReg = 1 ∧
      (∀ index, inputBase ≤ index → final index = store index) ∧
      Internal.StoreEnvelope (inputLength + inputBase)
        (inputLength + inputBase) final := by
  have hinv := loopInv_of_cursorReady hready hbound
  obtain ⟨final, hrun, hresult, hactive, hone, hframe, hfinalBound⟩ :=
    loop_measured hinv
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hrun
  have hremaining : remaining.length ≤ inputLength := by
    have htotal := hready.total_eq
    omega
  have hcostBound :
      64 * (remaining.length + 1) * width inputLength ≤
        timeBound inputLength := by
    rw [timeBound]
    change 64 * (remaining.length + 1) * width inputLength ≤
      96 * (inputLength + 1) * width inputLength
    apply Nat.mul_le_mul_right
    omega
  have hspaceBound : space ≤ spaceBound inputLength := by
    rw [← envelopeSpace_eq_spaceBound]
    exact hspace
  refine ⟨final, cost, space, ?_, le_trans hcost hcostBound, hspaceBound,
    hresult, hactive, hone, hframe, hfinalBound⟩
  simpa [loopStepCount] using! hexec

theorem program_measured_internal (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      match CircuitCode.NatCode.decodePrefix? bits with
      | none =>
          final verdictReg = 0 ∧ final valueReg = bits.length ∧
          final pointerReg = inputBase + bits.length ∧ final remainingReg = 0
      | some (value, rest) =>
          final verdictReg = 1 ∧ final valueReg = value ∧
          final pointerReg = inputBase + value + 1 ∧
          final remainingReg = rest.length := by
  obtain ⟨hsetup, hsetupBound⟩ := setup_measured bits
  have hsetupInv := setup_inv bits hsetupBound
  obtain ⟨final, hloop, hfinal, _hactive, _hone, _hframe, _hfinalBound⟩ :=
    loop_measured hsetupInv
  have hseq := hsetup.seq hloop
  have hcostLe :
      20 * width bits.length +
          64 * (bits.length + 1) * width bits.length ≤
        timeBound bits.length := by
    rw [timeBound]
    change 20 * width bits.length +
        64 * (bits.length + 1) * width bits.length ≤
      96 * (bits.length + 1) * width bits.length
    calc
      _ = (64 * (bits.length + 1) + 20) * width bits.length := by ring
      _ ≤ (96 * (bits.length + 1)) * width bits.length :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hprogram := hseq.weakenCost hcostLe
  have hprogram' : MeasuredRuns program (inputStore bits) final
      (stepCount bits) (timeBound bits.length) (resourceSpace bits.length) := by
    rw [program]
    cases hdecode : CircuitCode.NatCode.decodePrefix? bits with
    | none =>
        rw [hdecode] at hprogram
        simp only at hprogram
        convert! hprogram using 1
        all_goals simp [stepCount, hdecode]
        all_goals omega
    | some result =>
        rcases result with ⟨value, suffix⟩
        rw [hdecode] at hprogram
        simp only at hprogram
        convert! hprogram using 1
        all_goals simp [stepCount, hdecode]
        all_goals omega
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hprogram'
  have hspace' : space ≤ spaceBound bits.length := by
    rw [← envelopeSpace_eq_spaceBound]
    exact hspace
  refine ⟨final, cost, space, hexec, hcost, hspace', ?_⟩
  cases hdecode : CircuitCode.NatCode.decodePrefix? bits with
  | none =>
      rw [hdecode] at hfinal
      simpa [hdecode] using hfinal
  | some result =>
      rcases result with ⟨value, suffix⟩
      rw [hdecode] at hfinal
      simpa [hdecode] using hfinal

end UnaryDecode

end Structured

end RAM

end Complexity
