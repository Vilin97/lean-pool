/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Internal.Loop
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Internal.Capture
import Mathlib.Algebra.Order.Sub.Basic

/-!
# Public-input marshalling correctness -- proof internals

This file lifts the pointwise backward-copy facts to a loop invariant, repairs
the finitely many captured scratch positions, and establishes the complete
sparse representation of the Turing machine's initial configuration.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Store after installing the constants used by the backward-copy loop. -/
def marshalStart (n : ℕ) (x : List Bool) : Structured.Store :=
  Structured.Basic.execList (marshalConstants n) (initRegs x)

/-- Semantic invariant after relocating positions `|x|, …, cursor + 1`.
Uncaptured destinations are exact, captured destinations are at least marked
positive, future uncaptured raw sources retain their public-ABI value, and all
other data registers have their expected raw-or-zero contents. -/
def MarshalInvariant (n : ℕ) (x : List Bool) (cursor : ℕ)
    (store : Structured.Store) : Prop :=
  store stateReg = cursor ∧
    cursor ≤ x.length ∧
    store (zeroReg n) = 0 ∧
    store (oneReg n) = 1 ∧
    store (tapeCountReg n) = n + 2 ∧
    store (stateScratchReg n) = cellBase n ∧
    (∀ position, 0 < position → position ≤ cursor →
      position ∉ captureRegs n → store position = initRegs x position) ∧
    (∀ position, cursor < position → position ≤ x.length →
      position ∉ captureRegs n →
      store (cellReg n (inputTape n) position) =
        initRegs x position + 1) ∧
    (∀ position, cursor < position → position ≤ x.length →
      0 < store (cellReg n (inputTape n) position)) ∧
    (∀ reg, cellBase n ≤ reg →
      (∀ position, cursor < position → position ≤ x.length →
        reg ≠ cellReg n (inputTape n) position) →
      store reg = if reg ≤ cursor then initRegs x reg else 0)

private theorem marshalStart_of_not_captured (n : ℕ) (x : List Bool)
    {reg : ℕ} (hfree : reg ∉ captureRegs n) :
    marshalStart n x reg = initRegs x reg := by
  simp only [marshalStart, marshalConstants, Structured.Basic.execList,
    Structured.Basic.exec]
  have hzero : reg ≠ zeroReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hone : reg ≠ oneReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hcount : reg ≠ tapeCountReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hbase : reg ≠ stateScratchReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  rw [Function.update_of_ne hbase, Function.update_of_ne hcount,
    Function.update_of_ne hone, Function.update_of_ne hzero]

private theorem initRegs_eq_zero_of_length_lt (x : List Bool) {reg : ℕ}
    (hreg : x.length < reg) : initRegs x reg = 0 := by
  rw [initRegs, if_neg (by omega)]
  rw [List.getElem?_eq_none (by omega)]

/-- Installing loop constants establishes the invariant before any input
position has been relocated. -/
theorem marshalStart_invariant_internal (n : ℕ) (x : List Bool) :
    MarshalInvariant n x x.length (marshalStart n x) := by
  have hstate : marshalStart n x stateReg = x.length := by
    rw [marshalStart_of_not_captured]
    · simp [initRegs, stateReg]
    · simp [captureRegs, stateReg, zeroReg, oneReg, tapeCountReg,
        stateScratchReg, addressReg, valueReg]
  have hzero : marshalStart n x (zeroReg n) = 0 := by
    simp [marshalStart, marshalConstants, Structured.Basic.execList,
      Structured.Basic.exec, zeroReg, oneReg, tapeCountReg, stateScratchReg,
      Function.update_of_ne]
  have hone : marshalStart n x (oneReg n) = 1 := by
    simp [marshalStart, marshalConstants, Structured.Basic.execList,
      Structured.Basic.exec, oneReg, tapeCountReg, stateScratchReg,
      Function.update_of_ne]
  have hcount : marshalStart n x (tapeCountReg n) = n + 2 := by
    simp [marshalStart, marshalConstants, Structured.Basic.execList,
      Structured.Basic.exec, tapeCountReg, stateScratchReg,
      Function.update_of_ne]
  have hbase : marshalStart n x (stateScratchReg n) = cellBase n := by
    simp [marshalStart, marshalConstants, Structured.Basic.execList,
      Structured.Basic.exec]
  refine ⟨hstate, le_rfl, hzero, hone, hcount, hbase, ?_, ?_, ?_, ?_⟩
  · intro position _ _ hfree
    exact marshalStart_of_not_captured n x hfree
  · intro position hposition _ _
    omega
  · intro position hposition _
    omega
  · intro reg hdata _
    rw [marshalStart_of_not_captured]
    · by_cases hreg : reg ≤ x.length
      · simp [hreg]
      · have hz : initRegs x reg = 0 :=
          initRegs_eq_zero_of_length_lt x (reg := reg) (by omega)
        simp [hreg, hz]
    · simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
        addressReg, valueReg, cellBase] at *
      omega

private theorem position_lt_inputCell (n position : ℕ) :
    position < cellReg n (inputTape n) position := by
  simp [cellReg, inputTape, cellBase, Nat.mul_add]
  omega

private theorem inputCell_injective (n : ℕ) :
    Function.Injective (cellReg n (inputTape n)) := by
  intro left right heq
  simp [cellReg, inputTape] at heq
  omega

private theorem inputCell_not_captured (n position : ℕ) :
    cellReg n (inputTape n) position ∉ captureRegs n := by
  simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
    addressReg, valueReg, cellReg, inputTape, cellBase]
  omega

private theorem inputCell_data (n position : ℕ) :
    cellBase n ≤ cellReg n (inputTape n) position := by
  simp [cellReg, inputTape]

/-- One positive-cursor body advances the complete relocation invariant by one
position, including an exact value for ordinary sources and a positive visited
marker for captured scratch sources. -/
theorem marshalLoopOps_invariant_internal (n : ℕ) (x : List Bool)
    (cursor : ℕ) (store : Structured.Store) (hcursor : 0 < cursor)
    (hinvariant : MarshalInvariant n x cursor store) :
    MarshalInvariant n x (cursor - 1)
      (Structured.Basic.execList (marshalLoopOps n) store) := by
  rcases hinvariant with
    ⟨hstate, hcursorLength, hzero, hone, hcount, hbase, hsource, hexact,
      hpositive, hother⟩
  let middle := Structured.Basic.execList (marshalLoopOps n) store
  have hstorePositive : 0 < store stateReg := by omega
  have hcontrol :=
    marshalLoopOps_control_internal n store hstorePositive hzero
  have hmiddleState : middle stateReg = cursor - 1 := by
    change Structured.Basic.execList (marshalLoopOps n) store stateReg = _
    rw [hcontrol.1, hstate]
  refine ⟨hmiddleState, by omega, hcontrol.2.1, hcontrol.2.2.1,
    hcontrol.2.2.2.1, hcontrol.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro position hposition hpositionCursor hfree
    have hpositionState : position ≠ stateReg := by
      simp [stateReg]
      omega
    have hpositionSource : position ≠ store stateReg := by
      rw [hstate]
      omega
    have hpositionDestination :
        position ≠ cellReg n (inputTape n) (store stateReg) := by
      rw [hstate]
      have hhigh := position_lt_inputCell n cursor
      omega
    change Structured.Basic.execList (marshalLoopOps n) store position = _
    rw [marshalLoopOps_of_ne_internal n store position hstorePositive
      hzero hpositionState hfree hpositionSource hpositionDestination]
    exact hsource position hposition (by omega) hfree
  · intro position hposition hlength hfree
    by_cases heq : position = cursor
    · subst position
      have hfreeStore : store stateReg ∉ captureRegs n := by
        simpa [hstate] using hfree
      have hbody := marshalLoopOps_data_internal n store
        (cellReg n (inputTape n) cursor) hstorePositive hzero hfreeStore
        (inputCell_data n cursor)
      change Structured.Basic.execList (marshalLoopOps n) store
        (cellReg n (inputTape n) cursor) = _
      rw [hbody, hstate, Function.update_self,
        hsource cursor hcursor le_rfl hfree]
    · have hcursorPosition : cursor < position := by omega
      have hregState : cellReg n (inputTape n) position ≠ stateReg := by
        simp [stateReg, cellReg, inputTape, cellBase]
      have hregSource :
          cellReg n (inputTape n) position ≠ store stateReg := by
        rw [hstate]
        have hhigh := position_lt_inputCell n position
        omega
      have hregDestination : cellReg n (inputTape n) position ≠
          cellReg n (inputTape n) (store stateReg) := by
        intro hcells
        have := inputCell_injective n hcells
        rw [hstate] at this
        omega
      change Structured.Basic.execList (marshalLoopOps n) store
        (cellReg n (inputTape n) position) = _
      rw [marshalLoopOps_of_ne_internal n store
        (cellReg n (inputTape n) position) hstorePositive hzero hregState
        (inputCell_not_captured n position) hregSource hregDestination]
      exact hexact position hcursorPosition hlength hfree
  · intro position hposition hlength
    by_cases heq : position = cursor
    · subst position
      simpa [hstate] using hcontrol.2.2.2.2.2
    · have hcursorPosition : cursor < position := by omega
      have hregState : cellReg n (inputTape n) position ≠ stateReg := by
        simp [stateReg, cellReg, inputTape, cellBase]
      have hregSource :
          cellReg n (inputTape n) position ≠ store stateReg := by
        rw [hstate]
        have hhigh := position_lt_inputCell n position
        omega
      have hregDestination : cellReg n (inputTape n) position ≠
          cellReg n (inputTape n) (store stateReg) := by
        intro hcells
        have := inputCell_injective n hcells
        rw [hstate] at this
        omega
      change 0 < Structured.Basic.execList (marshalLoopOps n) store
        (cellReg n (inputTape n) position)
      rw [marshalLoopOps_of_ne_internal n store
        (cellReg n (inputTape n) position) hstorePositive hzero hregState
        (inputCell_not_captured n position) hregSource hregDestination]
      exact hpositive position hcursorPosition hlength
  · intro reg hdata hnotDestination
    have hregState : reg ≠ stateReg := by
      intro heq
      rw [heq] at hdata
      simp [stateReg, cellBase] at hdata
    have hregFree : reg ∉ captureRegs n := by
      intro hmem
      simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
        addressReg, valueReg] at hmem
      rcases hmem with h | h | h | h | h | h <;>
        rw [h] at hdata <;> simp [cellBase] at hdata <;> omega
    have hregDestination :
        reg ≠ cellReg n (inputTape n) (store stateReg) := by
      rw [hstate]
      apply hnotDestination cursor
      · omega
      · omega
    by_cases hregSource : reg = cursor
    · subst reg
      have hfreeStore : store stateReg ∉ captureRegs n := by
        simpa [hstate] using hregFree
      have hbody := marshalLoopOps_data_internal n store cursor
        hstorePositive hzero hfreeStore hdata
      have hregDestinationCursor :
          cursor ≠ cellReg n (inputTape n) cursor := by
        exact Nat.ne_of_lt (position_lt_inputCell n cursor)
      change Structured.Basic.execList (marshalLoopOps n) store cursor = _
      rw [hbody, hstate, Function.update_of_ne hregDestinationCursor,
        Function.update_self]
      simp [hcursor]
    · have hregSource' : reg ≠ store stateReg := by
        rw [hstate]
        exact hregSource
      have hpreserved := marshalLoopOps_of_ne_internal n store reg
        hstorePositive hzero hregState hregFree hregSource'
        hregDestination
      change Structured.Basic.execList (marshalLoopOps n) store reg = _
      rw [hpreserved]
      have holdNotDestination : ∀ position, cursor < position →
          position ≤ x.length →
          reg ≠ cellReg n (inputTape n) position := by
        intro position hposition hlength
        exact hnotDestination position (by omega) hlength
      rw [hother reg hdata holdNotDestination]
      by_cases hregLow : reg ≤ cursor - 1
      · simp [hregLow, show reg ≤ cursor by omega]
      · simp [hregLow, show ¬ reg ≤ cursor by omega]

/-- The complete backward loop executes once per input position and leaves the
relocation invariant at cursor zero. -/
theorem marshalLoop_invariant_exec_internal (n : ℕ) (x : List Bool)
    (cursor : ℕ) (store : Structured.Store)
    (hinvariant : MarshalInvariant n x cursor store) :
    ∃ final cost space,
      Structured.Exec (marshalLoop n) store final
        (marshalLoopSteps n cursor) cost space ∧
      MarshalInvariant n x 0 final := by
  induction cursor generalizing store with
  | zero =>
      have hstateZero : store stateReg = 0 := hinvariant.1
      refine ⟨store, bitlen (store stateReg) + 1, store.space, ?_, ?_⟩
      · simpa [marshalLoop, marshalLoopSteps] using
          (Structured.Exec.whileZero
            (body := .basics (marshalLoopOps n)) hstateZero)
      · exact hinvariant
  | succ cursor ih =>
      have hpositive : 0 < cursor + 1 := by omega
      have hstoreNonzero : store stateReg ≠ 0 := by
        rw [hinvariant.1]
        omega
      let middle := Structured.Basic.execList (marshalLoopOps n) store
      obtain ⟨bodyCost, bodySpace, hbody⟩ :=
        marshalLoopOps_exec_internal n store
      have hmiddleInvariant : MarshalInvariant n x cursor middle := by
        have hstep := marshalLoopOps_invariant_internal n x (cursor + 1)
          store hpositive hinvariant
        simpa [middle] using hstep
      obtain ⟨final, loopCost, loopSpace, hloop, hfinalInvariant⟩ :=
        ih middle hmiddleInvariant
      refine ⟨final,
        bitlen (store stateReg) + 1 + bodyCost + 1 + loopCost,
        max bodySpace loopSpace, ?_, hfinalInvariant⟩
      have hexec := Structured.Exec.whileNonzero hstoreNonzero hbody hloop
      convert hexec using 1
      simp [marshalLoopSteps, Nat.succ_mul]
      omega

/-- Exact store selected by one captured-position repair command. -/
def repairBitStore (n : ℕ) (entry : ℕ × ℕ)
    (store : Structured.Store) : Structured.Store :=
  let loaded := Structured.Basic.execList
    [.imm (addressReg n) (cellReg n (inputTape n) entry.1),
      .load (valueReg n) (addressReg n)] store
  if loaded (valueReg n) = 0 then loaded
  else Structured.Basic.execList
    [.imm (valueReg n) (entry.2 + 1),
      .store (addressReg n) (valueReg n)] loaded

/-- Exact store selected by the recursive captured-position repair pass. -/
def repairStore (n : ℕ) :
    List (ℕ × ℕ) → Structured.Store → Structured.Store
  | [], store => store
  | entry :: rest, store =>
      repairStore n rest (repairBitStore n entry store)

private theorem repairBit_exec_internal (n : ℕ) (entry : ℕ × ℕ)
    (store : Structured.Store) :
    ∃ steps cost space,
      Structured.Exec (repairBit n entry) store
        (repairBitStore n entry store) steps cost space := by
  let setup : List Structured.Basic :=
    [.imm (addressReg n) (cellReg n (inputTape n) entry.1),
      .load (valueReg n) (addressReg n)]
  let loaded := Structured.Basic.execList setup store
  obtain ⟨setupCost, setupSpace, hsetup⟩ :=
    Structured.Internal.exec_basics_exists setup store
  by_cases hzero : loaded (valueReg n) = 0
  · have hbranch := Structured.Exec.ifZero
      (onNonzero := .basics
        [.imm (valueReg n) (entry.2 + 1),
          .store (addressReg n) (valueReg n)])
      hzero (Structured.Exec.skip loaded)
    refine ⟨setup.length + 1, setupCost + (bitlen (loaded (valueReg n)) + 1),
      max setupSpace loaded.space, ?_⟩
    have hexec := Structured.Exec.seq hsetup hbranch
    simpa [repairBit, repairBitStore, setup, loaded, hzero,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hexec
  · let writes : List Structured.Basic :=
      [.imm (valueReg n) (entry.2 + 1),
        .store (addressReg n) (valueReg n)]
    let final := Structured.Basic.execList writes loaded
    obtain ⟨writeCost, writeSpace, hwrites⟩ :=
      Structured.Internal.exec_basics_exists writes loaded
    have hbranch := Structured.Exec.ifNonzero
      (onZero := Structured.Cmd.skip) hzero hwrites
    refine ⟨setup.length + (writes.length + 2),
      setupCost + (bitlen (loaded (valueReg n)) + 1 + writeCost + 1),
      max setupSpace (max loaded.space writeSpace), ?_⟩
    have hexec := Structured.Exec.seq hsetup hbranch
    simpa [repairBit, repairBitStore, setup, loaded, writes, final, hzero,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hexec

/-- The recursive repair command has an exact structured execution. -/
theorem repairCaptured_exec_internal (n : ℕ)
    (captured : List (ℕ × ℕ)) (store : Structured.Store) :
    ∃ steps cost space,
      Structured.Exec (repairCaptured n captured) store
        (repairStore n captured store) steps cost space := by
  induction captured generalizing store with
  | nil =>
      exact ⟨0, 0, store.space, Structured.Exec.skip store⟩
  | cons entry rest ih =>
      obtain ⟨firstSteps, firstCost, firstSpace, hfirst⟩ :=
        repairBit_exec_internal n entry store
      obtain ⟨restSteps, restCost, restSpace, hrest⟩ :=
        ih (repairBitStore n entry store)
      exact ⟨firstSteps + restSteps, firstCost + restCost,
        max firstSpace restSpace, Structured.Exec.seq hfirst hrest⟩

/-- On data registers, one repair either preserves the store or updates exactly
the selected input-cell destination. -/
theorem repairBitStore_data_internal (n : ℕ) (entry : ℕ × ℕ)
    (store : Structured.Store) (reg : ℕ) (hdata : cellBase n ≤ reg) :
    repairBitStore n entry store reg =
      if store (cellReg n (inputTape n) entry.1) = 0 then store reg
      else Function.update store (cellReg n (inputTape n) entry.1)
        (entry.2 + 1) reg := by
  let addressed :=
    (Structured.Basic.imm (addressReg n)
      (cellReg n (inputTape n) entry.1)).exec store
  let loaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec addressed
  have haddress : addressed (addressReg n) =
      cellReg n (inputTape n) entry.1 := by
    simp [addressed, Structured.Basic.exec]
  have hloadedValue : loaded (valueReg n) =
      store (cellReg n (inputTape n) entry.1) := by
    have hdestinationAddress :
        cellReg n (inputTape n) entry.1 ≠ addressReg n := by
      simp [cellReg, inputTape, cellBase, addressReg]
      omega
    have haddressedDestination : addressed
        (cellReg n (inputTape n) entry.1) =
        store (cellReg n (inputTape n) entry.1) := by
      simp only [addressed, Structured.Basic.exec]
      rw [Function.update_of_ne hdestinationAddress]
    simp only [loaded, Structured.Basic.exec, Function.update_self]
    rw [haddress, haddressedDestination]
  have hloadedAddress : loaded (addressReg n) =
      cellReg n (inputTape n) entry.1 := by
    simp only [loaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [addressReg, valueReg])]
    exact haddress
  have hregAddress : reg ≠ addressReg n := by
    intro heq
    rw [heq] at hdata
    simp [addressReg, cellBase] at hdata
    omega
  have hregValue : reg ≠ valueReg n := by
    intro heq
    rw [heq] at hdata
    simp [valueReg, cellBase] at hdata
    omega
  have hloadedData : loaded reg = store reg := by
    simp only [loaded, Structured.Basic.exec]
    rw [Function.update_of_ne hregValue]
    simp only [addressed, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
  unfold repairBitStore
  change (if loaded (valueReg n) = 0 then loaded else
    Structured.Basic.execList
      [.imm (valueReg n) (entry.2 + 1),
        .store (addressReg n) (valueReg n)] loaded) reg = _
  rw [hloadedValue]
  by_cases hzero : store (cellReg n (inputTape n) entry.1) = 0
  · simp [hzero, hloadedData]
  · simp only [hzero, if_false]
    let valued :=
      (Structured.Basic.imm (valueReg n) (entry.2 + 1)).exec loaded
    have hvaluedAddress : valued (addressReg n) =
        cellReg n (inputTape n) entry.1 := by
      simp only [valued, Structured.Basic.exec]
      rw [Function.update_of_ne (by simp [addressReg, valueReg])]
      exact hloadedAddress
    have hvaluedValue : valued (valueReg n) = entry.2 + 1 := by
      simp [valued, Structured.Basic.exec]
    change (Structured.Basic.store (addressReg n) (valueReg n)).exec
      valued reg = _
    simp only [Structured.Basic.exec]
    rw [hvaluedAddress, hvaluedValue]
    by_cases heq : reg = cellReg n (inputTape n) entry.1
    · subst reg
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne heq]
      simp only [valued, Structured.Basic.exec]
      rw [Function.update_of_ne hregValue]
      exact hloadedData

/-- A repair list preserves a data register that is not one of its selected
input-cell destinations. -/
theorem repairStore_data_of_not_mem_internal (n : ℕ)
    (captured : List (ℕ × ℕ)) (store : Structured.Store) (reg : ℕ)
    (hdata : cellBase n ≤ reg)
    (hnot : ∀ entry, entry ∈ captured →
      reg ≠ cellReg n (inputTape n) entry.1) :
    repairStore n captured store reg = store reg := by
  induction captured generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      have hhead : reg ≠ cellReg n (inputTape n) entry.1 :=
        hnot entry (by simp)
      have hrest : ∀ candidate, candidate ∈ rest →
          reg ≠ cellReg n (inputTape n) candidate.1 := by
        intro candidate hmem
        exact hnot candidate (by simp [hmem])
      simp only [repairStore]
      rw [ih (repairBitStore n entry store) hrest,
        repairBitStore_data_internal n entry store reg hdata]
      by_cases hzero : store (cellReg n (inputTape n) entry.1) = 0
      · simp [hzero]
      · simp [hzero, Function.update_of_ne hhead]

/-- A visited destination selected exactly once by a repair list receives its
captured Boolean value shifted to the sparse symbol code. -/
theorem repairStore_selected_internal (n : ℕ)
    (captured : List (ℕ × ℕ)) (store : Structured.Store)
    (position value : ℕ) (hmem : (position, value) ∈ captured)
    (hnodup : (captured.map Prod.fst).Nodup)
    (hpositive : 0 < store (cellReg n (inputTape n) position)) :
    repairStore n captured store (cellReg n (inputTape n) position) =
      value + 1 := by
  induction captured generalizing store with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hheadFresh, hrestNodup⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        have hupdated : repairBitStore n (position, value) store
            (cellReg n (inputTape n) position) = value + 1 := by
          rw [repairBitStore_data_internal n (position, value) store
            (cellReg n (inputTape n) position) (inputCell_data n position)]
          simp [show store (cellReg n (inputTape n) position) ≠ 0 by omega]
        have hrestPreserves := repairStore_data_of_not_mem_internal n rest
          (repairBitStore n (position, value) store)
          (cellReg n (inputTape n) position) (inputCell_data n position)
          (by
            intro candidate hcandidate heqCell
            apply hheadFresh
            rw [List.mem_map]
            refine ⟨candidate, hcandidate, ?_⟩
            exact (inputCell_injective n heqCell).symm)
        simp only [repairStore]
        rw [hrestPreserves, hupdated]
      · have hentryDifferent : position ≠ entry.1 := by
          intro heq
          subst position
          apply hheadFresh
          rw [List.mem_map]
          exact ⟨(entry.1, value), hmem, rfl⟩
        have hheadPreserves : repairBitStore n entry store
            (cellReg n (inputTape n) position) =
              store (cellReg n (inputTape n) position) := by
          rw [repairBitStore_data_internal n entry store
            (cellReg n (inputTape n) position) (inputCell_data n position)]
          by_cases hzero : store (cellReg n (inputTape n) entry.1) = 0
          · simp [hzero]
          · have hcells : cellReg n (inputTape n) position ≠
                cellReg n (inputTape n) entry.1 := by
              intro heqCell
              exact hentryDifferent (inputCell_injective n heqCell)
            simp [hzero, Function.update_of_ne hcells]
        have hnextPositive : 0 < repairBitStore n entry store
            (cellReg n (inputTape n) position) := by
          rw [hheadPreserves]
          exact hpositive
        simp only [repairStore]
        exact ih (repairBitStore n entry store) hmem hrestNodup hnextPositive

/-- A zero data register stays zero throughout every conditional repair,
including when it is an unvisited captured destination. -/
theorem repairStore_data_zero_internal (n : ℕ)
    (captured : List (ℕ × ℕ)) (store : Structured.Store) (reg : ℕ)
    (hdata : cellBase n ≤ reg) (hzero : store reg = 0) :
    repairStore n captured store reg = 0 := by
  induction captured generalizing store with
  | nil => exact hzero
  | cons entry rest ih =>
      have hnextZero : repairBitStore n entry store reg = 0 := by
        rw [repairBitStore_data_internal n entry store reg hdata]
        by_cases hentryZero :
            store (cellReg n (inputTape n) entry.1) = 0
        · simp [hentryZero, hzero]
        · have hne : reg ≠ cellReg n (inputTape n) entry.1 := by
            intro heq
            subst reg
            exact hentryZero hzero
          simp [hentryZero, Function.update_of_ne hne, hzero]
      simp only [repairStore]
      exact ih (repairBitStore n entry store) hnextZero

/-- Closed form of the accumulator-style capture traversal. -/
private theorem captureValues_eq_reverse_append (store : Structured.Store)
    (regs : List ℕ) (captured : List (ℕ × ℕ)) :
    captureValues store regs captured =
      (regs.map (fun reg => (reg, store reg))).reverse ++ captured := by
  induction regs generalizing captured with
  | nil => simp [captureValues]
  | cons reg rest ih =>
      rw [captureValues, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Captured values selected for a public input. -/
def capturedInput (n : ℕ) (x : List Bool) : List (ℕ × ℕ) :=
  captureValues (initRegs x) (captureRegs n) []

private theorem capturedInput_mem_iff (n : ℕ) (x : List Bool)
    (position : ℕ) :
    (position, initRegs x position) ∈ capturedInput n x ↔
      position ∈ captureRegs n := by
  rw [capturedInput, captureValues_eq_reverse_append]
  simp

private theorem capturedInput_fst_nodup (n : ℕ) (x : List Bool) :
    ((capturedInput n x).map Prod.fst).Nodup := by
  have hregs : (captureRegs n).Nodup := by
    simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
      addressReg, valueReg]
  rw [capturedInput, captureValues_eq_reverse_append]
  simp only [List.append_nil, List.map_reverse, List.map_map]
  simpa [Function.comp_def] using hregs

private theorem capturedInput_positions (n : ℕ) (x : List Bool)
    {entry : ℕ × ℕ} (hmem : entry ∈ capturedInput n x) :
    entry.1 ∈ captureRegs n ∧ entry.2 = initRegs x entry.1 := by
  rw [capturedInput, captureValues_eq_reverse_append] at hmem
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at hmem
  obtain ⟨position, hposition, rfl⟩ := hmem
  exact ⟨hposition, rfl⟩

private theorem initRegs_add_one_eq_input_symbol (x : List Bool)
    {position : ℕ} (hpositive : 0 < position)
    (hlength : position ≤ x.length) :
    initRegs x position + 1 =
      symbolCode ((Tape.init (x.map Γ.ofBool)).cells position) := by
  obtain ⟨index, rfl⟩ : ∃ index, position = index + 1 :=
    ⟨position - 1, by omega⟩
  have hindex : index < x.length := by omega
  rw [Tape.init_ofBool_cells_lt x index hindex]
  simp only [initRegs, show index + 1 ≠ 0 by omega, if_false]
  rw [show index + 1 - 1 = index by omega,
    List.getElem?_eq_getElem hindex]
  cases x[index] <;> simp [Γ.ofBool, symbolCode]

/-- After captured-position repair, every positive input cell has its exact TM
symbol code, cell zero is still temporarily blank, and all non-input tapes are
still blank. -/
theorem repairStore_cells_internal (n : ℕ) (x : List Bool)
    (store : Structured.Store)
    (hinvariant : MarshalInvariant n x 0 store) :
    let repaired := repairStore n (capturedInput n x) store
    (∀ position, 0 < position →
      repaired (cellReg n (inputTape n) position) =
        symbolCode ((Tape.init (x.map Γ.ofBool)).cells position)) ∧
    repaired (cellReg n (inputTape n) 0) = 0 ∧
    (∀ (tape : Fin (n + 2)) (position : ℕ), tape ≠ inputTape n →
      repaired (cellReg n tape position) = 0) := by
  rcases hinvariant with
    ⟨_, _, _, _, _, _, _, hexact, hpositive, hother⟩
  let captured := capturedInput n x
  let repaired := repairStore n captured store
  have hcapturedNodup : (captured.map Prod.fst).Nodup := by
    exact capturedInput_fst_nodup n x
  refine ⟨?_, ?_, ?_⟩
  · intro position hposition
    by_cases hlength : position ≤ x.length
    · by_cases hcaptured : position ∈ captureRegs n
      · have hmem : (position, initRegs x position) ∈ captured := by
          exact (capturedInput_mem_iff n x position).2 hcaptured
        have hrepaired := repairStore_selected_internal n captured store
          position (initRegs x position) hmem hcapturedNodup
          (hpositive position hposition hlength)
        exact hrepaired.trans
          (initRegs_add_one_eq_input_symbol x hposition hlength)
      · have hnot : ∀ entry, entry ∈ captured →
            cellReg n (inputTape n) position ≠
              cellReg n (inputTape n) entry.1 := by
          intro entry hentry heq
          have hentryInfo := capturedInput_positions n x hentry
          apply hcaptured
          rw [inputCell_injective n heq]
          exact hentryInfo.1
        have hpreserved := repairStore_data_of_not_mem_internal n captured
          store (cellReg n (inputTape n) position)
          (inputCell_data n position) hnot
        rw [hpreserved, hexact position hposition hlength hcaptured]
        exact initRegs_add_one_eq_input_symbol x hposition hlength
    · have hloopZero : store (cellReg n (inputTape n) position) = 0 := by
        have hnot : ∀ candidate, 0 < candidate →
            candidate ≤ x.length →
            cellReg n (inputTape n) position ≠
              cellReg n (inputTape n) candidate := by
          intro candidate _ hcandidate heq
          have := inputCell_injective n heq
          omega
        rw [hother (cellReg n (inputTape n) position)
          (inputCell_data n position) hnot]
        have hpositiveReg : 0 < cellReg n (inputTape n) position := by
          simp [cellReg, inputTape, cellBase]
        simp [show ¬ cellReg n (inputTape n) position ≤ 0 by omega]
      have hrepaired := repairStore_data_zero_internal n captured store
        (cellReg n (inputTape n) position) (inputCell_data n position)
        hloopZero
      rw [hrepaired]
      obtain ⟨index, rfl⟩ : ∃ index, position = index + 1 :=
        ⟨position - 1, by omega⟩
      rw [Tape.init_ofBool_cells_ge x index (by omega)]
      rfl
  · have hloopZero : store (cellReg n (inputTape n) 0) = 0 := by
      have hnot : ∀ candidate, 0 < candidate →
          candidate ≤ x.length →
          cellReg n (inputTape n) 0 ≠
            cellReg n (inputTape n) candidate := by
        intro candidate hcandidate _ heq
        have := inputCell_injective n heq
        omega
      rw [hother (cellReg n (inputTape n) 0) (inputCell_data n 0) hnot]
      simp [cellReg, inputTape, cellBase]
    exact repairStore_data_zero_internal n captured store
      (cellReg n (inputTape n) 0) (inputCell_data n 0) hloopZero
  · intro tape position htape
    have hdata : cellBase n ≤ cellReg n tape position := by
      unfold cellReg
      omega
    have hnot : ∀ candidate, 0 < candidate →
        candidate ≤ x.length →
        cellReg n tape position ≠
          cellReg n (inputTape n) candidate := by
      intro candidate _ _ heq
      have hpairs : (tape, position) = (inputTape n, candidate) :=
        cellReg_injective_internal (n := n) heq
      exact htape (congrArg Prod.fst hpairs)
    have hloopZero : store (cellReg n tape position) = 0 := by
      rw [hother (cellReg n tape position) hdata hnot]
      have hpositiveReg : 0 < cellReg n tape position := by
        simp [cellReg, cellBase]
      simp [show ¬ cellReg n tape position ≤ 0 by omega]
    exact repairStore_data_zero_internal n captured store
      (cellReg n tape position) hdata hloopZero

/-- Exact store after initializing state, heads, and all cell-zero markers. -/
noncomputable def initializeStore (tm : TM n)
    (store : Structured.Store) : Structured.Store :=
  Structured.Basic.execList (initializeConfigOps tm) store

private theorem initializeConfigWrites_fst_nodup (tm : TM n) :
    ((initializeConfigWrites tm).map Prod.fst).Nodup := by
  let heads := (List.finRange (n + 2)).map headReg
  let starts := (List.finRange (n + 2)).map fun tape => cellReg n tape 0
  have hheadInjective : Function.Injective (@headReg n) := by
    intro left right heq
    apply Fin.ext
    simp [headReg] at heq
    omega
  have hstartInjective : Function.Injective
      (fun tape : Fin (n + 2) => cellReg n tape 0) := by
    intro left right heq
    have hpairs : (left, 0) = (right, 0) :=
      cellReg_injective_internal (n := n) heq
    exact congrArg Prod.fst hpairs
  have hheads : heads.Nodup :=
    List.Nodup.map hheadInjective (List.nodup_finRange (n + 2))
  have hstarts : starts.Nodup :=
    List.Nodup.map hstartInjective (List.nodup_finRange (n + 2))
  have hdisjoint : ∀ head ∈ heads, ∀ start ∈ starts, head ≠ start := by
    intro head hhead start hstart heq
    simp only [heads, List.mem_map] at hhead
    simp only [starts, List.mem_map] at hstart
    obtain ⟨headTape, _, rfl⟩ := hhead
    obtain ⟨startTape, _, rfl⟩ := hstart
    simp [headReg, cellReg, cellBase] at heq
    omega
  have hcontrol : stateReg ∉ heads ++ starts := by
    intro hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · simp only [heads, List.mem_map] at hmem
      obtain ⟨tape, _, heq⟩ := hmem
      simp [stateReg, headReg] at heq
    · simp only [starts, List.mem_map] at hmem
      obtain ⟨tape, _, heq⟩ := hmem
      simp [stateReg, cellReg, cellBase] at heq
  have hresult : (stateReg :: heads ++ starts).Nodup :=
    List.nodup_cons.mpr
      ⟨hcontrol, List.nodup_append.mpr ⟨hheads, hstarts, hdisjoint⟩⟩
  simpa [initializeConfigWrites, heads, starts, Function.comp_def] using hresult

private theorem initializeConfigWrites_cell_pos_not_mem (tm : TM n)
    (tape : Fin (n + 2)) (position : ℕ) (hposition : 0 < position) :
    cellReg n tape position ∉ (initializeConfigWrites tm).map Prod.fst := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨write, hwrite, heq⟩ := hmem
  simp only [initializeConfigWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hwrite
  rcases hwrite with hstateOrHead | hstart
  · rcases hstateOrHead with heqState | hhead
    · subst write
      simp [stateReg, cellReg, cellBase] at heq
      omega
    · obtain ⟨headTape, _, rfl⟩ := hhead
      simp [headReg, cellReg, cellBase] at heq
      omega
  · obtain ⟨startTape, _, rfl⟩ := hstart
    have hpairs : (tape, position) = (startTape, 0) :=
      cellReg_injective_internal (n := n) heq.symm
    have := congrArg Prod.snd hpairs
    omega

/-- State, head, and left-marker initialization turns repaired tape data into
the complete sparse representation of `tm.initCfg x`. -/
theorem initializeStore_represents_internal (tm : TM n) (x : List Bool)
    (store : Structured.Store)
    (hinvariant : MarshalInvariant n x 0 store) :
    Represents tm (tm.initCfg x)
      (initializeStore tm (repairStore n (capturedInput n x) store)) := by
  let repaired := repairStore n (capturedInput n x) store
  have hcells := repairStore_cells_internal n x store hinvariant
  have hnodup := initializeConfigWrites_fst_nodup tm
  intro field
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hstateZero : state = 0 := by omega
    subst state
    change initializeStore tm repaired stateReg = stateCode tm tm.qstart
    unfold initializeStore initializeConfigOps
    apply Structured.Internal.Basic.execList_imm_apply_of_mem
      (initializeConfigWrites tm) repaired hnodup
    simp [initializeConfigWrites]
  · rcases headOrCell with tape | cell
    · change initializeStore tm repaired (headReg tape) =
        (tapeAt (tm.initCfg x) tape).head
      have hwrite : initializeStore tm repaired (headReg tape) = 0 := by
        unfold initializeStore initializeConfigOps
        apply Structured.Internal.Basic.execList_imm_apply_of_mem
          (initializeConfigWrites tm) repaired hnodup
        simp [initializeConfigWrites]
      rw [hwrite]
      unfold tapeAt
      split
      · rfl
      · split <;> rfl
    · rcases cell with ⟨tape, position⟩
      change initializeStore tm repaired (cellReg n tape position) =
        symbolCode ((tapeAt (tm.initCfg x) tape).cells position)
      by_cases hposition : position = 0
      · subst position
        have hwrite : initializeStore tm repaired (cellReg n tape 0) =
            symbolCode Γ.start := by
          unfold initializeStore initializeConfigOps
          apply Structured.Internal.Basic.execList_imm_apply_of_mem
            (initializeConfigWrites tm) repaired hnodup
          simp [initializeConfigWrites]
        rw [hwrite]
        unfold tapeAt
        split <;> simp [Tape.init]
      · have hpositive : 0 < position := by omega
        have hpreserved : initializeStore tm repaired
            (cellReg n tape position) = repaired (cellReg n tape position) := by
          unfold initializeStore initializeConfigOps
          exact Structured.Internal.Basic.execList_imm_apply_of_not_mem
            (initializeConfigWrites tm) repaired (cellReg n tape position)
            (initializeConfigWrites_cell_pos_not_mem tm tape position hpositive)
        rw [hpreserved]
        by_cases htape : tape = inputTape n
        · subst tape
          have hinput := hcells.1 position hpositive
          change repaired (cellReg n (inputTape n) position) = _ at hinput
          rw [hinput]
          simp [tapeAt, inputTape]
        · have hblank := hcells.2.2 tape position htape
          change repaired (cellReg n tape position) = 0 at hblank
          rw [hblank]
          unfold tapeAt
          split
          · rename_i hinput
            exfalso
            apply htape
            apply Fin.ext
            simpa [inputTape] using hinput
          · split <;> simp [Tape.init, hposition, symbolCode]

/-- The selected capture-tree leaf executes the fixedValue setup, exact backward
copy, conditional repair, and semantic initialization, ending in a complete
sparse representation of the TM's initial configuration. -/
theorem marshalLeaf_exec_internal (tm : TM n) (x : List Bool) :
    ∃ final steps cost space,
      Structured.Exec (marshalLeaf tm (capturedInput n x))
        (initRegs x) final steps cost space ∧
      Represents tm (tm.initCfg x) final := by
  obtain ⟨setupCost, setupSpace, hsetup⟩ :=
    Structured.Internal.exec_basics_exists (marshalConstants n) (initRegs x)
  have hstartInvariant := marshalStart_invariant_internal n x
  obtain ⟨looped, loopCost, loopSpace, hloop, hloopInvariant⟩ :=
    marshalLoop_invariant_exec_internal n x x.length (marshalStart n x)
      hstartInvariant
  obtain ⟨repairSteps, repairCost, repairSpace, hrepair⟩ :=
    repairCaptured_exec_internal n (capturedInput n x) looped
  obtain ⟨initializeCost, initializeSpace, hinitialize⟩ :=
    Structured.Internal.exec_basics_exists (initializeConfigOps tm)
      (repairStore n (capturedInput n x) looped)
  have hrepresents := initializeStore_represents_internal tm x looped
    hloopInvariant
  let repaired := repairStore n (capturedInput n x) looped
  let final := initializeStore tm repaired
  have htail := Structured.Exec.seq hrepair hinitialize
  have hcopy := Structured.Exec.seq hloop htail
  have hexec := Structured.Exec.seq hsetup hcopy
  refine ⟨final,
    (marshalConstants n).length +
      (marshalLoopSteps n x.length +
        (repairSteps + (initializeConfigOps tm).length)),
    setupCost + (loopCost + (repairCost + initializeCost)),
    max setupSpace (max loopSpace (max repairSpace initializeSpace)), ?_, ?_⟩
  · simpa [marshalLeaf, capturedInput, marshalStart, repaired, final,
      initializeStore] using hexec
  · simpa [repaired, final] using hrepresents

/-- The fixed public-ABI marshaller follows the unique capture-tree path for
the input and establishes the sparse initial TM configuration. -/
theorem marshalInput_exec_internal (tm : TM n) (x : List Bool) :
    ∃ final steps cost space,
      Structured.Exec (marshalInput tm) (initRegs x) final steps cost space ∧
      Represents tm (tm.initCfg x) final := by
  obtain ⟨final, leafSteps, leafCost, leafSpace, hleaf, hrepresents⟩ :=
    marshalLeaf_exec_internal tm x
  have hselected : ∃ steps cost space,
      Structured.Exec
        (marshalLeaf tm
          (captureValues (initRegs x) (captureRegs n) []))
        (initRegs x) final steps cost space := by
    exact ⟨leafSteps, leafCost, leafSpace, by simpa [capturedInput] using hleaf⟩
  obtain ⟨steps, cost, space, hexec⟩ :=
    marshalInput_exec_of_leaf_internal tm x hselected
  exact ⟨final, steps, cost, space, hexec, hrepresents⟩

end Sparse

end TMConfig

end RAM

end Complexity
