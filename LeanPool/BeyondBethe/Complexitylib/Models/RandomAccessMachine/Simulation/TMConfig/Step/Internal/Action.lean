/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Layout
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources

/-!
# Selected TM transition actions -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

variable {n bound : ℕ}

namespace Step


private theorem execList_append (first second : List Structured.Basic)
    (store : Structured.Store) :
    Structured.Basic.execList (first ++ second) store =
      Structured.Basic.execList second (Structured.Basic.execList first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons op rest ih => simp [Structured.Basic.execList, ih]

/-- Representation restricted to one named tape block. -/
private def RepresentsTape (bound : ℕ) (slot : Fin (n + 2))
    (tape : Tape) (store : Structured.Store) : Prop :=
  store (headReg slot) = tape.head ∧
    ∀ position : Fin (bound + 1),
      store (cellBase n bound slot + position.val) =
        symbolCode (tape.cells position.val)

private theorem Represents.tape {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store) (slot : Fin (n + 2)) :
    RepresentsTape bound slot (tapeAt cfg slot) store := by
  constructor
  · have hhead := hrepresents (headField (bound := bound) slot)
    rwa [← headReg_eq_fieldReg_internal] at hhead
  · intro position
    have hcell := hrepresents (cellField slot position)
    rwa [← cellBase_add_eq_fieldReg_internal] at hcell

private theorem configReg_ne_address {n bound reg : ℕ}
    (hreg : reg < registerCount n bound) : reg ≠ addressReg n bound :=
  fun heq => not_lt_of_ge (addressReg_ge_internal n bound) (heq ▸ hreg)

private theorem configReg_ne_value {n bound reg : ℕ}
    (hreg : reg < registerCount n bound) : reg ≠ valueReg n bound :=
  fun heq => not_lt_of_ge (valueReg_ge_internal n bound) (heq ▸ hreg)

/-- On configuration registers, the concrete write block is exactly an update
at the represented head followed by restoration of cell zero. -/
private theorem writeOps_apply (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (store : Structured.Store) {reg : ℕ}
    (hregAddress : reg ≠ addressReg n bound)
    (hregValue : reg ≠ valueReg n bound) :
    Structured.Basic.execList (writeOps n bound slot write) store reg =
      Function.update
        (Function.update store
          (cellBase n bound slot + store (headReg slot)) (writeCode write))
        (cellBase n bound slot) (symbolCode Γ.start) reg := by
  let first :=
    (Structured.Basic.imm (addressReg n bound) (cellBase n bound slot)).exec store
  let addressed :=
    (Structured.Basic.add (addressReg n bound) (addressReg n bound)
      (headReg slot)).exec first
  let valued := (Structured.Basic.imm (valueReg n bound) (writeCode write)).exec addressed
  have haddressHead : addressReg n bound ≠ headReg slot := by
    intro heq
    have hfield := fieldReg_lt_internal (headField (bound := bound) slot)
    rw [← headReg_eq_fieldReg_internal] at hfield
    have hscratch := addressReg_ge_internal n bound
    omega
  have haddressValue : addressReg n bound ≠ valueReg n bound := by
    simp [addressReg, valueReg]
  have hfirstAddress : first (addressReg n bound) = cellBase n bound slot := by
    simp [first, Structured.Basic.exec]
  have hfirstHead : first (headReg slot) = store (headReg slot) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm haddressHead)]
  have haddressedAddress :
      addressed (addressReg n bound) =
        cellBase n bound slot + store (headReg slot) := by
    simp only [addressed, Structured.Basic.exec, Function.update_self]
    rw [hfirstAddress, hfirstHead]
  have hvaluedAddress :
      valued (addressReg n bound) =
        cellBase n bound slot + store (headReg slot) := by
    simp only [valued, Structured.Basic.exec]
    rw [Function.update_of_ne haddressValue, haddressedAddress]
  have hvaluedValue : valued (valueReg n bound) = writeCode write := by
    simp [valued, Structured.Basic.exec]
  have hvaluedConfig : valued reg = store reg := by
    simp [valued, addressed, first, Structured.Basic.exec,
      Function.update_of_ne hregAddress, Function.update_of_ne hregValue]
  simp only [writeOps, Structured.Basic.execList]
  change Function.update
      (Function.update valued (valued (addressReg n bound))
        (valued (valueReg n bound)))
      (cellBase n bound slot) (symbolCode Γ.start) reg = _
  rw [hvaluedAddress, hvaluedValue]
  by_cases hzero : reg = cellBase n bound slot
  · subst reg
    rw [Function.update_self, Function.update_self]
  · by_cases htarget : reg = cellBase n bound slot + store (headReg slot)
    · rw [Function.update_of_ne hzero, Function.update_of_ne hzero]
      subst reg
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzero, Function.update_of_ne hzero,
        Function.update_of_ne htarget, Function.update_of_ne htarget]
      exact hvaluedConfig

private theorem headReg_ne_cellReg (headSlot cellSlot : Fin (n + 2))
    (position : Fin (bound + 1)) :
    headReg headSlot ≠ cellBase n bound cellSlot + position.val := by
  intro heq
  rw [headReg_eq_fieldReg_internal,
    cellBase_add_eq_fieldReg_internal] at heq
  have hfield := fieldReg_injective_internal heq
  cases hfield

private theorem cellReg_ne_cellReg_of_slot_ne {first second : Fin (n + 2)}
    (hne : first ≠ second) (firstPosition secondPosition : Fin (bound + 1)) :
    cellBase n bound first + firstPosition.val ≠
      cellBase n bound second + secondPosition.val := by
  intro heq
  rw [cellBase_add_eq_fieldReg_internal,
    cellBase_add_eq_fieldReg_internal] at heq
  have hfield := fieldReg_injective_internal heq
  change Sum.inr (Sum.inr (first, firstPosition)) =
    Sum.inr (Sum.inr (second, secondPosition)) at hfield
  have hpairs := Sum.inr.inj (Sum.inr.inj hfield)
  exact hne (congrArg Prod.fst hpairs)

private theorem writeOps_head (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (store : Structured.Store) :
    Structured.Basic.execList (writeOps n bound slot write) store (headReg slot) =
      store (headReg slot) := by
  have hreg : headReg slot < registerCount n bound := by
    rw [headReg_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  rw [writeOps_apply n bound slot write store
    (configReg_ne_address hreg) (configReg_ne_value hreg)]
  have hzero : headReg slot ≠ cellBase n bound slot := by
    simp [headReg, cellBase]
    omega
  have htarget :
      headReg slot ≠ cellBase n bound slot + store (headReg slot) := by
    simp [headReg, cellBase]
    omega
  rw [Function.update_of_ne hzero, Function.update_of_ne htarget]

private theorem writeOps_cells (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (tape : Tape) (store : Structured.Store)
    (hrepresents : RepresentsTape bound slot tape store)
    (hstart : tape.cells 0 = Γ.start)
    (position : Fin (bound + 1)) :
    Structured.Basic.execList (writeOps n bound slot write) store
        (cellBase n bound slot + position.val) =
      symbolCode ((tape.write write.toΓ).cells position.val) := by
  have hstoreHead : store (headReg slot) = tape.head := hrepresents.1
  have hstoreCell := hrepresents.2 position
  have hreg : cellBase n bound slot + position.val < registerCount n bound := by
    rw [cellBase_add_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  rw [writeOps_apply n bound slot write store
    (configReg_ne_address hreg) (configReg_ne_value hreg)]
  rw [hstoreHead]
  by_cases hheadZero : tape.head = 0
  · rw [Tape.write, ite_eq_left hheadZero]
    by_cases hpositionZero : position.val = 0
    · rw [hheadZero, hpositionZero, Nat.add_zero, Function.update_self, hstart]
    · have htarget :
          cellBase n bound slot + position.val ≠ cellBase n bound slot + tape.head := by
        omega
      have hbase :
          cellBase n bound slot + position.val ≠ cellBase n bound slot := by
        omega
      rw [Function.update_of_ne hbase, Function.update_of_ne htarget, hstoreCell]
  · rw [Tape.write, ite_eq_right hheadZero]
    change Function.update
        (Function.update store (cellBase n bound slot + tape.head) (writeCode write))
          (cellBase n bound slot) (symbolCode Γ.start)
          (cellBase n bound slot + position.val) =
      symbolCode (Function.update tape.cells tape.head write.toΓ position.val)
    by_cases hpositionHead : position.val = tape.head
    · have hpositionZero : position.val ≠ 0 := by omega
      have hbase :
          cellBase n bound slot + position.val ≠ cellBase n bound slot := by
        omega
      rw [Function.update_of_ne hbase]
      have htarget :
          cellBase n bound slot + position.val = cellBase n bound slot + tape.head := by
        omega
      rw [htarget, Function.update_self, hpositionHead, Function.update_self]
      rfl
    · by_cases hpositionZero : position.val = 0
      · rw [hpositionZero, Nat.add_zero, Function.update_self,
          Function.update_of_ne (Ne.symm hheadZero), hstart]
      · have htarget :
            cellBase n bound slot + position.val ≠ cellBase n bound slot + tape.head := by
          omega
        have hbase :
            cellBase n bound slot + position.val ≠ cellBase n bound slot := by
          omega
        rw [Function.update_of_ne hbase, Function.update_of_ne htarget,
          Function.update_of_ne hpositionHead, hstoreCell]

private theorem writeOps_tape (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (tape : Tape) (store : Structured.Store)
    (hrepresents : RepresentsTape bound slot tape store)
    (hstart : tape.cells 0 = Γ.start) :
    RepresentsTape bound slot (tape.write write.toΓ)
      (Structured.Basic.execList (writeOps n bound slot write) store) := by
  constructor
  · rw [Tape.write_head]
    exact (writeOps_head n bound slot write store).trans
      hrepresents.1
  · exact writeOps_cells n bound slot write tape store hrepresents hstart

private theorem moveOps_apply_of_ne (n bound : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (store : Structured.Store) {reg : ℕ}
    (hne : reg ≠ headReg slot) :
    Structured.Basic.execList (moveOps n bound slot direction) store reg = store reg := by
  cases direction <;>
    simp [moveOps, Structured.Basic.execList, Structured.Basic.exec,
      Function.update_of_ne hne]

private theorem moveOps_tape (n bound : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (tape : Tape) (store : Structured.Store)
    (hrepresents : RepresentsTape bound slot tape store)
    (hone : store (oneReg n bound) = 1) :
    RepresentsTape bound slot (tape.move direction)
      (Structured.Basic.execList (moveOps n bound slot direction) store) := by
  constructor
  · cases direction <;>
      simp [moveOps, Structured.Basic.execList, Structured.Basic.exec, Tape.move,
        hrepresents.1, hone]
  · intro position
    rw [moveOps_apply_of_ne n bound slot direction store
      (headReg_ne_cellReg slot slot position).symm]
    rw [Tape.move_cells]
    exact hrepresents.2 position

private theorem writeOps_one (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (store : Structured.Store)
    (hhead : store (headReg slot) ≤ bound) :
    Structured.Basic.execList (writeOps n bound slot write) store
        (oneReg n bound) = store (oneReg n bound) := by
  have honeAddress : oneReg n bound ≠ addressReg n bound := by
    simp [oneReg, addressReg]
  have honeValue : oneReg n bound ≠ valueReg n bound := by
    simp [oneReg, valueReg]
  have honeBase : oneReg n bound ≠ cellBase n bound slot := by
    intro heq
    have hcell := fieldReg_lt_internal
      (cellField slot (⟨0, by omega⟩ : Fin (bound + 1)))
    rw [← cellBase_add_eq_fieldReg_internal] at hcell
    simp only [Nat.add_zero] at hcell
    have hone := oneReg_ge_internal n bound
    omega
  let position : Fin (bound + 1) := ⟨store (headReg slot), by omega⟩
  have htargetLt :
      cellBase n bound slot + store (headReg slot) < registerCount n bound := by
    change cellBase n bound slot + position.val < registerCount n bound
    rw [cellBase_add_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  have honeTarget :
      oneReg n bound ≠ cellBase n bound slot + store (headReg slot) := by
    intro heq
    have hone := oneReg_ge_internal n bound
    omega
  rw [writeOps_apply n bound slot write store honeAddress honeValue,
    Function.update_of_ne honeBase, Function.update_of_ne honeTarget]

private theorem writeMoveOps_tape_internal (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (tape : Tape) (store : Structured.Store)
    (hrepresents : RepresentsTape bound slot tape store)
    (hhead : tape.head ≤ bound) (hstart : tape.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1) :
    RepresentsTape bound slot (tape.writeAndMove write.toΓ direction)
      (Structured.Basic.execList (writeMoveOps n bound slot write direction) store) := by
  let written := Structured.Basic.execList (writeOps n bound slot write) store
  have hwritten := writeOps_tape n bound slot write tape store hrepresents hstart
  have honeWritten : written (oneReg n bound) = 1 := by
    exact (writeOps_one n bound slot write store (hrepresents.1 ▸ hhead)).trans hone
  rw [writeMoveOps, execList_append]
  exact moveOps_tape n bound slot direction (tape.write write.toΓ) written
    hwritten honeWritten

private theorem headReg_ne_headReg_of_slot_ne {first second : Fin (n + 2)}
    (hne : first ≠ second) : headReg first ≠ headReg second := by
  intro heq
  apply hne
  apply Fin.ext
  simp [headReg] at heq
  omega

theorem writeMoveOps_one_internal (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (store : Structured.Store)
    (hhead : store (headReg slot) ≤ bound) :
    Structured.Basic.execList (writeMoveOps n bound slot write direction) store
        (oneReg n bound) = store (oneReg n bound) := by
  let written := Structured.Basic.execList (writeOps n bound slot write) store
  have honeWritten : written (oneReg n bound) = store (oneReg n bound) := by
    change Structured.Basic.execList (writeOps n bound slot write) store
        (oneReg n bound) = store (oneReg n bound)
    exact writeOps_one n bound slot write store hhead
  have honeHead : oneReg n bound ≠ headReg slot := by
    intro heq
    have hheadReg := fieldReg_lt_internal (headField (bound := bound) slot)
    rw [← headReg_eq_fieldReg_internal] at hheadReg
    have hone := oneReg_ge_internal n bound
    omega
  rw [writeMoveOps, execList_append,
    moveOps_apply_of_ne n bound slot direction written honeHead, honeWritten]

private theorem writeMoveOps_otherTape_internal (n bound : ℕ)
    {slot other : Fin (n + 2)} (hne : slot ≠ other)
    (write : Γw) (direction : Dir3) (otherTape : Tape)
    (store : Structured.Store)
    (hother : RepresentsTape bound other otherTape store)
    (hhead : store (headReg slot) ≤ bound) :
    RepresentsTape bound other otherTape
      (Structured.Basic.execList (writeMoveOps n bound slot write direction) store) := by
  let written := Structured.Basic.execList (writeOps n bound slot write) store
  let selectedPosition : Fin (bound + 1) :=
    ⟨store (headReg slot), by omega⟩
  have hotherHeadReg : headReg other < registerCount n bound := by
    rw [headReg_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  have hwriteHead : written (headReg other) = store (headReg other) := by
    change Structured.Basic.execList (writeOps n bound slot write) store
        (headReg other) = store (headReg other)
    rw [writeOps_apply n bound slot write store
      (configReg_ne_address hotherHeadReg) (configReg_ne_value hotherHeadReg)]
    have hbase : headReg other ≠ cellBase n bound slot := by
      simpa using
        (headReg_ne_cellReg other slot (⟨0, by omega⟩ : Fin (bound + 1)))
    have htarget :
        headReg other ≠ cellBase n bound slot + store (headReg slot) := by
      simpa [selectedPosition] using
        (headReg_ne_cellReg other slot selectedPosition)
    rw [Function.update_of_ne hbase, Function.update_of_ne htarget]
  have hmoveHead :
      Structured.Basic.execList (moveOps n bound slot direction) written
          (headReg other) = written (headReg other) :=
    moveOps_apply_of_ne n bound slot direction written
      (headReg_ne_headReg_of_slot_ne (Ne.symm hne))
  constructor
  · rw [writeMoveOps, execList_append, hmoveHead, hwriteHead]
    exact hother.1
  · intro position
    have hotherCellReg :
        cellBase n bound other + position.val < registerCount n bound := by
      rw [cellBase_add_eq_fieldReg_internal]
      exact fieldReg_lt_internal _
    have hwriteCell :
        written (cellBase n bound other + position.val) =
          store (cellBase n bound other + position.val) := by
      change Structured.Basic.execList (writeOps n bound slot write) store
          (cellBase n bound other + position.val) =
        store (cellBase n bound other + position.val)
      rw [writeOps_apply n bound slot write store
        (configReg_ne_address hotherCellReg) (configReg_ne_value hotherCellReg)]
      have hbase :
          cellBase n bound other + position.val ≠ cellBase n bound slot := by
        simpa using
          (cellReg_ne_cellReg_of_slot_ne (Ne.symm hne) position
            (⟨0, by omega⟩ : Fin (bound + 1)))
      have htarget :
          cellBase n bound other + position.val ≠
            cellBase n bound slot + store (headReg slot) := by
        simpa [selectedPosition] using
          (cellReg_ne_cellReg_of_slot_ne (Ne.symm hne) position selectedPosition)
      rw [Function.update_of_ne hbase, Function.update_of_ne htarget]
    have hmoveCell :
        Structured.Basic.execList (moveOps n bound slot direction) written
            (cellBase n bound other + position.val) =
          written (cellBase n bound other + position.val) :=
      moveOps_apply_of_ne n bound slot direction written
        (headReg_ne_cellReg slot other position).symm
    rw [writeMoveOps, execList_append, hmoveCell, hwriteCell]
    exact hother.2 position

private theorem RepresentsTape.stateUpdate (bound : ℕ) (slot : Fin (n + 2))
    (tape : Tape) (store : Structured.Store) (state : ℕ)
    (hrepresents : RepresentsTape bound slot tape store) :
    RepresentsTape bound slot tape
      ((Structured.Basic.imm 0 state).exec store) := by
  constructor
  · simpa [Structured.Basic.exec, headReg, Function.update_of_ne] using
      hrepresents.1
  · intro position
    simpa [Structured.Basic.exec, cellBase, Function.update_of_ne] using
      hrepresents.2 position

private theorem moveOps_one (n bound : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (store : Structured.Store) :
    Structured.Basic.execList (moveOps n bound slot direction) store
        (oneReg n bound) = store (oneReg n bound) := by
  apply moveOps_apply_of_ne
  intro heq
  have hhead := fieldReg_lt_internal (headField (bound := bound) slot)
  rw [← headReg_eq_fieldReg_internal] at hhead
  have hone := oneReg_ge_internal n bound
  omega

private theorem moveOps_zero (n bound : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (store : Structured.Store) :
    Structured.Basic.execList (moveOps n bound slot direction) store 0 = store 0 := by
  apply moveOps_apply_of_ne
  simp [headReg]
  omega

private theorem moveOps_otherTape (n bound : ℕ)
    {slot other : Fin (n + 2)} (hne : slot ≠ other)
    (direction : Dir3) (otherTape : Tape) (store : Structured.Store)
    (hother : RepresentsTape bound other otherTape store) :
    RepresentsTape bound other otherTape
      (Structured.Basic.execList (moveOps n bound slot direction) store) := by
  constructor
  · rw [moveOps_apply_of_ne n bound slot direction store
      (headReg_ne_headReg_of_slot_ne (Ne.symm hne))]
    exact hother.1
  · intro position
    rw [moveOps_apply_of_ne n bound slot direction store
      (headReg_ne_cellReg slot other position).symm]
    exact hother.2 position

private theorem writeMoveOps_zero (n bound : ℕ) (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (store : Structured.Store) :
    Structured.Basic.execList (writeMoveOps n bound slot write direction) store 0 =
      store 0 := by
  let written := Structured.Basic.execList (writeOps n bound slot write) store
  have hzeroAddress : 0 ≠ addressReg n bound := by
    simp [addressReg, scratchBase, registerCount]
  have hzeroValue : 0 ≠ valueReg n bound := by
    simp [valueReg, scratchBase, registerCount]
  have hzeroWritten : written 0 = store 0 := by
    change Structured.Basic.execList (writeOps n bound slot write) store 0 = store 0
    rw [writeOps_apply n bound slot write store hzeroAddress hzeroValue]
    have hbase : 0 ≠ cellBase n bound slot := by
      simp [cellBase]
      omega
    have htarget : 0 ≠ cellBase n bound slot + store (headReg slot) := by
      simp [cellBase]
      omega
    rw [Function.update_of_ne hbase, Function.update_of_ne htarget]
  rw [writeMoveOps, execList_append,
    moveOps_zero n bound slot direction written, hzeroWritten]

private theorem workTape_injective (n : ℕ) :
    Function.Injective (workTape : Fin n → Fin (n + 2)) := by
  intro first second heq
  apply Fin.ext
  simpa [workTape] using congrArg Fin.val heq

private theorem inputTape_ne_workTape (n : ℕ) (i : Fin n) :
    inputTape n ≠ workTape i := by
  intro heq
  have := congrArg Fin.val heq
  simp [inputTape, workTape] at this

private theorem outputTape_ne_workTape (n : ℕ) (i : Fin n) :
    outputTape n ≠ workTape i := by
  intro heq
  have hi := i.isLt
  have := congrArg Fin.val heq
  simp [outputTape, workTape] at this
  omega

private theorem inputTape_ne_outputTape (n : ℕ) :
    inputTape n ≠ outputTape n := by
  intro heq
  have := congrArg Fin.val heq
  simp [inputTape, outputTape] at this

/-- Reassemble the fieldwise configuration representation from the state and
the three kinds of named tape blocks. -/
private theorem represents_of_named_tapes {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstate : store 0 = stateCode tm cfg.state)
    (hinput : RepresentsTape bound (inputTape n) cfg.input store)
    (hwork : ∀ i, RepresentsTape bound (workTape i) (cfg.work i) store)
    (houtput : RepresentsTape bound (outputTape n) cfg.output store) :
    Represents tm bound cfg store := by
  intro field
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstateFin⟩
    have hzero : state = 0 := by omega
    subst state
    simpa [fieldReg_state_internal, fieldValue] using! hstate
  · rcases headOrCell with head | cell
    · change store (headReg head) = (tapeAt cfg head).head
      by_cases hinputSlot : head = inputTape n
      · subst head
        rw [hinput.1]
        simpa [inputTape] using
          congrArg Tape.head (tapeAt_input_internal cfg).symm
      · by_cases houtputSlot : head = outputTape n
        · subst head
          rw [houtput.1]
          simpa [outputTape] using
            congrArg Tape.head (tapeAt_output_internal cfg).symm
        · let i : Fin n := ⟨head.val - 1, by
            have hpositive : 0 < head.val := by
              have hnezero : head.val ≠ 0 := by
                intro hzero
                apply hinputSlot
                apply Fin.ext
                simpa [inputTape] using hzero
              omega
            have hnotOutput : head.val ≠ n + 1 := by
              intro heq
              apply houtputSlot
              apply Fin.ext
              simpa [outputTape] using heq
            omega⟩
          have hhead : head = workTape i := by
            apply Fin.ext
            simp [i, workTape]
            have hpositive : 0 < head.val := by
              have hnezero : head.val ≠ 0 := by
                intro hzero
                apply hinputSlot
                apply Fin.ext
                simpa [inputTape] using hzero
              omega
            omega
          rw [hhead, (hwork i).1]
          simpa [workTape] using
            congrArg Tape.head (tapeAt_work_internal cfg i).symm
    · rcases cell with ⟨tape, position⟩
      simp only [fieldValue]
      change store (fieldReg (cellField tape position)) =
        symbolCode ((tapeAt cfg tape).cells position.val)
      rw [← cellBase_add_eq_fieldReg_internal]
      by_cases hinputSlot : tape = inputTape n
      · subst tape
        rw [hinput.2 position]
        simpa [inputTape] using congrArg (fun t => symbolCode (t.cells position.val))
          (tapeAt_input_internal cfg).symm
      · by_cases houtputSlot : tape = outputTape n
        · subst tape
          rw [houtput.2 position]
          simpa [outputTape] using congrArg (fun t => symbolCode (t.cells position.val))
            (tapeAt_output_internal cfg).symm
        · let i : Fin n := ⟨tape.val - 1, by
            have hpositive : 0 < tape.val := by
              have hnezero : tape.val ≠ 0 := by
                intro hzero
                apply hinputSlot
                apply Fin.ext
                simpa [inputTape] using hzero
              omega
            have hnotOutput : tape.val ≠ n + 1 := by
              intro heq
              apply houtputSlot
              apply Fin.ext
              simpa [outputTape] using heq
            omega⟩
          have htape : tape = workTape i := by
            apply Fin.ext
            simp [i, workTape]
            have hpositive : 0 < tape.val := by
              have hnezero : tape.val ≠ 0 := by
                intro hzero
                apply hinputSlot
                apply Fin.ext
                simpa [inputTape] using hzero
              omega
            omega
          rw [htape, (hwork i).2 position]
          simpa [workTape] using congrArg (fun t => symbolCode (t.cells position.val))
            (tapeAt_work_internal cfg i).symm

/-- Invariant after updating a prefix of the work tapes for one selected
transition. -/
private structure WorkPrefix (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (nextState : tm.Q)
    (inputDirection : Dir3) (workWrites : Fin n → Γw)
    (workDirections : Fin n → Dir3) (processed : List (Fin n))
    (store : Structured.Store) : Prop where
  state : store 0 = stateCode tm nextState
  one : store (oneReg n bound) = 1
  input : RepresentsTape bound (inputTape n)
    (cfg.input.move inputDirection) store
  work : ∀ i, RepresentsTape bound (workTape i)
    (if i ∈ processed then
      (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)
    else cfg.work i) store
  output : RepresentsTape bound (outputTape n) cfg.output store

private theorem actionPrelude_workPrefix {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (nextState : tm.Q) (inputDirection : Dir3)
    (workWrites : Fin n → Γw) (workDirections : Fin n → Dir3)
    (hrepresents : Represents tm bound cfg store)
    (hone : store (oneReg n bound) = 1) :
    let initialized := (Structured.Basic.imm 0 (stateCode tm nextState)).exec store
    let final := Structured.Basic.execList
      (moveOps n bound (inputTape n) inputDirection) initialized
    WorkPrefix tm bound cfg nextState inputDirection workWrites workDirections [] final := by
  let initialized := (Structured.Basic.imm 0 (stateCode tm nextState)).exec store
  let final := Structured.Basic.execList
    (moveOps n bound (inputTape n) inputDirection) initialized
  have honeReg : oneReg n bound ≠ 0 := by
    simp [oneReg, scratchBase, registerCount]
  have honeInitialized : initialized (oneReg n bound) = 1 := by
    simpa [initialized, Structured.Basic.exec,
      Function.update_of_ne honeReg] using hone
  have hinputStore : RepresentsTape bound (inputTape n) cfg.input store := by
    have htape := Represents.tape hrepresents (inputTape n)
    simpa [inputTape] using! htape
  have hinputInitialized :
      RepresentsTape bound (inputTape n) cfg.input initialized :=
    hinputStore.stateUpdate bound (inputTape n) cfg.input store
      (stateCode tm nextState)
  have hworkInitialized : ∀ i,
      RepresentsTape bound (workTape i) (cfg.work i) initialized := by
    intro i
    have htape := Represents.tape hrepresents (workTape i)
    have hnamed : RepresentsTape bound (workTape i) (cfg.work i) store := by
      rw [show tapeAt cfg (workTape i) = cfg.work i by
        simpa [workTape] using tapeAt_work_internal cfg i] at htape
      exact htape
    exact hnamed.stateUpdate bound (workTape i) (cfg.work i) store
      (stateCode tm nextState)
  have houtputStore : RepresentsTape bound (outputTape n) cfg.output store := by
    have htape := Represents.tape hrepresents (outputTape n)
    rw [show tapeAt cfg (outputTape n) = cfg.output by
      simpa [outputTape] using tapeAt_output_internal cfg] at htape
    exact htape
  have houtputInitialized :
      RepresentsTape bound (outputTape n) cfg.output initialized :=
    houtputStore.stateUpdate bound (outputTape n) cfg.output store
      (stateCode tm nextState)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [moveOps_zero n bound (inputTape n) inputDirection initialized]
    simp [initialized, Structured.Basic.exec]
  · exact (moveOps_one n bound (inputTape n) inputDirection initialized).trans
      honeInitialized
  · exact moveOps_tape n bound (inputTape n) inputDirection cfg.input initialized
      hinputInitialized honeInitialized
  · intro i
    simpa using moveOps_otherTape n bound
      (inputTape_ne_workTape n i) inputDirection (cfg.work i) initialized
      (hworkInitialized i)
  · exact moveOps_otherTape n bound (inputTape_ne_outputTape n) inputDirection
      cfg.output initialized houtputInitialized

private theorem workPrefix_step {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3} {processed : List (Fin n)}
    {store : Structured.Store}
    (hprefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections processed store)
    (i : Fin n) (hfresh : i ∉ processed)
    (hhead : (cfg.work i).head ≤ bound)
    (hstart : (cfg.work i).cells 0 = Γ.start) :
    WorkPrefix tm bound cfg nextState inputDirection workWrites workDirections
      (i :: processed)
      (Structured.Basic.execList
        (writeMoveOps n bound (workTape i) (workWrites i) (workDirections i)) store) := by
  have hselected : RepresentsTape bound (workTape i) (cfg.work i) store := by
    simpa [hfresh] using hprefix.work i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (writeMoveOps_zero n bound (workTape i) (workWrites i)
      (workDirections i) store).trans hprefix.state
  · exact (writeMoveOps_one_internal n bound (workTape i) (workWrites i)
      (workDirections i) store (hselected.1 ▸ hhead)).trans hprefix.one
  · exact writeMoveOps_otherTape_internal n bound
      (Ne.symm (inputTape_ne_workTape n i)) (workWrites i) (workDirections i)
      (cfg.input.move inputDirection) store hprefix.input (hselected.1 ▸ hhead)
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using writeMoveOps_tape_internal n bound (workTape i)
        (workWrites i) (workDirections i) (cfg.work i) store hselected hhead
        hstart hprefix.one
    · have hslots : workTape i ≠ workTape j := by
        exact fun heq => hji ((workTape_injective n) heq).symm
      simpa [hji] using writeMoveOps_otherTape_internal n bound hslots
        (workWrites i) (workDirections i)
        (if j ∈ processed then
          (cfg.work j).writeAndMove (workWrites j).toΓ (workDirections j)
        else cfg.work j) store (hprefix.work j) (hselected.1 ▸ hhead)
  · exact writeMoveOps_otherTape_internal n bound
      (outputTape_ne_workTape n i).symm (workWrites i) (workDirections i)
      cfg.output store hprefix.output (hselected.1 ▸ hhead)

private theorem workPrefix_list {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3}
    (items processed : List (Fin n)) {store : Structured.Store}
    (hprefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections processed store)
    (hfresh : ∀ i, i ∈ items → i ∉ processed)
    (hnodup : items.Nodup)
    (hheads : ∀ i, (cfg.work i).head ≤ bound)
    (hstarts : ∀ i, (cfg.work i).cells 0 = Γ.start) :
    WorkPrefix tm bound cfg nextState inputDirection workWrites workDirections
      (items.reverse ++ processed)
      (Structured.Basic.execList
        (items.flatMap (fun i => writeMoveOps n bound (workTape i)
          (workWrites i) (workDirections i))) store) := by
  induction items generalizing processed store with
  | nil => simpa using! hprefix
  | cons i rest ih =>
      have hinot : i ∉ processed := hfresh i (by simp)
      have hnext := workPrefix_step hprefix i hinot (hheads i) (hstarts i)
      have hrestFresh : ∀ j, j ∈ rest → j ∉ i :: processed := by
        intro j hj hmem
        rcases List.mem_cons.mp hmem with heq | hprocessed
        · subst j
          exact (List.nodup_cons.mp hnodup).1 hj
        · exact hfresh j (by simp [hj]) hprocessed
      have hfinal := ih (processed := i :: processed) hnext hrestFresh
        (List.nodup_cons.mp hnodup).2
      simpa [List.flatMap_cons, execList_append, List.reverse_cons,
        List.append_assoc] using hfinal

theorem actionOps_represents_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1) :
    Represents tm bound next
      (Structured.Basic.execList
        (actionOps tm bound cfg.state (readSymbols cfg)) store) := by
  have hnotHalted := TM.state_ne_qhalt_of_step hstep
  rcases hdelta : tm.δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read with
    ⟨nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection⟩
  rw [TM.step, ite_eq_right hnotHalted, hdelta] at hstep
  dsimp only at hstep
  injection hstep with hnext
  subst next
  have hreadInput :
      readSymbols cfg (inputTape n) = cfg.input.read := by
    simpa [readSymbols, inputTape] using
      congrArg Tape.read (tapeAt_input_internal cfg)
  have hreadWork :
      (fun i => readSymbols cfg (workTape i)) =
        (fun i => (cfg.work i).read) := by
    funext i
    simpa [readSymbols, workTape] using
      congrArg Tape.read (tapeAt_work_internal cfg i)
  have hreadOutput :
      readSymbols cfg (outputTape n) = cfg.output.read := by
    simpa [readSymbols, outputTape] using
      congrArg Tape.read (tapeAt_output_internal cfg)
  let initialized :=
    (Structured.Basic.imm 0 (stateCode tm nextState)).exec store
  let afterInput := Structured.Basic.execList
    (moveOps n bound (inputTape n) inputDirection) initialized
  have hprefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections [] afterInput := by
    exact actionPrelude_workPrefix nextState inputDirection workWrites
      workDirections hrepresents hone
  have hworkHeads : ∀ i, (cfg.work i).head ≤ bound := by
    intro i
    have hhead := hheads (workTape i)
    rw [show tapeAt cfg (workTape i) = cfg.work i by
      simpa [workTape] using tapeAt_work_internal cfg i] at hhead
    exact hhead
  let afterWork := Structured.Basic.execList
    ((List.finRange n).flatMap (fun i =>
      writeMoveOps n bound (workTape i) (workWrites i) (workDirections i)))
      afterInput
  have hworkPrefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections ((List.finRange n).reverse ++ []) afterWork := by
    exact workPrefix_list (List.finRange n) [] hprefix (by simp)
      (List.nodup_finRange n) hworkHeads hworkStart
  have hworkFinal : ∀ i,
      RepresentsTape bound (workTape i)
        ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i))
        afterWork := by
    intro i
    simpa using hworkPrefix.work i
  have houtputHead : cfg.output.head ≤ bound := by
    have hhead := hheads (outputTape n)
    rw [show tapeAt cfg (outputTape n) = cfg.output by
      simpa [outputTape] using tapeAt_output_internal cfg] at hhead
    exact hhead
  let final := Structured.Basic.execList
    (writeMoveOps n bound (outputTape n) outputWrite outputDirection) afterWork
  have hstateFinal : final 0 = stateCode tm nextState := by
    exact (writeMoveOps_zero n bound (outputTape n) outputWrite outputDirection
      afterWork).trans hworkPrefix.state
  have honeFinal : final (oneReg n bound) = 1 := by
    exact (writeMoveOps_one_internal n bound (outputTape n) outputWrite
      outputDirection afterWork (hworkPrefix.output.1 ▸ houtputHead)).trans
        hworkPrefix.one
  have hinputFinal : RepresentsTape bound (inputTape n)
      (cfg.input.move inputDirection) final := by
    exact writeMoveOps_otherTape_internal n bound
      (inputTape_ne_outputTape n).symm outputWrite outputDirection
      (cfg.input.move inputDirection) afterWork hworkPrefix.input
      (hworkPrefix.output.1 ▸ houtputHead)
  have hworkFinal' : ∀ i, RepresentsTape bound (workTape i)
      ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)) final := by
    intro i
    exact writeMoveOps_otherTape_internal n bound
      (outputTape_ne_workTape n i) outputWrite outputDirection
      ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i))
      afterWork (hworkFinal i) (hworkPrefix.output.1 ▸ houtputHead)
  have houtputFinal : RepresentsTape bound (outputTape n)
      (cfg.output.writeAndMove outputWrite.toΓ outputDirection) final := by
    exact writeMoveOps_tape_internal n bound (outputTape n) outputWrite
      outputDirection cfg.output afterWork hworkPrefix.output houtputHead
      houtputStart hworkPrefix.one
  have hfinalRepresents :
      Represents tm bound
        { state := nextState
          input := cfg.input.move inputDirection
          work := fun i =>
            (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)
          output := cfg.output.writeAndMove outputWrite.toΓ outputDirection }
        final := by
    exact represents_of_named_tapes hstateFinal hinputFinal hworkFinal'
      houtputFinal
  simpa [actionOps, hreadInput, hreadWork, hreadOutput, hdelta,
    initialized, afterInput, afterWork, final, execList_append,
    Structured.Basic.execList, List.append_assoc] using
    hfinalRepresents

private abbrev StepEnvelope (tm : TM n) (bound : ℕ) :=
  Structured.Internal.StoreEnvelope (registerLimit n bound) (wordBound tm bound)

private abbrev StepEnvelopeChain (tm : TM n) (bound : ℕ) :=
  Structured.Internal.Basic.EnvelopeChain (registerLimit n bound) (wordBound tm bound)

private theorem registerCount_lt_registerLimit' (n bound : ℕ) :
    registerCount n bound < registerLimit n bound := by
  simp [registerLimit, scratchBase]
  omega

private theorem registerLimit_le_wordBound' (tm : TM n) (bound : ℕ) :
    registerLimit n bound ≤ wordBound tm bound :=
  le_max_left _ _

private theorem headReg_lt_registerLimit (n bound : ℕ)
    (tape : Fin (n + 2)) : headReg tape < registerLimit n bound := by
  have hhead := fieldReg_lt_internal (headField (bound := bound) tape)
  rw [← headReg_eq_fieldReg_internal] at hhead
  exact lt_trans hhead (registerCount_lt_registerLimit' n bound)

private theorem cellBase_lt_registerLimit (n bound : ℕ)
    (tape : Fin (n + 2)) : cellBase n bound tape < registerLimit n bound := by
  have hcell := fieldReg_lt_internal
    (cellField tape (⟨0, by omega⟩ : Fin (bound + 1)))
  rw [← cellBase_add_eq_fieldReg_internal] at hcell
  simpa using lt_trans hcell (registerCount_lt_registerLimit' n bound)

private theorem smallValue_le_wordBound (tm : TM n) (bound value : ℕ)
    (hvalue : value ≤ 3) : value ≤ wordBound tm bound := by
  have hthree : 3 ≤ registerLimit n bound := by
    simp [registerLimit, scratchBase, registerCount]
  exact le_trans hvalue (le_trans hthree (registerLimit_le_wordBound' tm bound))

private theorem moveOps_envelopeChain (tm : TM n) (bound : ℕ)
    (tape : Fin (n + 2)) (direction : Dir3) (store : Structured.Store)
    (henvelope : StepEnvelope tm bound store)
    (hhead : store (headReg tape) ≤ bound)
    (hone : store (oneReg n bound) = 1) :
    StepEnvelopeChain tm bound (moveOps n bound tape direction) store := by
  have hindex := headReg_lt_registerLimit n bound tape
  have hbound : bound + 1 ≤ wordBound tm bound := by
    exact le_trans (le_max_right _ _)
      (le_max_right (registerLimit n bound) _)
  cases direction with
  | stay => exact henvelope
  | left =>
      have hfinal : StepEnvelope tm bound
          ((Structured.Basic.sub (headReg tape) (headReg tape)
            (oneReg n bound)).exec store) := by
        apply henvelope.execBasic
        · exact hindex
        · simp only [Structured.Internal.Basic.writeValue]
          omega
      exact ⟨henvelope, hfinal⟩
  | right =>
      have hfinal : StepEnvelope tm bound
          ((Structured.Basic.add (headReg tape) (headReg tape)
            (oneReg n bound)).exec store) := by
        apply henvelope.execBasic
        · exact hindex
        · simp only [Structured.Internal.Basic.writeValue]
          rw [hone]
          omega
      exact ⟨henvelope, hfinal⟩

private theorem writeOps_envelopeChain (tm : TM n) (bound : ℕ)
    (tape : Fin (n + 2)) (write : Γw) (store : Structured.Store)
    (henvelope : StepEnvelope tm bound store)
    (hhead : store (headReg tape) ≤ bound) :
    StepEnvelopeChain tm bound (writeOps n bound tape write) store := by
  let first :=
    (Structured.Basic.imm (addressReg n bound) (cellBase n bound tape)).exec store
  let addressed :=
    (Structured.Basic.add (addressReg n bound) (addressReg n bound)
      (headReg tape)).exec first
  let valued := (Structured.Basic.imm (valueReg n bound) (writeCode write)).exec addressed
  let stored := (Structured.Basic.store (addressReg n bound)
    (valueReg n bound)).exec valued
  let final :=
    (Structured.Basic.imm (cellBase n bound tape) (symbolCode Γ.start)).exec stored
  have hscratch := scratch_lt_registerLimit_internal n bound
  have hbaseLt := cellBase_lt_registerLimit n bound tape
  have hbaseBound : cellBase n bound tape ≤ wordBound tm bound :=
    le_trans (Nat.le_of_lt hbaseLt) (registerLimit_le_wordBound' tm bound)
  have hfirst : StepEnvelope tm bound first := by
    apply henvelope.execBasic
    · exact hscratch.2.2.2.1
    · simpa [Structured.Internal.Basic.writeValue] using hbaseBound
  have haddressHead : addressReg n bound ≠ headReg tape := by
    intro heq
    have haddress := addressReg_ge_internal n bound
    have hheadReg := fieldReg_lt_internal (headField (bound := bound) tape)
    rw [← headReg_eq_fieldReg_internal] at hheadReg
    omega
  have hfirstAddress : first (addressReg n bound) = cellBase n bound tape := by
    simp [first, Structured.Basic.exec]
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm haddressHead)]
  let position : Fin (bound + 1) := ⟨store (headReg tape), by omega⟩
  have htargetLt :
      cellBase n bound tape + store (headReg tape) < registerCount n bound := by
    change cellBase n bound tape + position.val < registerCount n bound
    rw [cellBase_add_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  have htargetBound :
      cellBase n bound tape + store (headReg tape) ≤ wordBound tm bound := by
    exact le_trans (Nat.le_of_lt htargetLt)
      (le_trans (Nat.le_of_lt (registerCount_lt_registerLimit' n bound))
        (registerLimit_le_wordBound' tm bound))
  have haddressed : StepEnvelope tm bound addressed := by
    apply hfirst.execBasic
    · exact hscratch.2.2.2.1
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hfirstAddress, hfirstHead]
      exact htargetBound
  have hwriteBound : writeCode write ≤ wordBound tm bound := by
    apply smallValue_le_wordBound tm bound
    cases write <;> decide
  have hvalued : StepEnvelope tm bound valued := by
    apply haddressed.execBasic
    · exact hscratch.2.2.2.2.1
    · simpa [Structured.Internal.Basic.writeValue] using hwriteBound
  have hvaluedAddress :
      valued (addressReg n bound) =
        cellBase n bound tape + store (headReg tape) := by
    simp only [valued, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · simp [addressed, Structured.Basic.exec, hfirstAddress, hfirstHead]
    · simp [addressReg, valueReg]
  have hvaluedValue : valued (valueReg n bound) = writeCode write := by
    simp [valued, Structured.Basic.exec]
  have hstored : StepEnvelope tm bound stored := by
    apply hvalued.execBasic
    · simp only [Structured.Internal.Basic.writeIndex]
      rw [hvaluedAddress]
      exact lt_trans htargetLt (registerCount_lt_registerLimit' n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hvaluedValue]
      exact hwriteBound
  have hstartBound : symbolCode Γ.start ≤ wordBound tm bound :=
    smallValue_le_wordBound tm bound _ (by decide)
  have hfinal : StepEnvelope tm bound final := by
    apply hstored.execBasic
    · exact hbaseLt
    · simpa [Structured.Internal.Basic.writeValue] using hstartBound
  simpa [writeOps, first, addressed, valued, stored, final] using!
    And.intro henvelope (And.intro hfirst
      (And.intro haddressed (And.intro hvalued (And.intro hstored hfinal))))

private theorem writeMoveOps_envelopeChain (tm : TM n) (bound : ℕ)
    (tape : Fin (n + 2)) (write : Γw) (direction : Dir3)
    (store : Structured.Store) (henvelope : StepEnvelope tm bound store)
    (hhead : store (headReg tape) ≤ bound)
    (hone : store (oneReg n bound) = 1) :
    StepEnvelopeChain tm bound (writeMoveOps n bound tape write direction) store := by
  let written := Structured.Basic.execList (writeOps n bound tape write) store
  have hwrite := writeOps_envelopeChain tm bound tape write store henvelope hhead
  have hwrittenEnvelope : StepEnvelope tm bound written := hwrite.final
  have hwrittenHead : written (headReg tape) ≤ bound := by
    change Structured.Basic.execList (writeOps n bound tape write) store
        (headReg tape) ≤ bound
    rw [writeOps_head n bound tape write store]
    exact hhead
  have hwrittenOne : written (oneReg n bound) = 1 := by
    exact (writeOps_one n bound tape write store hhead).trans hone
  have hmove := moveOps_envelopeChain tm bound tape direction written
    hwrittenEnvelope hwrittenHead hwrittenOne
  simpa [writeMoveOps] using hwrite.append hmove

private theorem workPrefix_list_envelope {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3}
    (items processed : List (Fin n)) {store : Structured.Store}
    (hprefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections processed store)
    (henvelope : StepEnvelope tm bound store)
    (hfresh : ∀ i, i ∈ items → i ∉ processed)
    (hnodup : items.Nodup)
    (hheads : ∀ i, (cfg.work i).head ≤ bound)
    (hstarts : ∀ i, (cfg.work i).cells 0 = Γ.start) :
    let ops := items.flatMap (fun i => writeMoveOps n bound (workTape i)
      (workWrites i) (workDirections i))
    WorkPrefix tm bound cfg nextState inputDirection workWrites workDirections
        (items.reverse ++ processed) (Structured.Basic.execList ops store) ∧
      StepEnvelopeChain tm bound ops store := by
  induction items generalizing processed store with
  | nil => exact ⟨by simpa using! hprefix, henvelope⟩
  | cons i rest ih =>
      have hinot : i ∉ processed := hfresh i (by simp)
      have hselected : RepresentsTape bound (workTape i) (cfg.work i) store := by
        simpa [hinot] using hprefix.work i
      have hblock := writeMoveOps_envelopeChain tm bound (workTape i)
        (workWrites i) (workDirections i) store henvelope
        (hselected.1 ▸ hheads i) hprefix.one
      have hnext := workPrefix_step hprefix i hinot (hheads i) (hstarts i)
      have hrestFresh : ∀ j, j ∈ rest → j ∉ i :: processed := by
        intro j hj hmem
        rcases List.mem_cons.mp hmem with heq | hprocessed
        · subst j
          exact (List.nodup_cons.mp hnodup).1 hj
        · exact hfresh j (by simp [hj]) hprocessed
      obtain ⟨hfinalPrefix, hrestChain⟩ :=
        ih (processed := i :: processed) hnext hblock.final hrestFresh
          (List.nodup_cons.mp hnodup).2
      refine ⟨?_, ?_⟩
      · simpa [List.flatMap_cons, execList_append, List.reverse_cons,
          List.append_assoc] using hfinalPrefix
      · simpa [List.flatMap_cons] using hblock.append hrestChain

private theorem actionOps_envelopeChain_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    StepEnvelopeChain tm bound
      (actionOps tm bound cfg.state (readSymbols cfg)) store := by
  rcases hdelta : tm.δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read with
    ⟨nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection⟩
  have hreadInput : readSymbols cfg (inputTape n) = cfg.input.read := by
    simpa [readSymbols, inputTape] using
      congrArg Tape.read (tapeAt_input_internal cfg)
  have hreadWork : (fun i => readSymbols cfg (workTape i)) =
      (fun i => (cfg.work i).read) := by
    funext i
    simpa [readSymbols, workTape] using
      congrArg Tape.read (tapeAt_work_internal cfg i)
  have hreadOutput : readSymbols cfg (outputTape n) = cfg.output.read := by
    simpa [readSymbols, outputTape] using
      congrArg Tape.read (tapeAt_output_internal cfg)
  let initialized :=
    (Structured.Basic.imm 0 (stateCode tm nextState)).exec store
  have hstateBound : stateCode tm nextState ≤ wordBound tm bound := by
    exact le_trans (Nat.le_of_lt (stateCode_lt_internal tm nextState))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hinitialized : StepEnvelope tm bound initialized := by
    apply henvelope.execBasic
    · simp [registerLimit, scratchBase, registerCount]
    · simpa [Structured.Internal.Basic.writeValue] using hstateBound
  have hstateChain : StepEnvelopeChain tm bound
      [.imm 0 (stateCode tm nextState)] store := ⟨henvelope, hinitialized⟩
  have hinputStore : RepresentsTape bound (inputTape n) cfg.input store := by
    have htape := Represents.tape hrepresents (inputTape n)
    simpa [inputTape] using! htape
  have hinputHead : initialized (headReg (inputTape n)) ≤ bound := by
    have hhead := hheads (inputTape n)
    rw [show tapeAt cfg (inputTape n) = cfg.input by
      simpa [inputTape] using tapeAt_input_internal cfg] at hhead
    rw [show initialized (headReg (inputTape n)) = store (headReg (inputTape n)) by
      simp [initialized, Structured.Basic.exec, headReg, inputTape,
        Function.update_of_ne]]
    exact hinputStore.1.symm ▸ hhead
  have honeInitialized : initialized (oneReg n bound) = 1 := by
    rw [show initialized (oneReg n bound) = store (oneReg n bound) by
      simp [initialized, Structured.Basic.exec, oneReg, scratchBase, registerCount,
        Function.update_of_ne]]
    exact hone
  let afterInput := Structured.Basic.execList
    (moveOps n bound (inputTape n) inputDirection) initialized
  have hinputChain := moveOps_envelopeChain tm bound (inputTape n)
    inputDirection initialized hinitialized hinputHead honeInitialized
  have hprefix : WorkPrefix tm bound cfg nextState inputDirection
      workWrites workDirections [] afterInput := by
    exact actionPrelude_workPrefix nextState inputDirection workWrites
      workDirections hrepresents hone
  have hworkHeads : ∀ i, (cfg.work i).head ≤ bound := by
    intro i
    have hhead := hheads (workTape i)
    rw [show tapeAt cfg (workTape i) = cfg.work i by
      simpa [workTape] using tapeAt_work_internal cfg i] at hhead
    exact hhead
  obtain ⟨hworkPrefix, hworkChain⟩ := workPrefix_list_envelope
    (List.finRange n) [] hprefix hinputChain.final (by simp)
      (List.nodup_finRange n) hworkHeads hworkStart
  let workOps := (List.finRange n).flatMap (fun i =>
    writeMoveOps n bound (workTape i) (workWrites i) (workDirections i))
  let afterWork := Structured.Basic.execList workOps afterInput
  have houtputHead : afterWork (headReg (outputTape n)) ≤ bound := by
    have houtput := hworkPrefix.output.1
    have hhead := hheads (outputTape n)
    rw [show tapeAt cfg (outputTape n) = cfg.output by
      simpa [outputTape] using tapeAt_output_internal cfg] at hhead
    change Structured.Basic.execList
      ((List.finRange n).flatMap (fun i => writeMoveOps n bound (workTape i)
        (workWrites i) (workDirections i))) afterInput
        (headReg (outputTape n)) ≤ bound
    rw [houtput]
    exact hhead
  have houtputChain := writeMoveOps_envelopeChain tm bound (outputTape n)
    outputWrite outputDirection afterWork hworkChain.final houtputHead hworkPrefix.one
  have hcombined := hstateChain.append (hinputChain.append
    (hworkChain.append houtputChain))
  simpa [actionOps, hreadInput, hreadWork, hreadOutput, hdelta, initialized,
    afterInput, workOps, afterWork, List.append_assoc] using hcombined

theorem actionOps_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    let final := Structured.Basic.execList
      (actionOps tm bound cfg.state (readSymbols cfg)) store
    Structured.Internal.MeasuredRuns
        (action tm bound cfg.state (readSymbols cfg)) store final
        (actionOps tm bound cfg.state (readSymbols cfg)).length
        (4 * (actionOps tm bound cfg.state (readSymbols cfg)).length *
          wordWidth tm bound) (spaceBound tm bound) ∧
      Represents tm bound next final ∧
        Structured.Internal.StoreEnvelope
          (registerLimit n bound) (wordBound tm bound) final := by
  have hchain := actionOps_envelopeChain_internal hrepresents hheads
    hworkStart hone henvelope
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (actionOps tm bound cfg.state (readSymbols cfg)) store hchain
  refine ⟨?_, actionOps_represents_internal hstep hrepresents hheads
    hworkStart houtputStart hone, hmeasured.2⟩
  simpa [action, wordWidth, spaceBound, Structured.Internal.valueWidth,
    Structured.Internal.envelopeSpace] using hmeasured.1

end Step

end TMConfig

end RAM

end Complexity
