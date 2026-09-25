/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Layout

/-!
# Selected sparse TM transition actions -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


private theorem execList_append (first second : List Structured.Basic)
    (store : Structured.Store) :
    Structured.Basic.execList (first ++ second) store =
      Structured.Basic.execList second (Structured.Basic.execList first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons op rest ih => simp [Structured.Basic.execList, ih]

/-- Representation restricted to one named sparse tape. -/
private def RepresentsTape (slot : Fin (n + 2))
    (tape : Tape) (store : Structured.Store) : Prop :=
  store (headReg slot) = tape.head ∧
    ∀ position, store (cellReg n slot position) =
      symbolCode (tape.cells position)

private theorem Represents.tape {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (slot : Fin (n + 2)) :
    RepresentsTape slot (tapeAt cfg slot) store := by
  constructor
  · exact hrepresents (Sum.inr (Sum.inl slot))
  · intro position
    exact hrepresents (Sum.inr (Sum.inr (slot, position)))

private theorem headReg_ne_cellReg (headSlot cellSlot : Fin (n + 2))
    (position : ℕ) :
    headReg headSlot ≠ cellReg n cellSlot position := by
  intro heq
  have hfield :
      fieldReg (Sum.inr (Sum.inl headSlot)) =
        fieldReg (Sum.inr (Sum.inr (cellSlot, position))) := heq
  have := fieldReg_injective_internal hfield
  cases this

private theorem headReg_ne_headReg_of_slot_ne {first second : Fin (n + 2)}
    (hne : first ≠ second) : headReg first ≠ headReg second := by
  intro heq
  apply hne
  apply Fin.ext
  simp [headReg] at heq
  omega

private theorem cellReg_ne_cellReg_of_slot_ne {first second : Fin (n + 2)}
    (hne : first ≠ second) (firstPosition secondPosition : ℕ) :
    cellReg n first firstPosition ≠ cellReg n second secondPosition := by
  intro heq
  have hpairs : (first, firstPosition) = (second, secondPosition) :=
    cellReg_injective_internal heq
  exact hne (congrArg Prod.fst hpairs)

private theorem cellReg_ne_cellReg_of_position_ne (slot : Fin (n + 2))
    {first second : ℕ} (hne : first ≠ second) :
    cellReg n slot first ≠ cellReg n slot second := by
  intro heq
  have hpairs : (slot, first) = (slot, second) :=
    cellReg_injective_internal heq
  exact hne (congrArg Prod.snd hpairs)

private theorem addressOps_apply_of_ne (n : ℕ) (slot : Fin (n + 2))
    (store : Structured.Store) (reg : ℕ)
    (hvalue : reg ≠ valueReg n) (haddress : reg ≠ addressReg n) :
    Structured.Basic.execList (addressOps n slot) store reg = store reg := by
  simp [addressOps, Structured.Basic.execList, Structured.Basic.exec,
    Function.update_of_ne hvalue, Function.update_of_ne haddress]

/-- On configuration registers, a sparse write is exactly an update at the
represented head followed by restoration of cell zero. -/
private theorem writeOps_apply {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    (slot : Fin (n + 2)) (write : Γw) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2) (reg : ℕ)
    (hregValue : reg ≠ valueReg n) (hregAddress : reg ≠ addressReg n) :
    Structured.Basic.execList (writeOps n slot write) store reg =
      Function.update
        (Function.update (Structured.Basic.execList (addressOps n slot) store)
          (cellReg n slot (tapeAt cfg slot).head) (symbolCode write.toΓ))
        (cellReg n slot 0) (symbolCode Γ.start) reg := by
  let addressed := Structured.Basic.execList (addressOps n slot) store
  have haddress : addressed (addressReg n) =
      cellReg n slot (tapeAt cfg slot).head :=
    addressOps_address_internal hrepresents slot htapeCount
  have haddressValue : addressReg n ≠ valueReg n := by
    simp [addressReg, valueReg]
  have hvaluedAddress :
      ((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec addressed)
          (addressReg n) = addressed (addressReg n) := by
    simp [Structured.Basic.exec, Function.update_of_ne haddressValue]
  have hvaluedValue :
      ((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec addressed)
          (valueReg n) = symbolCode write.toΓ := by
    simp [Structured.Basic.exec]
  simp only [writeOps, execList_append, Structured.Basic.execList]
  change Function.update
      (Function.update
        ((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec addressed)
        (((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec addressed)
          (addressReg n))
        (((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec addressed)
          (valueReg n)))
      (cellReg n slot 0) (symbolCode Γ.start) reg = _
  rw [hvaluedAddress, hvaluedValue, haddress]
  by_cases hzero : reg = cellReg n slot 0
  · subst reg
    rw [Function.update_self, Function.update_self]
  · by_cases htarget : reg = cellReg n slot (tapeAt cfg slot).head
    · rw [Function.update_of_ne hzero, Function.update_of_ne hzero]
      subst reg
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzero, Function.update_of_ne hzero,
        Function.update_of_ne htarget, Function.update_of_ne htarget]
      rw [show
        ((Structured.Basic.imm (valueReg n) (symbolCode write.toΓ)).exec
          addressed) reg = addressed reg by
            simp [Structured.Basic.exec, Function.update_of_ne hregValue]]

private theorem writeOps_tape {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    (slot : Fin (n + 2)) (write : Γw) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hstart : (tapeAt cfg slot).cells 0 = Γ.start) :
    RepresentsTape slot ((tapeAt cfg slot).write write.toΓ)
      (Structured.Basic.execList (writeOps n slot write) store) := by
  let addressed := Structured.Basic.execList (addressOps n slot) store
  have haddressed := addressOps_represents_internal hrepresents slot
  have htape := Represents.tape haddressed slot
  constructor
  · rw [writeOps_apply slot write store hrepresents htapeCount
        (headReg slot)]
    · rw [Function.update_of_ne
          (headReg_ne_cellReg slot slot 0),
        Function.update_of_ne
          (headReg_ne_cellReg slot slot (tapeAt cfg slot).head)]
      simpa [Tape.write_head] using htape.1
    · simp [headReg, valueReg]
      omega
    · simp [headReg, addressReg]
      omega
  · intro position
    rw [writeOps_apply slot write store hrepresents htapeCount
        (cellReg n slot position)]
    · by_cases hheadZero : (tapeAt cfg slot).head = 0
      · by_cases hpositionZero : position = 0
        · subst position
          simp [Tape.write, hheadZero, hstart]
        · have hcellZero :=
            cellReg_ne_cellReg_of_position_ne (n := n) slot hpositionZero
          simp [Tape.write, hheadZero, hcellZero,
            htape.2 position]
      · by_cases hpositionHead : position = (tapeAt cfg slot).head
        · subst position
          have hcellZero := cellReg_ne_cellReg_of_position_ne (n := n) slot
            hheadZero
          simp [Tape.write, hheadZero, hcellZero]
        · by_cases hpositionZero : position = 0
          · subst position
            rw [Function.update_self]
            rw [Tape.write, ite_eq_right hheadZero]
            change symbolCode Γ.start = symbolCode
              (Function.update (tapeAt cfg slot).cells
                (tapeAt cfg slot).head write.toΓ 0)
            rw [Function.update_of_ne hpositionHead, hstart]
          · have hcellZero :=
              cellReg_ne_cellReg_of_position_ne (n := n) slot hpositionZero
            have hcellHead := cellReg_ne_cellReg_of_position_ne (n := n) slot
              hpositionHead
            simp [Tape.write, hheadZero, hpositionHead,
              hcellZero, hcellHead, htape.2 position]
    · simp [cellReg, valueReg, cellBase]
      omega
    · simp [cellReg, addressReg, cellBase]
      omega

private theorem moveOps_apply_of_ne (n : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (store : Structured.Store) {reg : ℕ}
    (hne : reg ≠ headReg slot) :
    Structured.Basic.execList (moveOps n slot direction) store reg = store reg := by
  cases direction <;>
    simp [moveOps, Structured.Basic.execList, Structured.Basic.exec,
      Function.update_of_ne hne]

private theorem moveOps_tape (n : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (tape : Tape) (store : Structured.Store)
    (hrepresents : RepresentsTape slot tape store)
    (hone : store (oneReg n) = 1) :
    RepresentsTape slot (tape.move direction)
      (Structured.Basic.execList (moveOps n slot direction) store) := by
  constructor
  · cases direction <;>
      simp [moveOps, Structured.Basic.execList, Structured.Basic.exec, Tape.move,
        hrepresents.1, hone]
  · intro position
    rw [moveOps_apply_of_ne n slot direction store
      (headReg_ne_cellReg slot slot position).symm]
    rw [Tape.move_cells]
    exact hrepresents.2 position

private theorem controlReg_ne_cellReg (n reg : ℕ)
    (hhigh : reg < cellBase n)
    (slot : Fin (n + 2)) (position : ℕ) :
    reg ≠ cellReg n slot position := by
  intro heq
  have hcell := cellBase_le_cellReg_internal slot position
  omega

private theorem writeOps_control {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    (slot : Fin (n + 2)) (write : Γw) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2) (reg : ℕ)
    (hhigh : reg < cellBase n)
    (hvalue : reg ≠ valueReg n) (haddress : reg ≠ addressReg n) :
    Structured.Basic.execList (writeOps n slot write) store reg = store reg := by
  rw [writeOps_apply slot write store hrepresents htapeCount reg hvalue haddress]
  rw [Function.update_of_ne
      (controlReg_ne_cellReg n reg hhigh slot 0),
    Function.update_of_ne
      (controlReg_ne_cellReg n reg hhigh slot (tapeAt cfg slot).head)]
  exact addressOps_apply_of_ne n slot store reg hvalue haddress

private theorem moveOps_control (n : ℕ) (slot : Fin (n + 2))
    (direction : Dir3) (store : Structured.Store) (reg : ℕ)
    (hlow : n + 3 ≤ reg) :
    Structured.Basic.execList (moveOps n slot direction) store reg = store reg := by
  apply moveOps_apply_of_ne
  intro heq
  have hhead := headReg_lt_control_internal slot
  omega

private theorem writeMoveOps_control {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2) (reg : ℕ)
    (hlow : n + 3 ≤ reg) (hhigh : reg < cellBase n)
    (hvalue : reg ≠ valueReg n) (haddress : reg ≠ addressReg n) :
    Structured.Basic.execList (writeMoveOps n slot write direction) store reg =
      store reg := by
  let written := Structured.Basic.execList (writeOps n slot write) store
  rw [writeMoveOps, execList_append,
    moveOps_control n slot direction written reg hlow]
  exact writeOps_control slot write store hrepresents htapeCount reg
    hhigh hvalue haddress

private theorem writeMoveOps_tape_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hone : store (oneReg n) = 1)
    (hstart : (tapeAt cfg slot).cells 0 = Γ.start) :
    RepresentsTape slot
      ((tapeAt cfg slot).writeAndMove write.toΓ direction)
      (Structured.Basic.execList (writeMoveOps n slot write direction) store) := by
  let written := Structured.Basic.execList (writeOps n slot write) store
  have hwritten := writeOps_tape slot write store hrepresents htapeCount hstart
  have hrange := scratch_range_internal n
  have honeWritten : written (oneReg n) = 1 := by
    exact (writeOps_control slot write store hrepresents htapeCount
      (oneReg n) hrange.2.1.2 (by simp [oneReg, valueReg])
      (by simp [oneReg, addressReg])).trans hone
  rw [writeMoveOps, execList_append]
  exact moveOps_tape n slot direction ((tapeAt cfg slot).write write.toΓ)
    written hwritten honeWritten

private theorem writeMoveOps_otherTape_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {slot other : Fin (n + 2)}
    (hne : slot ≠ other) (write : Γw) (direction : Dir3)
    (store : Structured.Store) (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2) :
    RepresentsTape other (tapeAt cfg other)
      (Structured.Basic.execList (writeMoveOps n slot write direction) store) := by
  let addressed := Structured.Basic.execList (addressOps n slot) store
  let written := Structured.Basic.execList (writeOps n slot write) store
  have haddressed := addressOps_represents_internal hrepresents slot
  have hother := Represents.tape haddressed other
  have hheadWritten : written (headReg other) = addressed (headReg other) := by
    change Structured.Basic.execList (writeOps n slot write) store
        (headReg other) = addressed (headReg other)
    rw [writeOps_apply slot write store hrepresents htapeCount (headReg other)]
    · rw [Function.update_of_ne (headReg_ne_cellReg other slot 0),
        Function.update_of_ne
          (headReg_ne_cellReg other slot (tapeAt cfg slot).head)]
    · simp [headReg, valueReg]
      omega
    · simp [headReg, addressReg]
      omega
  constructor
  · rw [writeMoveOps, execList_append,
      moveOps_apply_of_ne n slot direction written
        (headReg_ne_headReg_of_slot_ne (Ne.symm hne)),
      hheadWritten]
    exact hother.1
  · intro position
    have hcellWritten : written (cellReg n other position) =
        addressed (cellReg n other position) := by
      change Structured.Basic.execList (writeOps n slot write) store
          (cellReg n other position) = addressed (cellReg n other position)
      rw [writeOps_apply slot write store hrepresents htapeCount
          (cellReg n other position)]
      · rw [Function.update_of_ne
            (cellReg_ne_cellReg_of_slot_ne (Ne.symm hne) position 0),
          Function.update_of_ne
            (cellReg_ne_cellReg_of_slot_ne (Ne.symm hne) position
              (tapeAt cfg slot).head)]
      · simp [cellReg, valueReg, cellBase]
        omega
      · simp [cellReg, addressReg, cellBase]
        omega
    rw [writeMoveOps, execList_append,
      moveOps_apply_of_ne n slot direction written
        (headReg_ne_cellReg slot other position).symm,
      hcellWritten]
    exact hother.2 position

private theorem RepresentsTape.stateUpdate (slot : Fin (n + 2))
    (tape : Tape) (store : Structured.Store) (state : ℕ)
    (hrepresents : RepresentsTape slot tape store) :
    RepresentsTape slot tape
      ((Structured.Basic.imm stateReg state).exec store) := by
  constructor
  · simpa [Structured.Basic.exec, stateReg, headReg,
      Function.update_of_ne] using hrepresents.1
  · intro position
    simpa [Structured.Basic.exec, stateReg, cellReg, cellBase,
      Function.update_of_ne] using hrepresents.2 position

private theorem moveOps_otherTape (n : ℕ)
    {slot other : Fin (n + 2)} (hne : slot ≠ other)
    (direction : Dir3) (otherTape : Tape) (store : Structured.Store)
    (hother : RepresentsTape other otherTape store) :
    RepresentsTape other otherTape
      (Structured.Basic.execList (moveOps n slot direction) store) := by
  constructor
  · rw [moveOps_apply_of_ne n slot direction store
      (headReg_ne_headReg_of_slot_ne (Ne.symm hne))]
    exact hother.1
  · intro position
    rw [moveOps_apply_of_ne n slot direction store
      (headReg_ne_cellReg slot other position).symm]
    exact hother.2 position

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

/-- Reassemble the complete sparse representation from the state and named
tape blocks. -/
private theorem represents_of_named_tapes {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstate : store stateReg = stateCode tm cfg.state)
    (hinput : RepresentsTape (inputTape n) cfg.input store)
    (hwork : ∀ i, RepresentsTape (workTape i) (cfg.work i) store)
    (houtput : RepresentsTape (outputTape n) cfg.output store) :
    Represents tm cfg store := by
  intro field
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstateFin⟩
    have hzero : state = 0 := by omega
    subst state
    simpa [fieldReg, fieldValue] using hstate
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
      change store (cellReg n tape position) =
        symbolCode ((tapeAt cfg tape).cells position)
      by_cases hinputSlot : tape = inputTape n
      · subst tape
        rw [hinput.2 position]
        simpa [inputTape] using
          congrArg (fun t => symbolCode (t.cells position))
            (tapeAt_input_internal cfg).symm
      · by_cases houtputSlot : tape = outputTape n
        · subst tape
          rw [houtput.2 position]
          simpa [outputTape] using
            congrArg (fun t => symbolCode (t.cells position))
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
          simpa [workTape] using
            congrArg (fun t => symbolCode (t.cells position))
              (tapeAt_work_internal cfg i).symm

/-- Invariant after updating a prefix of the work tapes. -/
private structure WorkPrefix (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (nextState : tm.Q) (inputDirection : Dir3)
    (workWrites : Fin n → Γw) (workDirections : Fin n → Dir3)
    (processed : List (Fin n)) (store : Structured.Store) : Prop where
  state : store stateReg = stateCode tm nextState
  one : store (oneReg n) = 1
  tapeCount : store (tapeCountReg n) = n + 2
  input : RepresentsTape (inputTape n) (cfg.input.move inputDirection) store
  work : ∀ i, RepresentsTape (workTape i)
    (if i ∈ processed then
      (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)
    else cfg.work i) store
  output : RepresentsTape (outputTape n) cfg.output store

private theorem actionPrelude_workPrefix {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (nextState : tm.Q) (inputDirection : Dir3)
    (workWrites : Fin n → Γw) (workDirections : Fin n → Dir3)
    (hrepresents : Represents tm cfg store)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2) :
    let initialized :=
      (Structured.Basic.imm stateReg (stateCode tm nextState)).exec store
    let final := Structured.Basic.execList
      (moveOps n (inputTape n) inputDirection) initialized
    WorkPrefix tm cfg nextState inputDirection workWrites workDirections [] final := by
  let initialized :=
    (Structured.Basic.imm stateReg (stateCode tm nextState)).exec store
  let final := Structured.Basic.execList
    (moveOps n (inputTape n) inputDirection) initialized
  have honeInitialized : initialized (oneReg n) = 1 := by
    simpa [initialized, Structured.Basic.exec, stateReg, oneReg,
      Function.update_of_ne] using hone
  have hcountInitialized : initialized (tapeCountReg n) = n + 2 := by
    simpa [initialized, Structured.Basic.exec, stateReg, tapeCountReg,
      Function.update_of_ne] using htapeCount
  have hinputInitialized : RepresentsTape (inputTape n) cfg.input initialized := by
    have htape := (Represents.tape hrepresents (inputTape n)).stateUpdate
      (inputTape n) (tapeAt cfg (inputTape n)) store (stateCode tm nextState)
    rw [show tapeAt cfg (inputTape n) = cfg.input by
      simpa [inputTape] using tapeAt_input_internal cfg] at htape
    exact htape
  have hworkInitialized : ∀ i,
      RepresentsTape (workTape i) (cfg.work i) initialized := by
    intro i
    have htape := (Represents.tape hrepresents (workTape i)).stateUpdate
      (workTape i) (tapeAt cfg (workTape i)) store (stateCode tm nextState)
    rw [show tapeAt cfg (workTape i) = cfg.work i by
      simpa [workTape] using tapeAt_work_internal cfg i] at htape
    exact htape
  have houtputInitialized :
      RepresentsTape (outputTape n) cfg.output initialized := by
    have htape := (Represents.tape hrepresents (outputTape n)).stateUpdate
      (outputTape n) (tapeAt cfg (outputTape n)) store (stateCode tm nextState)
    rw [show tapeAt cfg (outputTape n) = cfg.output by
      simpa [outputTape] using tapeAt_output_internal cfg] at htape
    exact htape
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveOps_apply_of_ne n (inputTape n) inputDirection initialized]
    · simp [initialized, Structured.Basic.exec]
    · simp [stateReg, headReg, inputTape]
  · exact (moveOps_control n (inputTape n) inputDirection initialized
      (oneReg n) (by simp [oneReg])).trans honeInitialized
  · exact (moveOps_control n (inputTape n) inputDirection initialized
      (tapeCountReg n) (by simp [tapeCountReg])).trans hcountInitialized
  · exact moveOps_tape n (inputTape n) inputDirection cfg.input initialized
      hinputInitialized honeInitialized
  · intro i
    simpa using moveOps_otherTape n (inputTape_ne_workTape n i)
      inputDirection (cfg.work i) initialized (hworkInitialized i)
  · exact moveOps_otherTape n (inputTape_ne_outputTape n) inputDirection
      cfg.output initialized houtputInitialized

private theorem writeMoveOps_state {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} (slot : Fin (n + 2))
    (write : Γw) (direction : Dir3) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2) :
    Structured.Basic.execList (writeMoveOps n slot write direction) store
        stateReg = store stateReg := by
  let written := Structured.Basic.execList (writeOps n slot write) store
  rw [writeMoveOps, execList_append,
    moveOps_apply_of_ne n slot direction written]
  · change Structured.Basic.execList (writeOps n slot write) store stateReg =
      store stateReg
    rw [writeOps_apply slot write store hrepresents htapeCount stateReg]
    · have hzero : stateReg ≠ cellReg n slot 0 := by
        simp [stateReg, cellReg, cellBase]
        omega
      have htarget : stateReg ≠
          cellReg n slot (tapeAt cfg slot).head := by
        simp [stateReg, cellReg, cellBase]
        omega
      rw [Function.update_of_ne hzero, Function.update_of_ne htarget]
      exact addressOps_apply_of_ne n slot store stateReg
        (by simp [stateReg, valueReg]) (by simp [stateReg, addressReg])
    · simp [stateReg, valueReg]
    · simp [stateReg, addressReg]
  · simp [stateReg, headReg]
    omega

private theorem workPrefix_step {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3} {processed : List (Fin n)}
    {store : Structured.Store}
    (hprefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections processed store)
    (i : Fin n) (hfresh : i ∉ processed)
    (hstart : (cfg.work i).cells 0 = Γ.start) :
    WorkPrefix tm cfg nextState inputDirection workWrites workDirections
      (i :: processed)
      (Structured.Basic.execList
        (writeMoveOps n (workTape i) (workWrites i) (workDirections i)) store) := by
  let current : Complexity.Cfg n tm.Q :=
    { state := nextState
      input := cfg.input.move inputDirection
      work := fun j => if j ∈ processed then
        (cfg.work j).writeAndMove (workWrites j).toΓ (workDirections j)
      else cfg.work j
      output := cfg.output }
  have hcurrent : Represents tm current store := by
    exact represents_of_named_tapes hprefix.state hprefix.input hprefix.work
      hprefix.output
  have hselectedTape : tapeAt current (workTape i) = cfg.work i := by
    simp [current, workTape, hfresh, tapeAt_work_internal]
  have hselected : RepresentsTape (workTape i) (cfg.work i) store := by
    simpa [hselectedTape] using Represents.tape hcurrent (workTape i)
  have hselectedFinal := writeMoveOps_tape_internal (tm := tm)
    (cfg := current) (workTape i) (workWrites i) (workDirections i) store
    hcurrent hprefix.tapeCount hprefix.one (by simpa [hselectedTape] using hstart)
  have hrange := scratch_range_internal n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (writeMoveOps_state (workTape i) (workWrites i)
      (workDirections i) store hcurrent hprefix.tapeCount).trans hprefix.state
  · exact (writeMoveOps_control (workTape i) (workWrites i)
      (workDirections i) store hcurrent hprefix.tapeCount (oneReg n)
      hrange.2.1.1 hrange.2.1.2 (by simp [oneReg, valueReg])
      (by simp [oneReg, addressReg])).trans hprefix.one
  · exact (writeMoveOps_control (workTape i) (workWrites i)
      (workDirections i) store hcurrent hprefix.tapeCount (tapeCountReg n)
      hrange.2.2.1.1 hrange.2.2.1.2 (by simp [tapeCountReg, valueReg])
      (by simp [tapeCountReg, addressReg])).trans hprefix.tapeCount
  · have hother := writeMoveOps_otherTape_internal
      (tm := tm) (cfg := current) (Ne.symm (inputTape_ne_workTape n i))
      (workWrites i) (workDirections i) store hcurrent hprefix.tapeCount
    simpa [current, inputTape] using! hother
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [hselectedTape] using hselectedFinal
    · have hslots : workTape i ≠ workTape j := by
        exact fun heq => hji ((workTape_injective n) heq).symm
      have hother := writeMoveOps_otherTape_internal
        (tm := tm) (cfg := current) hslots (workWrites i)
        (workDirections i) store hcurrent hprefix.tapeCount
      have htape : tapeAt current (workTape j) =
          (if j ∈ processed then
            (cfg.work j).writeAndMove (workWrites j).toΓ (workDirections j)
          else cfg.work j) := by
        simpa [current, workTape] using tapeAt_work_internal current j
      rw [htape] at hother
      simpa [hji] using hother
  · have hother := writeMoveOps_otherTape_internal
      (tm := tm) (cfg := current) (outputTape_ne_workTape n i).symm
      (workWrites i) (workDirections i) store hcurrent hprefix.tapeCount
    have htape : tapeAt current (outputTape n) = cfg.output := by
      simpa [current, outputTape] using tapeAt_output_internal current
    rw [htape] at hother
    exact hother

private theorem workPrefix_list {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3}
    (items processed : List (Fin n)) {store : Structured.Store}
    (hprefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections processed store)
    (hfresh : ∀ i, i ∈ items → i ∉ processed)
    (hnodup : items.Nodup)
    (hstarts : ∀ i, (cfg.work i).cells 0 = Γ.start) :
    WorkPrefix tm cfg nextState inputDirection workWrites workDirections
      (items.reverse ++ processed)
      (Structured.Basic.execList
        (items.flatMap (fun i => writeMoveOps n (workTape i)
          (workWrites i) (workDirections i))) store) := by
  induction items generalizing processed store with
  | nil => simpa using! hprefix
  | cons i rest ih =>
      have hinot : i ∉ processed := hfresh i (by simp)
      have hnext := workPrefix_step hprefix i hinot (hstarts i)
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

theorem actionOps_represents_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2) :
    Represents tm next
      (Structured.Basic.execList
        (actionOps tm cfg.state (readSymbols cfg)) store) := by
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
    (Structured.Basic.imm stateReg (stateCode tm nextState)).exec store
  let afterInput := Structured.Basic.execList
    (moveOps n (inputTape n) inputDirection) initialized
  have hprefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections [] afterInput := by
    exact actionPrelude_workPrefix nextState inputDirection workWrites
      workDirections hrepresents hone htapeCount
  let afterWork := Structured.Basic.execList
    ((List.finRange n).flatMap (fun i =>
      writeMoveOps n (workTape i) (workWrites i) (workDirections i)))
      afterInput
  have hworkPrefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections ((List.finRange n).reverse ++ []) afterWork := by
    exact workPrefix_list (List.finRange n) [] hprefix (by simp)
      (List.nodup_finRange n) hworkStart
  have hworkFinal : ∀ i,
      RepresentsTape (workTape i)
        ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i))
        afterWork := by
    intro i
    simpa using hworkPrefix.work i
  let current : Complexity.Cfg n tm.Q :=
    { state := nextState
      input := cfg.input.move inputDirection
      work := fun i =>
        (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)
      output := cfg.output }
  have hcurrent : Represents tm current afterWork := by
    exact represents_of_named_tapes hworkPrefix.state hworkPrefix.input
      hworkFinal hworkPrefix.output
  have houtputTape : tapeAt current (outputTape n) = cfg.output := by
    simpa [current, outputTape] using tapeAt_output_internal current
  let final := Structured.Basic.execList
    (writeMoveOps n (outputTape n) outputWrite outputDirection) afterWork
  have houtputFinalRaw := writeMoveOps_tape_internal (tm := tm)
    (cfg := current) (outputTape n) outputWrite outputDirection afterWork
    hcurrent hworkPrefix.tapeCount hworkPrefix.one
    (by simpa [houtputTape] using houtputStart)
  have houtputFinal : RepresentsTape (outputTape n)
      (cfg.output.writeAndMove outputWrite.toΓ outputDirection) final := by
    simpa [final, houtputTape] using houtputFinalRaw
  have hinputFinalRaw := writeMoveOps_otherTape_internal
    (tm := tm) (cfg := current) (inputTape_ne_outputTape n).symm
    outputWrite outputDirection afterWork hcurrent hworkPrefix.tapeCount
  have hinputTape : tapeAt current (inputTape n) =
      cfg.input.move inputDirection := by
    simpa [current, inputTape] using tapeAt_input_internal current
  have hinputFinal : RepresentsTape (inputTape n)
      (cfg.input.move inputDirection) final := by
    rw [hinputTape] at hinputFinalRaw
    exact hinputFinalRaw
  have hworkFinal' : ∀ i, RepresentsTape (workTape i)
      ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i))
      final := by
    intro i
    have hother := writeMoveOps_otherTape_internal
      (tm := tm) (cfg := current) (outputTape_ne_workTape n i)
      outputWrite outputDirection afterWork hcurrent hworkPrefix.tapeCount
    have htape : tapeAt current (workTape i) =
        (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i) := by
      simpa [current, workTape] using tapeAt_work_internal current i
    rw [htape] at hother
    exact hother
  have hstateFinal : final stateReg = stateCode tm nextState := by
    exact (writeMoveOps_state (outputTape n) outputWrite outputDirection
      afterWork hcurrent hworkPrefix.tapeCount).trans hworkPrefix.state
  have hfinalRepresents :
      Represents tm
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
    Structured.Basic.execList, List.append_assoc] using hfinalRepresents

private abbrev ResourceEnvelope (tm : TM n) (bound : ℕ) :=
  Structured.Internal.StoreEnvelope (registerBound n (bound + 1))
    (wordBound tm bound)

private abbrev ResourceEnvelopeChain (tm : TM n) (bound : ℕ) :=
  Structured.Internal.Basic.EnvelopeChain (registerBound n (bound + 1))
    (wordBound tm bound)

private theorem control_lt_registerBound (n bound : ℕ) :
    cellBase n < registerBound n (bound + 1) := by
  simp [registerBound, cellReg, outputTape]
  omega

private theorem registerBound_le_wordBound (tm : TM n) (bound : ℕ) :
    registerBound n (bound + 1) ≤ wordBound tm bound :=
  le_max_left _ _

private theorem headReg_lt_registerBound (n bound : ℕ)
    (tape : Fin (n + 2)) : headReg tape < registerBound n (bound + 1) := by
  have hfixed : n + 3 ≤ cellBase n := by
    simp [cellBase]
    omega
  exact lt_of_lt_of_le (headReg_lt_control_internal tape)
    (le_trans hfixed (Nat.le_of_lt (control_lt_registerBound n bound)))

private theorem cellReg_lt_registerBound (tape : Fin (n + 2))
    {position bound : ℕ} (hposition : position ≤ bound + 1) :
    cellReg n tape position < registerBound n (bound + 1) := by
  have hmul := Nat.mul_le_mul_right (n + 2) hposition
  simp only [cellReg, registerBound, outputTape]
  omega

private theorem smallValue_le_wordBound (tm : TM n) (bound value : ℕ)
    (hvalue : value ≤ 4) : value ≤ wordBound tm bound := by
  have hfour : 4 ≤ registerBound n (bound + 1) := by
    have hcontrol := control_lt_registerBound n bound
    simp [cellBase] at hcontrol
    omega
  exact le_trans hvalue
    (le_trans hfour (registerBound_le_wordBound tm bound))

private theorem moveOps_envelopeChain (tm : TM n) (bound : ℕ)
    (tape : Fin (n + 2)) (direction : Dir3) (store : Structured.Store)
    (henvelope : ResourceEnvelope tm bound store)
    (hhead : store (headReg tape) ≤ bound)
    (hone : store (oneReg n) = 1) :
    ResourceEnvelopeChain tm bound (moveOps n tape direction) store := by
  have hindex := headReg_lt_registerBound n bound tape
  have hbound : bound + 1 ≤ wordBound tm bound := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  cases direction with
  | stay => exact henvelope
  | left =>
      have hfinal : ResourceEnvelope tm bound
          ((Structured.Basic.sub (headReg tape) (headReg tape)
            (oneReg n)).exec store) := by
        apply henvelope.execBasic
        · exact hindex
        · simp only [Structured.Internal.Basic.writeValue]
          omega
      exact ⟨henvelope, hfinal⟩
  | right =>
      have hfinal : ResourceEnvelope tm bound
          ((Structured.Basic.add (headReg tape) (headReg tape)
            (oneReg n)).exec store) := by
        apply henvelope.execBasic
        · exact hindex
        · simp only [Structured.Internal.Basic.writeValue]
          rw [hone]
          omega
      exact ⟨henvelope, hfinal⟩

private theorem writeOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} (tape : Fin (n + 2)) (write : Γw)
    (store : Structured.Store) (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (henvelope : ResourceEnvelope tm bound store)
    (hhead : (tapeAt cfg tape).head ≤ bound) :
    ResourceEnvelopeChain tm bound (writeOps n tape write) store := by
  let first := (Structured.Basic.imm (valueReg n)
    (cellBase n + tape.val)).exec store
  let multiplied := (Structured.Basic.mul (addressReg n) (headReg tape)
    (tapeCountReg n)).exec first
  let addressed := (Structured.Basic.add (addressReg n) (addressReg n)
    (valueReg n)).exec multiplied
  let valued := (Structured.Basic.imm (valueReg n)
    (symbolCode write.toΓ)).exec addressed
  let stored := (Structured.Basic.store (addressReg n) (valueReg n)).exec valued
  let final := (Structured.Basic.imm (cellReg n tape 0)
    (symbolCode Γ.start)).exec stored
  have hrange := scratch_range_internal n
  have hbaseLt : cellBase n + tape.val < registerBound n (bound + 1) := by
    simpa [cellReg] using
      (cellReg_lt_registerBound tape (bound := bound)
        (position := 0) (by omega))
  have hbaseBound : cellBase n + tape.val ≤ wordBound tm bound :=
    le_trans (Nat.le_of_lt hbaseLt) (registerBound_le_wordBound tm bound)
  have hfirst : ResourceEnvelope tm bound first := by
    apply henvelope.execBasic
    · exact lt_trans hrange.2.2.2.2.2.1.2
        (control_lt_registerBound n bound)
    · simpa [Structured.Internal.Basic.writeValue] using hbaseBound
  have hstoreHead : store (headReg tape) = (tapeAt cfg tape).head :=
    hrepresents (Sum.inr (Sum.inl tape))
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    have hne : headReg tape ≠ valueReg n := by
      simp [headReg, valueReg]
      omega
    simp [first, Structured.Basic.exec, Function.update_of_ne hne]
  have hfirstCount : first (tapeCountReg n) = store (tapeCountReg n) := by
    simp [first, Structured.Basic.exec, tapeCountReg, valueReg,
      Function.update_of_ne]
  have hproductBound : (tapeAt cfg tape).head * (n + 2) ≤
      wordBound tm bound := by
    have htarget := cellReg_lt_registerBound tape
      (position := (tapeAt cfg tape).head) (bound := bound) (by omega)
    have hproduct : (tapeAt cfg tape).head * (n + 2) <
        registerBound n (bound + 1) := by
      simp [cellReg] at htarget
      omega
    exact le_trans (Nat.le_of_lt hproduct)
      (registerBound_le_wordBound tm bound)
  have hmultiplied : ResourceEnvelope tm bound multiplied := by
    apply hfirst.execBasic
    · exact lt_trans hrange.2.2.2.2.1.2
        (control_lt_registerBound n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hfirstHead, hfirstCount, hstoreHead, htapeCount]
      exact hproductBound
  have hmultipliedAddress : multiplied (addressReg n) =
      (tapeAt cfg tape).head * (n + 2) := by
    simp only [multiplied, Structured.Basic.exec, Function.update_self]
    rw [hfirstHead, hfirstCount, hstoreHead, htapeCount]
  have hmultipliedValue : multiplied (valueReg n) =
      cellBase n + tape.val := by
    simp [multiplied, first, Structured.Basic.exec, valueReg, addressReg,
      Function.update_of_ne]
  have htargetLt : cellReg n tape (tapeAt cfg tape).head <
      registerBound n (bound + 1) :=
    cellReg_lt_registerBound tape (bound := bound) (by omega)
  have htargetBound : cellReg n tape (tapeAt cfg tape).head ≤
      wordBound tm bound :=
    le_trans (Nat.le_of_lt htargetLt) (registerBound_le_wordBound tm bound)
  have haddressed : ResourceEnvelope tm bound addressed := by
    apply hmultiplied.execBasic
    · exact lt_trans hrange.2.2.2.2.1.2
        (control_lt_registerBound n bound)
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hmultipliedAddress, hmultipliedValue]
      simp [cellReg] at htargetBound
      omega
  have hwriteBound : symbolCode write.toΓ ≤ wordBound tm bound := by
    apply smallValue_le_wordBound tm bound
    cases write <;> decide
  have hvalued : ResourceEnvelope tm bound valued := by
    apply haddressed.execBasic
    · exact lt_trans hrange.2.2.2.2.2.1.2
        (control_lt_registerBound n bound)
    · simpa [Structured.Internal.Basic.writeValue] using hwriteBound
  have hvaluedAddress : valued (addressReg n) =
      cellReg n tape (tapeAt cfg tape).head := by
    simp only [valued, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · simp [addressed, Structured.Basic.exec, hmultipliedAddress,
        hmultipliedValue, cellReg]
      omega
    · simp [addressReg, valueReg]
  have hvaluedValue : valued (valueReg n) = symbolCode write.toΓ := by
    simp [valued, Structured.Basic.exec]
  have hstored : ResourceEnvelope tm bound stored := by
    apply hvalued.execBasic
    · simp only [Structured.Internal.Basic.writeIndex]
      rw [hvaluedAddress]
      exact htargetLt
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hvaluedValue]
      exact hwriteBound
  have hstartBound : symbolCode Γ.start ≤ wordBound tm bound :=
    smallValue_le_wordBound tm bound _ (by decide)
  have hfinal : ResourceEnvelope tm bound final := by
    apply hstored.execBasic
    · exact cellReg_lt_registerBound tape (bound := bound)
        (position := 0) (by omega)
    · simpa [Structured.Internal.Basic.writeValue] using hstartBound
  simpa [writeOps, addressOps, first, multiplied, addressed, valued, stored,
    final] using! And.intro henvelope (And.intro hfirst
      (And.intro hmultiplied (And.intro haddressed
        (And.intro hvalued (And.intro hstored hfinal)))))

private theorem writeMoveOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} (tape : Fin (n + 2)) (write : Γw)
    (direction : Dir3) (store : Structured.Store)
    (hrepresents : Represents tm cfg store)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hone : store (oneReg n) = 1)
    (hstart : (tapeAt cfg tape).cells 0 = Γ.start)
    (hhead : (tapeAt cfg tape).head ≤ bound)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerBound n (bound + 1)) (wordBound tm bound) store) :
    ResourceEnvelopeChain tm bound
      (writeMoveOps n tape write direction) store := by
  let written := Structured.Basic.execList (writeOps n tape write) store
  have hwrite := writeOps_envelopeChain tape write store hrepresents
    htapeCount henvelope hhead
  have hwrittenTape := writeOps_tape tape write store hrepresents
    htapeCount hstart
  have hwrittenHead : written (headReg tape) ≤ bound := by
    change Structured.Basic.execList (writeOps n tape write) store
      (headReg tape) ≤ bound
    rw [hwrittenTape.1, Tape.write_head]
    exact hhead
  have hrange := scratch_range_internal n
  have hwrittenOne : written (oneReg n) = 1 := by
    exact (writeOps_control tape write store hrepresents htapeCount
      (oneReg n) hrange.2.1.2 (by simp [oneReg, valueReg])
      (by simp [oneReg, addressReg])).trans hone
  have hmove := moveOps_envelopeChain tm bound tape direction written
    hwrite.final hwrittenHead hwrittenOne
  simpa [writeMoveOps] using hwrite.append hmove

private theorem workPrefix_list_envelope {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {nextState : tm.Q}
    {inputDirection : Dir3} {workWrites : Fin n → Γw}
    {workDirections : Fin n → Dir3}
    (items processed : List (Fin n)) {store : Structured.Store}
    (hprefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections processed store)
    (henvelope : ResourceEnvelope tm bound store)
    (hfresh : ∀ i, i ∈ items → i ∉ processed)
    (hnodup : items.Nodup)
    (hheads : ∀ i, (cfg.work i).head ≤ bound)
    (hstarts : ∀ i, (cfg.work i).cells 0 = Γ.start) :
    let ops := items.flatMap (fun i => writeMoveOps n (workTape i)
      (workWrites i) (workDirections i))
    WorkPrefix tm cfg nextState inputDirection workWrites workDirections
        (items.reverse ++ processed) (Structured.Basic.execList ops store) ∧
      ResourceEnvelopeChain tm bound ops store := by
  induction items generalizing processed store with
  | nil => exact ⟨by simpa using! hprefix, henvelope⟩
  | cons i rest ih =>
      have hinot : i ∉ processed := hfresh i (by simp)
      let current : Complexity.Cfg n tm.Q :=
        { state := nextState
          input := cfg.input.move inputDirection
          work := fun j => if j ∈ processed then
            (cfg.work j).writeAndMove (workWrites j).toΓ (workDirections j)
          else cfg.work j
          output := cfg.output }
      have hcurrent : Represents tm current store := by
        exact represents_of_named_tapes hprefix.state hprefix.input hprefix.work
          hprefix.output
      have hselectedTape : tapeAt current (workTape i) = cfg.work i := by
        simp [current, workTape, hinot, tapeAt_work_internal]
      have hblock := writeMoveOps_envelopeChain (tm := tm) (bound := bound)
        (cfg := current) (workTape i) (workWrites i) (workDirections i) store
        hcurrent hprefix.tapeCount hprefix.one
        (by simpa [hselectedTape] using hstarts i)
        (by simpa [hselectedTape] using hheads i) henvelope
      have hnext := workPrefix_step hprefix i hinot (hstarts i)
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
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (henvelope : ResourceEnvelope tm bound store) :
    ResourceEnvelopeChain tm bound
      (actionOps tm cfg.state (readSymbols cfg)) store := by
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
    (Structured.Basic.imm stateReg (stateCode tm nextState)).exec store
  have hstateBound : stateCode tm nextState ≤ wordBound tm bound := by
    have hstateLt : stateCode tm nextState < Fintype.card tm.Q := by
      simp [stateCode]
    exact le_trans (Nat.le_of_lt hstateLt)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hinitialized : ResourceEnvelope tm bound initialized := by
    apply henvelope.execBasic
    · simp [stateReg, registerBound, cellReg, outputTape, cellBase]
    · simpa [Structured.Internal.Basic.writeValue] using hstateBound
  have hstateChain : ResourceEnvelopeChain tm bound
      [.imm stateReg (stateCode tm nextState)] store :=
    ⟨henvelope, hinitialized⟩
  have hinputHead : initialized (headReg (inputTape n)) ≤ bound := by
    have hhead := hheads (inputTape n)
    have hstored := hrepresents (Sum.inr (Sum.inl (inputTape n)))
    change store (headReg (inputTape n)) =
      (tapeAt cfg (inputTape n)).head at hstored
    rw [show tapeAt cfg (inputTape n) = cfg.input by
      simpa [inputTape] using tapeAt_input_internal cfg] at hhead hstored
    rw [show initialized (headReg (inputTape n)) =
        store (headReg (inputTape n)) by
      simp [initialized, Structured.Basic.exec, stateReg, headReg, inputTape,
        Function.update_of_ne]]
    rw [hstored]
    exact hhead
  have honeInitialized : initialized (oneReg n) = 1 := by
    simpa [initialized, Structured.Basic.exec, stateReg, oneReg,
      Function.update_of_ne] using hone
  let afterInput := Structured.Basic.execList
    (moveOps n (inputTape n) inputDirection) initialized
  have hinputChain := moveOps_envelopeChain tm bound (inputTape n)
    inputDirection initialized hinitialized hinputHead honeInitialized
  have hprefix : WorkPrefix tm cfg nextState inputDirection
      workWrites workDirections [] afterInput := by
    exact actionPrelude_workPrefix nextState inputDirection workWrites
      workDirections hrepresents hone htapeCount
  have hworkHeads : ∀ i, (cfg.work i).head ≤ bound := by
    intro i
    have hhead := hheads (workTape i)
    rwa [show tapeAt cfg (workTape i) = cfg.work i by
      simpa [workTape] using tapeAt_work_internal cfg i] at hhead
  obtain ⟨hworkPrefix, hworkChain⟩ := workPrefix_list_envelope
    (bound := bound) (List.finRange n) [] hprefix hinputChain.final
      (by simp) (List.nodup_finRange n) hworkHeads hworkStart
  let workOps := (List.finRange n).flatMap (fun i =>
    writeMoveOps n (workTape i) (workWrites i) (workDirections i))
  let afterWork := Structured.Basic.execList workOps afterInput
  let current : Complexity.Cfg n tm.Q :=
    { state := nextState
      input := cfg.input.move inputDirection
      work := fun i =>
        (cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i)
      output := cfg.output }
  have hworkFinal : ∀ i, RepresentsTape (workTape i)
      ((cfg.work i).writeAndMove (workWrites i).toΓ (workDirections i))
      afterWork := by
    intro i
    simpa [afterWork, workOps] using hworkPrefix.work i
  have hcurrent : Represents tm current afterWork := by
    exact represents_of_named_tapes hworkPrefix.state hworkPrefix.input
      hworkFinal hworkPrefix.output
  have houtputTape : tapeAt current (outputTape n) = cfg.output := by
    simpa [current, outputTape] using tapeAt_output_internal current
  have houtputHead : (tapeAt current (outputTape n)).head ≤ bound := by
    rw [houtputTape]
    have hhead := hheads (outputTape n)
    rwa [show tapeAt cfg (outputTape n) = cfg.output by
      simpa [outputTape] using tapeAt_output_internal cfg] at hhead
  have houtputStartCurrent :
      (tapeAt current (outputTape n)).cells 0 = Γ.start := by
    rw [houtputTape]
    exact houtputStart
  have houtputChain := writeMoveOps_envelopeChain
    (tm := tm) (bound := bound) (cfg := current) (outputTape n)
    outputWrite outputDirection afterWork hcurrent hworkPrefix.tapeCount
    hworkPrefix.one houtputStartCurrent houtputHead hworkChain.final
  have hcombined := hstateChain.append (hinputChain.append
    (hworkChain.append houtputChain))
  simpa [actionOps, hreadInput, hreadWork, hreadOutput, hdelta, initialized,
    afterInput, workOps, afterWork, List.append_assoc] using hcombined

theorem actionOps_measured_internal {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerBound n (bound + 1)) (wordBound tm bound) store) :
    let final := Structured.Basic.execList
      (actionOps tm cfg.state (readSymbols cfg)) store
    Structured.Internal.MeasuredRuns
        (action tm cfg.state (readSymbols cfg)) store final
        (actionOps tm cfg.state (readSymbols cfg)).length
        (4 * (actionOps tm cfg.state (readSymbols cfg)).length *
          wordWidth tm bound) (spaceBound tm bound) ∧
      Represents tm next final ∧
        Structured.Internal.StoreEnvelope
          (registerBound n (bound + 1)) (wordBound tm bound) final := by
  have hchain := actionOps_envelopeChain_internal hrepresents hheads
    hworkStart houtputStart hone htapeCount henvelope
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (actionOps tm cfg.state (readSymbols cfg)) store hchain
  refine ⟨?_, actionOps_represents_internal hstep hrepresents hworkStart
    houtputStart hone htapeCount, hmeasured.2⟩
  simpa [action, wordWidth, spaceBound, Structured.Internal.valueWidth,
    Structured.Internal.envelopeSpace] using hmeasured.1


end Sparse

end TMConfig

end RAM

end Complexity
