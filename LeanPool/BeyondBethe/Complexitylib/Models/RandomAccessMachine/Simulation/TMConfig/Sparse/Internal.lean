/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Internal

/-!
# Sparse unbounded TM configuration encoding -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


theorem control_lt_cellBase_internal (n : ℕ) :
    valueReg n < cellBase n ∧ ∀ tape, symbolReg n tape < cellBase n := by
  constructor
  · simp [valueReg, cellBase]
    omega
  · intro tape
    simp [symbolReg, cellBase]
    omega

theorem headReg_lt_control_internal (tape : Fin (n + 2)) :
    headReg tape < n + 3 := by
  simp [headReg]
  omega

theorem cellBase_le_cellReg_internal (tape : Fin (n + 2)) (position : ℕ) :
    cellBase n ≤ cellReg n tape position := by
  simp [cellReg]
  omega

private theorem headPrefix_lt_cellBase (n : ℕ) : n + 3 < cellBase n := by
  simp [cellBase]
  omega

theorem decodeCellTape_cellReg_internal (tape : Fin (n + 2)) (position : ℕ) :
    decodeCellTape n (cellReg n tape position) = tape := by
  have hoffset : cellReg n tape position - cellBase n =
      position * (n + 2) + tape.val := by
    simp [cellReg]
    omega
  apply Fin.ext
  change (cellReg n tape position - cellBase n) % (n + 2) = tape.val
  rw [hoffset]
  simp [Nat.add_mod, Nat.mod_eq_of_lt tape.isLt]

theorem decodeCellPosition_cellReg_internal (tape : Fin (n + 2))
    (position : ℕ) :
    decodeCellPosition n (cellReg n tape position) = position := by
  have hoffset : cellReg n tape position - cellBase n =
      position * (n + 2) + tape.val := by
    simp [cellReg]
    omega
  rw [decodeCellPosition, hoffset, Nat.add_comm,
    Nat.add_mul_div_right tape.val position (by omega),
    Nat.div_eq_of_lt tape.isLt, Nat.zero_add]

theorem cellReg_injective_internal :
    Function.Injective (fun field : Fin (n + 2) × ℕ =>
      cellReg n field.1 field.2) := by
  intro first second heq
  have htape := congrArg (decodeCellTape n) heq
  have hposition := congrArg (decodeCellPosition n) heq
  rw [decodeCellTape_cellReg_internal, decodeCellTape_cellReg_internal] at htape
  rw [decodeCellPosition_cellReg_internal,
    decodeCellPosition_cellReg_internal] at hposition
  exact Prod.ext htape hposition

theorem fieldReg_injective_internal : Function.Injective (@fieldReg n) := by
  intro first second heq
  rcases first with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    rcases second with state' | headOrCell'
    · rcases state' with ⟨state', hstate'⟩
      have hzero' : state' = 0 := by omega
      subst state'
      rfl
    · rcases headOrCell' with tape | cell
      · simp [fieldReg, stateReg, headReg] at heq
        omega
      · rcases cell with ⟨tape, position⟩
        have hbase := cellBase_le_cellReg_internal tape position
        simp [fieldReg, stateReg, cellBase] at heq hbase
        omega
  · rcases headOrCell with tape | cell
    · rcases second with state' | headOrCell'
      · rcases state' with ⟨state', hstate'⟩
        have hzero : state' = 0 := by omega
        subst state'
        simp [fieldReg, stateReg, headReg] at heq
      · rcases headOrCell' with tape' | cell'
        · apply congrArg Sum.inr
          apply congrArg Sum.inl
          apply Fin.ext
          simp [fieldReg, headReg] at heq
          omega
        · rcases cell' with ⟨tape', position'⟩
          have hhead := headReg_lt_control_internal tape
          have hcell := cellBase_le_cellReg_internal tape' position'
          have hcontrol := headPrefix_lt_cellBase n
          simp [fieldReg] at heq
          omega
    · rcases cell with ⟨tape, position⟩
      rcases second with state' | headOrCell'
      · rcases state' with ⟨state', hstate'⟩
        have hzero : state' = 0 := by omega
        subst state'
        have hcell := cellBase_le_cellReg_internal tape position
        simp [fieldReg, stateReg, cellBase] at heq hcell
        omega
      · rcases headOrCell' with tape' | cell'
        · have hhead := headReg_lt_control_internal tape'
          have hcell := cellBase_le_cellReg_internal tape position
          simp [fieldReg, cellBase] at heq hcell
          omega
        · rcases cell' with ⟨tape', position'⟩
          have hpairs : (tape, position) = (tape', position') :=
            cellReg_injective_internal heq
          exact congrArg (fun pair => Sum.inr (Sum.inr pair)) hpairs

theorem fieldReg_ne_control_internal (field : Field n) {reg : ℕ}
    (hlow : n + 3 ≤ reg) (hhigh : reg < cellBase n) :
    fieldReg field ≠ reg := by
  intro heq
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    simp [fieldReg, stateReg] at heq
    omega
  · rcases headOrCell with tape | cell
    · have hhead := headReg_lt_control_internal tape
      simp [fieldReg] at heq
      omega
    · have hcell := cellBase_le_cellReg_internal cell.1 cell.2
      simp [fieldReg] at heq
      omega

theorem Represents.update_control_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store} {reg value : ℕ}
    (hrepresents : Represents tm cfg store)
    (hlow : n + 3 ≤ reg) (hhigh : reg < cellBase n) :
    Represents tm cfg (Function.update store reg value) := by
  intro field
  rw [Function.update_of_ne (fieldReg_ne_control_internal field hlow hhigh)]
  exact hrepresents field

theorem scratch_range_internal (n : ℕ) :
    (n + 3 ≤ zeroReg n ∧ zeroReg n < cellBase n) ∧
    (n + 3 ≤ oneReg n ∧ oneReg n < cellBase n) ∧
    (n + 3 ≤ tapeCountReg n ∧ tapeCountReg n < cellBase n) ∧
    (n + 3 ≤ stateScratchReg n ∧ stateScratchReg n < cellBase n) ∧
    (n + 3 ≤ addressReg n ∧ addressReg n < cellBase n) ∧
    (n + 3 ≤ valueReg n ∧ valueReg n < cellBase n) ∧
    ∀ tape, n + 3 ≤ symbolReg n tape ∧ symbolReg n tape < cellBase n := by
  constructor
  · simp [zeroReg, cellBase]
    omega
  constructor
  · simp [oneReg, cellBase]
    omega
  constructor
  · simp [tapeCountReg, cellBase]
    omega
  constructor
  · simp [stateScratchReg, cellBase]
    omega
  constructor
  · simp [addressReg, cellBase]
    omega
  constructor
  · simp [valueReg, cellBase]
    omega
  · intro tape
    have htape := tape.isLt
    simp [symbolReg, cellBase]
    omega

theorem encodeRegs_state_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    encodeRegs tm cfg stateReg = stateCode tm cfg.state := by
  simp [encodeRegs, stateReg]

theorem encodeRegs_head_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (tape : Fin (n + 2)) :
    encodeRegs tm cfg (headReg tape) = (tapeAt cfg tape).head := by
  have hstate : headReg tape ≠ stateReg := by
    simp [headReg, stateReg]
  rw [encodeRegs, dite_eq_right hstate,
    dif_pos (headReg_lt_control_internal tape)]
  congr 2
  apply Fin.ext
  simp [headReg]

theorem encodeRegs_cell_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (tape : Fin (n + 2)) (position : ℕ) :
    encodeRegs tm cfg (cellReg n tape position) =
      symbolCode ((tapeAt cfg tape).cells position) := by
  have hbase := cellBase_le_cellReg_internal tape position
  have hcontrol := headPrefix_lt_cellBase n
  have hnotState : cellReg n tape position ≠ stateReg := by
    simp [stateReg]
    omega
  have hnotHead : ¬ cellReg n tape position < n + 3 := by omega
  rw [encodeRegs, dite_eq_right hnotState, dite_eq_right hnotHead, ite_eq_left hbase,
    decodeCellTape_cellReg_internal, decodeCellPosition_cellReg_internal]

theorem encodeRegs_represents_internal (tm : TM n)
    (cfg : Complexity.Cfg n tm.Q) : Represents tm cfg (encodeRegs tm cfg) := by
  intro field
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    exact encodeRegs_state_internal tm cfg
  · rcases headOrCell with tape | cell
    · exact encodeRegs_head_internal tm cfg tape
    · exact encodeRegs_cell_internal tm cfg cell.1 cell.2

theorem decode_of_represents_internal (tm : TM n)
    (cfg : Complexity.Cfg n tm.Q) (store : Structured.Store)
    (hrepresents : Represents tm cfg store) : decode tm store = cfg := by
  apply Complexity.Cfg.ext
  · simp only [decode]
    have hstate := hrepresents (Sum.inl ⟨0, by omega⟩)
    change store stateReg = stateCode tm cfg.state at hstate
    rw [hstate]
    exact stateDecode_code_internal tm cfg.state
  · apply Tape.ext
    · simpa [decode, decodeTape, tapeAt_input_internal] using
        hrepresents (Sum.inr (Sum.inl ⟨0, by omega⟩))
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨0, by omega⟩, position)))
      change store (cellReg n ⟨0, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨0, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_input_internal]
  · funext i
    apply Tape.ext
    · have hhead := hrepresents (Sum.inr (Sum.inl ⟨i.val + 1, by omega⟩))
      change store (headReg ⟨i.val + 1, by omega⟩) =
        (tapeAt cfg ⟨i.val + 1, by omega⟩).head at hhead
      simpa [decode, decodeTape, tapeAt_work_internal] using hhead
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨i.val + 1, by omega⟩, position)))
      change store (cellReg n ⟨i.val + 1, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨i.val + 1, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_work_internal]
  · apply Tape.ext
    · have hhead := hrepresents (Sum.inr (Sum.inl ⟨n + 1, by omega⟩))
      change store (headReg ⟨n + 1, by omega⟩) =
        (tapeAt cfg ⟨n + 1, by omega⟩).head at hhead
      simpa [decode, decodeTape, tapeAt_output_internal] using hhead
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨n + 1, by omega⟩, position)))
      change store (cellReg n ⟨n + 1, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨n + 1, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_output_internal]

theorem decode_encode_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    decode tm (encodeRegs tm cfg) = cfg :=
  decode_of_represents_internal tm cfg (encodeRegs tm cfg)
    (encodeRegs_represents_internal tm cfg)

end Sparse

end TMConfig

end RAM

end Complexity
