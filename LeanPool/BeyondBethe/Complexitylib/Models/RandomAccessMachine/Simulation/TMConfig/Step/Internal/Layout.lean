/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Defs

/-!
# TM-to-RAM step layout -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

variable {n bound : ℕ} {tape : Fin (n + 2)}

namespace Step


theorem symbolCode_lt_internal (symbol : Γ) : symbolCode symbol < 4 := by
  cases symbol <;> decide

theorem symbolAt_code_internal (symbol : Γ) :
    symbolAt ⟨symbolCode symbol, symbolCode_lt_internal symbol⟩ = symbol := by
  exact symbolDecode_code_internal symbol

theorem stateCode_lt_internal (tm : TM n) (state : tm.Q) :
    stateCode tm state < Fintype.card tm.Q :=
  (Fintype.equivFin tm.Q state).isLt

theorem headReg_eq_fieldReg_internal (tape : Fin (n + 2)) :
    headReg tape = fieldReg (headField (bound := bound) tape) := by
  simp [headReg]

theorem cellBase_add_eq_fieldReg_internal (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    cellBase n bound tape + position.val = fieldReg (cellField tape position) := by
  simp [cellBase]

theorem zeroReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ zeroReg n bound := by
  simp [zeroReg, scratchBase]

theorem oneReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ oneReg n bound := by
  simp [oneReg, scratchBase]

theorem stateScratchReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ stateScratchReg n bound := by
  simp [stateScratchReg, scratchBase]

theorem addressReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ addressReg n bound := by
  simp [addressReg, scratchBase]

theorem valueReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ valueReg n bound := by
  simp [valueReg, scratchBase]

theorem symbolReg_ge_internal (n bound : ℕ) (tape : Fin (n + 2)) :
    registerCount n bound ≤ symbolReg n bound tape := by
  simp [symbolReg, scratchBase]
  omega

theorem scratch_lt_registerLimit_internal (n bound : ℕ) :
    zeroReg n bound < registerLimit n bound ∧
      oneReg n bound < registerLimit n bound ∧
      stateScratchReg n bound < registerLimit n bound ∧
      addressReg n bound < registerLimit n bound ∧
      valueReg n bound < registerLimit n bound ∧
      ∀ tape, symbolReg n bound tape < registerLimit n bound := by
  constructor
  · simp [zeroReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [oneReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [stateScratchReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [addressReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [valueReg, scratchBase, registerLimit]
    omega
  · intro tape
    simp [symbolReg, scratchBase, registerLimit]
    omega

theorem encodeRegs_storeBounded_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hheads : HeadsBounded cfg bound) :
    StoreBounded tm bound (encodeRegs tm bound cfg) := by
  constructor
  · intro reg hnonzero
    have hreg : reg < registerCount n bound := by
      by_contra hnot
      have hzero := encodeRegs_outside_internal tm bound cfg (Nat.le_of_not_gt hnot)
      exact hnonzero hzero
    exact lt_trans hreg (by
      simp [registerLimit, scratchBase]
      omega)
  · intro reg
    by_cases hreg : reg < registerCount n bound
    · rw [encodeRegs, dif_pos hreg]
      let field := (fieldEquiv n bound).symm ⟨reg, hreg⟩
      change fieldValue tm bound cfg field ≤ wordBound tm bound
      rcases field with state | headOrCell
      · exact le_trans (Nat.le_of_lt (stateCode_lt_internal tm cfg.state))
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · rcases headOrCell with tape | cell
        · exact le_trans (hheads tape) (le_trans (Nat.le_succ bound)
            (le_trans (le_max_right _ _) (le_max_right _ _)))
        · rcases cell with ⟨tape, position⟩
          have hcode : symbolCode ((tapeAt cfg tape).cells position.val) ≤ 3 := by
            cases (tapeAt cfg tape).cells position.val <;> decide
          have hthree : 3 ≤ registerLimit n bound := by
            simp [registerLimit, scratchBase, registerCount]
          exact le_trans hcode
            (le_trans hthree (le_max_left _ _))
    · simp [encodeRegs, hreg]

theorem loadTapeOps_represents_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store) (tape : Fin (n + 2)) :
    Represents tm bound cfg
      (Structured.Basic.execList (loadTapeOps n bound tape) store) := by
  simp only [loadTapeOps, Structured.Basic.execList, Structured.Basic.exec]
  apply Represents.update_outside_internal
  · apply Represents.update_outside_internal
    · exact hrepresents.update_outside_internal (addressReg_ge_internal n bound)
    · exact addressReg_ge_internal n bound
  · exact symbolReg_ge_internal n bound tape

theorem loadTapeOps_symbol_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hhead : (tapeAt cfg tape).head ≤ bound) :
    Structured.Basic.execList (loadTapeOps n bound tape) store
        (symbolReg n bound tape) =
      symbolCode ((tapeAt cfg tape).read) := by
  have hheadValue := hrepresents (headField (bound := bound) tape)
  rw [← headReg_eq_fieldReg_internal] at hheadValue
  change store (headReg tape) = (tapeAt cfg tape).head at hheadValue
  let position : Fin (bound + 1) := ⟨(tapeAt cfg tape).head, by omega⟩
  have hcellValue := hrepresents (cellField tape position)
  rw [← cellBase_add_eq_fieldReg_internal] at hcellValue
  change store (cellBase n bound tape + position.val) =
    symbolCode ((tapeAt cfg tape).cells position.val) at hcellValue
  have haddressHead : addressReg n bound ≠ headReg tape := by
    intro heq
    have hfield := fieldReg_lt_internal
      (headField (bound := bound) tape)
    rw [← headReg_eq_fieldReg_internal] at hfield
    have hscratch := addressReg_ge_internal n bound
    omega
  have haddressCell :
      addressReg n bound ≠ cellBase n bound tape + position.val := by
    rw [cellBase_add_eq_fieldReg_internal]
    exact ne_of_gt (lt_of_lt_of_le (fieldReg_lt_internal _) (addressReg_ge_internal n bound))
  let first :=
    (Structured.Basic.imm (addressReg n bound) (cellBase n bound tape)).exec store
  let addressed :=
    (Structured.Basic.add (addressReg n bound) (addressReg n bound)
      (headReg tape)).exec first
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm haddressHead)]
  have hfirstAddress : first (addressReg n bound) = cellBase n bound tape := by
    simp [first, Structured.Basic.exec]
  have haddressedAddress :
      addressed (addressReg n bound) =
        cellBase n bound tape + (tapeAt cfg tape).head := by
    simp only [addressed, Structured.Basic.exec, Function.update_self]
    rw [hfirstAddress, hfirstHead, hheadValue]
  have haddressedCell :
      addressed (cellBase n bound tape + position.val) =
        store (cellBase n bound tape + position.val) := by
    simp [addressed, first, Structured.Basic.exec,
      Function.update_of_ne (Ne.symm haddressCell)]
  change ((Structured.Basic.load (symbolReg n bound tape) (addressReg n bound)).exec
      addressed) (symbolReg n bound tape) = _
  simp only [Structured.Basic.exec, Function.update_self]
  rw [haddressedAddress]
  change addressed (cellBase n bound tape + position.val) = _
  rw [haddressedCell, hcellValue]
  rfl

end Step

end TMConfig

end RAM

end Complexity
