/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Internal

/-!
# Sparse TM-step address and loading layout -- proof internals
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

theorem symbolCode_lt_internal (symbol : Γ) : symbolCode symbol < 4 := by
  cases symbol <;> decide

theorem addressOps_represents_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (tape : Fin (n + 2)) :
    Represents tm cfg (Structured.Basic.execList (addressOps n tape) store) := by
  have hrange := scratch_range_internal n
  simp only [addressOps, Structured.Basic.execList]
  apply Represents.update_control_internal
  · apply Represents.update_control_internal
    · exact hrepresents.update_control_internal hrange.2.2.2.2.2.1.1
        hrange.2.2.2.2.2.1.2
    · exact hrange.2.2.2.2.1.1
    · exact hrange.2.2.2.2.1.2
  · exact hrange.2.2.2.2.1.1
  · exact hrange.2.2.2.2.1.2

theorem loadTapeOps_represents_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (tape : Fin (n + 2)) :
    Represents tm cfg (Structured.Basic.execList (loadTapeOps n tape) store) := by
  have hrange := scratch_range_internal n
  rw [loadTapeOps, execList_append]
  simp only [Structured.Basic.execList, Structured.Basic.exec]
  exact (addressOps_represents_internal hrepresents tape).update_control_internal
    (hrange.2.2.2.2.2.2 tape).1 (hrange.2.2.2.2.2.2 tape).2

theorem addressOps_address_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (tape : Fin (n + 2))
    (htapeCount : store (tapeCountReg n) = n + 2) :
    Structured.Basic.execList (addressOps n tape) store (addressReg n) =
      cellReg n tape (tapeAt cfg tape).head := by
  have hhead := hrepresents (Sum.inr (Sum.inl tape))
  change store (headReg tape) = (tapeAt cfg tape).head at hhead
  have hvalueHead : valueReg n ≠ headReg tape := by
    simp [valueReg, headReg]
    omega
  have hvalueCount : valueReg n ≠ tapeCountReg n := by
    simp [valueReg, tapeCountReg]
  have haddressValue : addressReg n ≠ valueReg n := by
    simp [addressReg, valueReg]
  let first := (Structured.Basic.imm (valueReg n)
    (cellBase n + tape.val)).exec store
  let multiplied := (Structured.Basic.mul (addressReg n) (headReg tape)
    (tapeCountReg n)).exec first
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm hvalueHead)]
  have hfirstCount : first (tapeCountReg n) = store (tapeCountReg n) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm hvalueCount)]
  have hfirstValue : first (valueReg n) = cellBase n + tape.val := by
    simp [first, Structured.Basic.exec]
  have hmultipliedAddress : multiplied (addressReg n) =
      (tapeAt cfg tape).head * (n + 2) := by
    simp only [multiplied, Structured.Basic.exec, Function.update_self]
    rw [hfirstHead, hfirstCount, hhead, htapeCount]
  have hmultipliedValue : multiplied (valueReg n) = cellBase n + tape.val := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (Ne.symm haddressValue), hfirstValue]
  simp only [addressOps, Structured.Basic.execList]
  change ((Structured.Basic.add (addressReg n) (addressReg n)
    (valueReg n)).exec multiplied) (addressReg n) = _
  simp only [Structured.Basic.exec, Function.update_self]
  rw [hmultipliedAddress, hmultipliedValue]
  simp [cellReg]
  omega

theorem loadTapeOps_symbol_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm cfg store) (tape : Fin (n + 2))
    (htapeCount : store (tapeCountReg n) = n + 2) :
    Structured.Basic.execList (loadTapeOps n tape) store (symbolReg n tape) =
      symbolCode ((tapeAt cfg tape).read) := by
  let addressed := Structured.Basic.execList (addressOps n tape) store
  have haddress : addressed (addressReg n) =
      cellReg n tape (tapeAt cfg tape).head :=
    addressOps_address_internal hrepresents tape htapeCount
  have haddressedRepresents := addressOps_represents_internal hrepresents tape
  have hcell := haddressedRepresents
    (Sum.inr (Sum.inr (tape, (tapeAt cfg tape).head)))
  change addressed (cellReg n tape (tapeAt cfg tape).head) =
    symbolCode ((tapeAt cfg tape).cells (tapeAt cfg tape).head) at hcell
  rw [loadTapeOps, execList_append]
  simp only [Structured.Basic.execList, Structured.Basic.exec, Function.update_self]
  change addressed (addressed (addressReg n)) = _
  rw [haddress, hcell]
  rfl

end Sparse

end TMConfig

end RAM

end Complexity
