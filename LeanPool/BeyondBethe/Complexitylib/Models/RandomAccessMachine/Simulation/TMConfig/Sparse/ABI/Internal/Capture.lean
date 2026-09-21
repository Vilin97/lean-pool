/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Defs
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Capturing raw-input scratch bits in finite control -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


theorem initRegs_bool_of_pos_internal (x : List Bool) {reg : ℕ}
    (hpos : 0 < reg) : initRegs x reg = 0 ∨ initRegs x reg = 1 := by
  rw [initRegs, if_neg (by omega)]
  cases hbit : x[reg - 1]? with
  | none => simp
  | some bit =>
      cases bit <;> simp

theorem captureRegs_positive_internal (n : ℕ) {reg : ℕ}
    (hmem : reg ∈ captureRegs n) : 0 < reg := by
  simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
    addressReg, valueReg] at hmem
  rcases hmem with h | h | h | h | h | h <;> omega

/-- If the selected leaf executes, the generated capture tree executes that
same leaf without changing the store. Branch costs are left existential here;
the later resource layer assigns their common envelope. -/
theorem captureInput_exec_of_leaf_internal (tm : TM n)
    (store : Structured.Store) (regs : List ℕ)
    (captured : List (ℕ × ℕ)) {final : Structured.Store}
    (hbits : ∀ reg, reg ∈ regs → store reg = 0 ∨ store reg = 1)
    (hleaf : ∃ steps cost space,
      Structured.Exec (marshalLeaf tm (captureValues store regs captured))
        store final steps cost space) :
    ∃ steps cost space,
      Structured.Exec (captureInput tm regs captured)
        store final steps cost space := by
  induction regs generalizing captured with
  | nil =>
      simpa [captureInput, captureValues] using hleaf
  | cons reg rest ih =>
      have hreg := hbits reg (by simp)
      have hrest : ∀ candidate, candidate ∈ rest →
          store candidate = 0 ∨ store candidate = 1 := by
        intro candidate hmem
        exact hbits candidate (by simp [hmem])
      simp only [captureValues] at hleaf
      obtain ⟨steps, cost, space, hbranch⟩ :=
        ih ((reg, store reg) :: captured) hrest hleaf
      rcases hreg with hzero | hone
      · refine ⟨steps + 1, bitlen (store reg) + 1 + cost,
          max store.space space, ?_⟩
        simpa [captureInput, hzero] using
          (Structured.Exec.ifZero (onNonzero :=
            captureInput tm rest ((reg, 1) :: captured)) hzero hbranch)
      · have hnonzero : store reg ≠ 0 := by omega
        refine ⟨steps + 2, bitlen (store reg) + 1 + cost + 1,
          max store.space space, ?_⟩
        simpa [captureInput, hone] using
          (Structured.Exec.ifNonzero (onZero :=
            captureInput tm rest ((reg, 0) :: captured)) hnonzero hbranch)

/-- Specialization of finite capture to the public RAM input store. -/
theorem marshalInput_exec_of_leaf_internal (tm : TM n) (x : List Bool)
    {final : Structured.Store}
    (hleaf : ∃ steps cost space,
      Structured.Exec
        (marshalLeaf tm (captureValues (initRegs x) (captureRegs n) []))
        (initRegs x) final steps cost space) :
    ∃ steps cost space,
      Structured.Exec (marshalInput tm) (initRegs x) final steps cost space := by
  apply captureInput_exec_of_leaf_internal tm (initRegs x) (captureRegs n) []
  · intro reg hmem
    exact initRegs_bool_of_pos_internal x
      (captureRegs_positive_internal n hmem)
  · exact hleaf

end Sparse

end TMConfig

end RAM

end Complexity
