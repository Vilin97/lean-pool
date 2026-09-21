/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs

/-!
# Bounded Turing-machine configuration encoding -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

theorem fieldReg_state_internal :
    fieldReg (stateField (n := n) (bound := bound)) = 0 := by
  rfl

theorem fieldReg_head_internal (tape : Fin (n + 2)) :
    fieldReg (headField (bound := bound) tape) = 1 + tape.val := by
  rfl

theorem fieldReg_cell_internal (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    fieldReg (cellField tape position) =
      1 + (n + 2) + tape.val * (bound + 1) + position.val := by
  simp [fieldReg, cellField, fieldEquiv, finProdFinEquiv, Nat.mul_comm]
  simp [finSumFinEquiv]
  change 1 + (n + 2 + (position.val + tape.val * (bound + 1))) = _
  omega

theorem symbolDecode_code_internal (symbol : Γ) :
    symbolDecode (symbolCode symbol) = symbol := by
  cases symbol <;> rfl

theorem stateDecode_code_internal (tm : TM n) (state : tm.Q) :
    stateDecode tm (stateCode tm state) = state := by
  simp [stateDecode, stateCode]

theorem tapeAt_input_internal (cfg : Complexity.Cfg n Q) :
    tapeAt cfg ⟨0, by omega⟩ = cfg.input := by
  simp [tapeAt]

theorem tapeAt_work_internal (cfg : Complexity.Cfg n Q) (i : Fin n) :
    tapeAt cfg ⟨i.val + 1, by omega⟩ = cfg.work i := by
  simp only [tapeAt]
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 1

theorem tapeAt_output_internal (cfg : Complexity.Cfg n Q) :
    tapeAt cfg ⟨n + 1, by omega⟩ = cfg.output := by
  simp [tapeAt]

theorem encodeRegs_field_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (field : Field n bound) :
    encodeRegs tm bound cfg (fieldReg field) = fieldValue tm bound cfg field := by
  have hreg : fieldReg field < registerCount n bound :=
    (fieldEquiv n bound field).isLt
  unfold encodeRegs
  rw [dif_pos hreg]
  have hfield :
      (⟨fieldReg field, hreg⟩ : Fin (registerCount n bound)) =
        fieldEquiv n bound field := by
    apply Fin.ext
    rfl
  rw [hfield, Equiv.symm_apply_apply]

theorem fieldReg_lt_internal (field : Field n bound) :
    fieldReg field < registerCount n bound :=
  (fieldEquiv n bound field).isLt

theorem fieldReg_injective_internal :
    Function.Injective (@fieldReg n bound) := by
  intro first second heq
  apply (fieldEquiv n bound).injective
  exact Fin.ext heq

theorem Represents.update_outside_internal {tm : TM n} {bound reg value : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {regs : ℕ → ℕ}
    (hrepresents : Represents tm bound cfg regs)
    (hreg : registerCount n bound ≤ reg) :
    Represents tm bound cfg (Function.update regs reg value) := by
  intro field
  rw [Function.update_of_ne]
  · exact hrepresents field
  · exact fun heq => (not_lt_of_ge hreg) (heq ▸ fieldReg_lt_internal field)

theorem encodeRegs_represents_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    Represents tm bound cfg (encodeRegs tm bound cfg) :=
  encodeRegs_field_internal tm bound cfg

private theorem decodeTape_of_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) (tape : Fin (n + 2)) :
    decodeTape bound regs tape = tapeAt cfg tape := by
  apply Tape.ext
  · simp only [decodeTape]
    rw [hrepresents (headField (bound := bound) tape)]
    rfl
  · funext position
    by_cases hposition : position < bound + 1
    · simp only [decodeTape, hposition, dif_pos]
      rw [hrepresents (cellField tape ⟨position, hposition⟩)]
      exact symbolDecode_code_internal _
    · simp only [decodeTape, hposition]
      exact (hbounded tape position (by omega)).symm

theorem decode_of_represents_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) : decode tm bound regs = cfg := by
  apply Complexity.Cfg.ext
  · simp only [decode]
    rw [hrepresents (stateField (n := n) (bound := bound))]
    exact stateDecode_code_internal tm cfg.state
  · simpa [decode, tapeAt_input_internal] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨0, by omega⟩
  · funext i
    simpa [decode, tapeAt_work_internal] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨i.val + 1, by omega⟩
  · simpa [decode, tapeAt_output_internal] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨n + 1, by omega⟩

theorem decode_encode_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hbounded : Bounded cfg bound) :
    decode tm bound (encode tm bound cfg).regs = cfg := by
  exact decode_of_represents_internal tm bound cfg (encode tm bound cfg).regs
    (encodeRegs_represents_internal tm bound cfg) hbounded

theorem encodeRegs_outside_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) {reg : ℕ}
    (hreg : registerCount n bound ≤ reg) :
    encodeRegs tm bound cfg reg = 0 := by
  simp [encodeRegs, Nat.not_lt.mpr hreg]

end TMConfig

end RAM

end Complexity
