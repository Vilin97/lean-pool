/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Internal

/-!
# Bounded Turing-machine configurations in RAM registers

This module exposes the first representation layer of the Turing-machine to RAM
simulation. The register layout is explicit, blank cells use value zero, and
`decode_encode` states the exact condition under which bounded decoding loses no
information.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

variable {n bound : ℕ}

/-- The state field is register zero. -/
@[simp] theorem fieldReg_state :
    fieldReg (stateField (n := n) (bound := bound)) = 0 :=
  fieldReg_state_internal

/-- Head registers immediately follow the state, in input/work/output order. -/
@[simp] theorem fieldReg_head (tape : Fin (n + 2)) :
    fieldReg (headField (bound := bound) tape) = 1 + tape.val :=
  fieldReg_head_internal tape

/-- Cell blocks follow all head registers, ordered by tape and position. -/
@[simp] theorem fieldReg_cell (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    fieldReg (cellField tape position) =
      1 + (n + 2) + tape.val * (bound + 1) + position.val :=
  fieldReg_cell_internal tape position

/-- Symbol coding is lossless on the four-symbol tape alphabet. -/
theorem symbolDecode_code (symbol : Γ) :
    symbolDecode (symbolCode symbol) = symbol :=
  symbolDecode_code_internal symbol

/-- Canonical finite-state coding is lossless. -/
theorem stateDecode_code (tm : TM n) (state : tm.Q) :
    stateDecode tm (stateCode tm state) = state :=
  stateDecode_code_internal tm state

/-- Reading an encoded field returns exactly that field's value. -/
theorem encodeRegs_field (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (field : Field n bound) :
    encodeRegs tm bound cfg (fieldReg field) = fieldValue tm bound cfg field :=
  encodeRegs_field_internal tm bound cfg field

/-- Every field address lies inside the explicit configuration prefix. -/
theorem fieldReg_lt (field : Field n bound) :
    fieldReg field < registerCount n bound :=
  fieldReg_lt_internal field

/-- Distinct configuration fields occupy distinct registers. -/
theorem fieldReg_injective : Function.Injective (@fieldReg n bound) :=
  fieldReg_injective_internal

/-- Updating a scratch register beyond the configuration prefix preserves every
represented field. -/
theorem Represents.update_outside {tm : TM n} {bound reg value : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {regs : ℕ → ℕ}
    (hrepresents : Represents tm bound cfg regs)
    (hreg : registerCount n bound ≤ reg) :
    Represents tm bound cfg (Function.update regs reg value) :=
  hrepresents.update_outside_internal hreg

/-- The canonical bounded encoding represents every one of its fields. -/
theorem encodeRegs_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    Represents tm bound cfg (encodeRegs tm bound cfg) :=
  encodeRegs_represents_internal tm bound cfg

/-- Any representing store decodes to its configuration when the omitted tape
suffixes are blank. Scratch registers do not affect decoding. -/
theorem decode_of_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) : decode tm bound regs = cfg :=
  decode_of_represents_internal tm bound cfg regs hrepresents hbounded

/-- Decoding an encoded bounded configuration recovers it exactly. -/
theorem decode_encode (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hbounded : Bounded cfg bound) :
    decode tm bound (encode tm bound cfg).regs = cfg :=
  decode_encode_internal tm bound cfg hbounded

/-- Registers beyond the explicit bounded layout are zero. -/
theorem encodeRegs_outside (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) {reg : ℕ}
    (hreg : registerCount n bound ≤ reg) :
    encodeRegs tm bound cfg reg = 0 :=
  encodeRegs_outside_internal tm bound cfg hreg

end TMConfig

end RAM

end Complexity
