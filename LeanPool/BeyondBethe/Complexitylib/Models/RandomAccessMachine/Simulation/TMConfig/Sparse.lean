/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Internal

/-!
# Sparse unbounded TM configurations in RAM registers

This is the fixed-layout representation used for the uniform TM-to-RAM
simulation. Unlike the bounded dense layout, its addresses do not depend on an
input length or running-time bound.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Distinct sparse fields occupy distinct RAM registers. -/
theorem fieldReg_injective : Function.Injective (@fieldReg n) :=
  fieldReg_injective_internal

/-- The canonical sparse encoding represents every state, head, and cell. -/
theorem encodeRegs_represents (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    Represents tm cfg (encodeRegs tm cfg) :=
  encodeRegs_represents_internal tm cfg

/-- Any representing sparse store decodes to its complete configuration; no
external cell-window premise is needed. -/
theorem decode_of_represents (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (store : Structured.Store) (hrepresents : Represents tm cfg store) :
    decode tm store = cfg :=
  decode_of_represents_internal tm cfg store hrepresents

/-- Sparse encoding followed by decoding is exact for every configuration. -/
theorem decode_encode (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    decode tm (encodeRegs tm cfg) = cfg :=
  decode_encode_internal tm cfg

end Sparse

end TMConfig

end RAM

end Complexity
