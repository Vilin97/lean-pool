/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines

/-!
# Decoded sparse-address equality — definitions

The entry decoder leaves an address target at its append position. This stage
rewinds it and compares it against a canonical query address, writing the
Boolean result on a third work tape.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Rewind a decoded address and compare it with a canonical query address. -/
def decodedAddressEqTM {n : ℕ}
    (addressIdx queryIdx resultIdx : Fin n) : TM n :=
  TM.seqTM (TM.rewindWorkTM addressIdx)
    (TM.binaryEqTM addressIdx queryIdx resultIdx)

/-- Linear time bound for decoded-address equality, including its composition
seam. -/
def decodedAddressEqTime (addressBits queryBits : List Bool) : ℕ :=
  addressBits.length + 3 + 1 + TM.binaryEqTime addressBits queryBits

end Machine

end RegisterStore

end RAM

end Complexity
