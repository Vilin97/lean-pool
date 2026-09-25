/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Internal

/-!
# Sparse RAM public-input initialization

The concrete initializer streams nonzero public-input bits into a canonical
sparse store, installs the optional length register, and produces the exact
clean work-tape image consumed by the reusable RAM program controller.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The concrete initializer's sparse store is the streamed nonzero input
entries followed by the optional nonzero length register. -/
theorem programInitialStore_eq_append (input : List Bool) :
    programInitialStore input =
      inputBitStoreFrom 1 input ++
        if input.length = 0 then [] else [(0, input.length)] :=
  programInitialStore_eq_append_internal input

/-- The concrete initializer emits one entry per true input bit and one more
exactly when the input is nonempty. -/
theorem programInitialStore_length (input : List Bool) :
    (programInitialStore input).length =
      inputTrueCount input + if input.length = 0 then 0 else 1 :=
  programInitialStore_length_internal input

/-- The sparse store produced from public input is canonical. -/
theorem programInitialStore_canonical (input : List Bool) :
    Canonical (programInitialStore input) :=
  programInitialStore_canonical_internal input

/-- The initializer's pure sparse snapshot represents the RAM public-input
configuration exactly. -/
theorem programInitialSnapshot_represents (input : List Bool) :
    (programInitialSnapshot input).Represents (RAM.initCfg input) :=
  programInitialSnapshot_represents_internal input

/-- Complete public-input initialization reaches the exact sparse snapshot
image consumed by the reusable program loop. -/
theorem programInitTM_hoareTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (programInitTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp.HasBinarySuffix [] ∧
        work = programSnapshotWork tapes (programInitialSnapshot input) ∧
        out = TM.resetBinaryBlank)
      (programInitTime tapes input) :=
  programInitTM_hoareTime_internal tapes input

end Machine

end RegisterStore

end RAM

end Complexity
