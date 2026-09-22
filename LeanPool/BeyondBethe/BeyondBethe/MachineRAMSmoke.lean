/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineTrimHighZeros
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine

/-!
# End-to-end smoke test for the RAM bit-graph bridge

This file instantiates every layer of the bridge on the canonical empty
output.  Although the computed function is deliberately trivial, the theorem
checks the complete interface: padded RAM input, logarithmic-cost decision,
simulation by a deterministic Turing machine, bounded bit assembly, and
canonical high-zero trimming.
-/

namespace BeyondBethe

open Complexity

def emptyMachineTarget (_ : List Bool) : List Bool := []

theorem outputBitLanguage_emptyMachineTarget :
    outputBitLanguage emptyMachineTarget = (∅ : Language) := by
  ext payload
  simp [outputBitLanguage, emptyMachineTarget]

theorem paddedOutputBitLanguage_emptyMachineTarget (count : ℕ) :
    MachineRAMBridge.paddedLanguage count
        (outputBitLanguage emptyMachineTarget) = (∅ : Language) := by
  rw [outputBitLanguage_emptyMachineTarget]
  ext payload
  simp [MachineRAMBridge.paddedLanguage]

/-- A concrete theorem exercising the complete padded-RAM-to-`FP` reduction.
No machine-time premise is accepted from the caller. -/
theorem emptyMachineTarget_mem_FP_from_paddedRAM (count : ℕ) :
    emptyMachineTarget ∈ Complexity.FP := by
  let ruler : List Bool → List Bool := fun _ => []
  have hdecides : RAM.rejectProg.DecidesInTime
      (MachineRAMBridge.paddedLanguage count
        (outputBitLanguage emptyMachineTarget))
      (2 : Polynomial ℕ).eval := by
    rw [paddedOutputBitLanguage_emptyMachineTarget]
    simpa using! RAM.rejectProg_decides
  apply canonicalTarget_mem_FP_of_paddedRamBitProgram count
    emptyMachineTarget ruler RAM.rejectProg (2 : Polynomial ℕ) hdecides
  · exact machineConst_mem_FP []
  · intro word
    simp [emptyMachineTarget, ruler]
  · intro word
    rfl

end BeyondBethe
