/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalization

/-!
# Exact finite-word minimum of two rationals

The input is the pair of two raw-rational words.  We compare their values and
return one of the original words; the public version then normalizes the
selected fraction.  This is the minimum operation used in the rational
smoothing level.
-/

namespace BeyondBethe

open Complexity

def machineRawRatMinCode (word : List Bool) : List Bool :=
  machineIfHead (machineRawRatLeBit word)
    (machinePairFirst word) (machinePairSecond word)

def machineRationalMinCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatMinCode word)

theorem machineRawRatMinCode_mem_FP :
    machineRawRatMinCode ∈ Complexity.FP := by
  exact machineIfHead_mem_FP machineRawRatLeBit_mem_FP
    machinePairFirst_mem_FP machinePairSecond_mem_FP

theorem machineRationalMinCode_mem_FP :
    machineRationalMinCode ∈ Complexity.FP := by
  simpa only [machineRationalMinCode] using
    machineCompose_mem_FP machineRawRatMinCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

@[simp] theorem machineRawRatMinCode_encode (q r : RawRat) :
    machineRawRatMinCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rawRatBinaryCode (if q.value ≤ r.value then q else r) := by
  rw [machineRawRatMinCode, machineRawRatLeBit_encode]
  by_cases h : q.value ≤ r.value <;> simp [h]

@[simp] theorem machineRationalMinCode_encode (q r : RawRat) :
    machineRationalMinCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rationalBinaryCode (min q.value r.value) := by
  rw [machineRationalMinCode, machineRawRatMinCode_encode]
  by_cases h : q.value ≤ r.value
  · rw [ite_eq_left h, machineNormalizeRawRatBinaryCode_encode,
      binaryNormalizeRawRat_eq_value, min_eq_left h]
  · have hrq : r.value ≤ q.value := le_of_not_ge h
    rw [ite_eq_right h, machineNormalizeRawRatBinaryCode_encode,
      binaryNormalizeRawRat_eq_value, min_eq_right hrq]

end BeyondBethe
