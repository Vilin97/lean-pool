/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheAffineEntry
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare
import LeanPool.BeyondBethe.BeyondBethe.MachineBool

/-!
# Exact finite-word test for a violated Bethe floor constraint

The floor oracle must distinguish the strict inequality
`betheAffineMatrixQ y i j < delta` from the permitted boundary case.  We do
this without normalization or approximate arithmetic: compute the recovered
entry as an unreduced rational and negate the exact comparison
`delta <= entry`.
-/

namespace BeyondBethe

open Complexity

def machineBetheFloorTestThreshold (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBetheFloorTestEntryWord (word : List Bool) : List Bool :=
  machinePairSecond word

def machineBetheFloorTestEntryRawCode (word : List Bool) : List Bool :=
  machineBetheAffineEntryRawCode (machineBetheFloorTestEntryWord word)

def machineBetheFloorTestThresholdLeEntryBit
    (word : List Bool) : List Bool :=
  machineRawRatLeBit
    (pair (machineBetheFloorTestThreshold word)
      (machineBetheFloorTestEntryRawCode word))

/-- One-bit answer, true exactly when the recovered entry is strictly below
the supplied rational floor on canonical inputs. -/
def machineBetheFloorViolationBit (word : List Bool) : List Bool :=
  machineNotBit (machineBetheFloorTestThresholdLeEntryBit word)

theorem machineBetheFloorTestThreshold_mem_FP :
    machineBetheFloorTestThreshold ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorTestEntryWord_mem_FP :
    machineBetheFloorTestEntryWord ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFloorTestEntryRawCode_mem_FP :
    machineBetheFloorTestEntryRawCode ∈ FP := by
  simpa only [machineBetheFloorTestEntryRawCode] using!
    machineCompose_mem_FP machineBetheFloorTestEntryWord_mem_FP
      machineBetheAffineEntryRawCode_mem_FP

theorem machineBetheFloorTestThresholdLeEntryBit_mem_FP :
    machineBetheFloorTestThresholdLeEntryBit ∈ FP := by
  have hinput := machinePair_mem_FP
    machineBetheFloorTestThreshold_mem_FP
    machineBetheFloorTestEntryRawCode_mem_FP
  simpa only [machineBetheFloorTestThresholdLeEntryBit] using!
    machineCompose_mem_FP hinput machineRawRatLeBit_mem_FP

theorem machineBetheFloorViolationBit_mem_FP :
    machineBetheFloorViolationBit ∈ FP := by
  simpa only [machineBetheFloorViolationBit] using!
    machineNotBit_mem_FP
      machineBetheFloorTestThresholdLeEntryBit_mem_FP

def machineBetheFloorTestCanonicalWord {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) : List Bool :=
  pair (rawRatBinaryCode delta)
    (machineBetheAffineEntryCanonicalWord i j y)

@[simp] theorem machineBetheFloorTestThreshold_encode {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) :
    machineBetheFloorTestThreshold
        (machineBetheFloorTestCanonicalWord delta i j y) =
      rawRatBinaryCode delta := by
  simp [machineBetheFloorTestThreshold,
    machineBetheFloorTestCanonicalWord]

@[simp] theorem machineBetheFloorTestEntryWord_encode {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) :
    machineBetheFloorTestEntryWord
        (machineBetheFloorTestCanonicalWord delta i j y) =
      machineBetheAffineEntryCanonicalWord i j y := by
  simp [machineBetheFloorTestEntryWord,
    machineBetheFloorTestCanonicalWord]

@[simp] theorem machineBetheFloorTestEntryRawCode_encode {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) :
    machineBetheFloorTestEntryRawCode
        (machineBetheFloorTestCanonicalWord delta i j y) =
      rawRatBinaryCode (rawBetheAffineEntry y i j) := by
  rw [machineBetheFloorTestEntryRawCode,
    machineBetheFloorTestEntryWord_encode,
    machineBetheAffineEntryRawCode_encode]

@[simp] theorem machineBetheFloorTestThresholdLeEntryBit_encode {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) :
    machineBetheFloorTestThresholdLeEntryBit
        (machineBetheFloorTestCanonicalWord delta i j y) =
      [decide (delta.value ≤ betheAffineMatrixQ y i j)] := by
  rw [machineBetheFloorTestThresholdLeEntryBit,
    machineBetheFloorTestThreshold_encode,
    machineBetheFloorTestEntryRawCode_encode,
    machineRawRatLeBit_encode,
    rawBetheAffineEntry_value]

@[simp] theorem machineBetheFloorViolationBit_encode {m : ℕ}
    (delta : RawRat) (i j : Fin (m + 1))
    (y : Fin (m * m) → ℚ) :
    machineBetheFloorViolationBit
        (machineBetheFloorTestCanonicalWord delta i j y) =
      [decide (betheAffineMatrixQ y i j < delta.value)] := by
  rw [machineBetheFloorViolationBit,
    machineBetheFloorTestThresholdLeEntryBit_encode,
    machineNotBit_one]
  by_cases h : delta.value ≤ betheAffineMatrixQ y i j
  · have hnot : ¬betheAffineMatrixQ y i j < delta.value :=
      not_lt_of_ge h
    simp [h, hnot]
  · have hlt : betheAffineMatrixQ y i j < delta.value := lt_of_not_ge h
    simp [h, hlt]

end BeyondBethe
