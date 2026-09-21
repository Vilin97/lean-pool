/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledLog
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalization

/-!
# One directed nearby-Bethe coordinate as a finite-word function

The input is `pair precision (pair tau x)`, where precision is unary, `tau` is
an arbitrary raw rational, and `x` is a canonical rational-entry word.  The
output is the unreduced rational

`scheduledLogLower (1-x) p + tau*x*scheduledLogLower x p`.
-/

namespace BeyondBethe

open Complexity

def machineNearbyCoordinatePrecisionRuler (word : List Bool) : List Bool :=
  machinePairFirst word

def machineNearbyCoordinatePayload (word : List Bool) : List Bool :=
  machinePairSecond word

def machineNearbyCoordinateTauRawCode (word : List Bool) : List Bool :=
  machinePairFirst (machineNearbyCoordinatePayload word)

def machineNearbyCoordinateXCode (word : List Bool) : List Bool :=
  machinePairSecond (machineNearbyCoordinatePayload word)

def machineNearbyCoordinateNegXRawCode (word : List Bool) : List Bool :=
  machineRawRatNegCode (machineNearbyCoordinateXCode word)

def machineNearbyCoordinateComplementUnnormalizedRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair rawRatOneCode (machineNearbyCoordinateNegXRawCode word))

/-- Normalize before logarithm scheduling so that range reduction reads the
canonical numerator and denominator lengths of `1-x`. -/
def machineNearbyCoordinateComplementCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineNearbyCoordinateComplementUnnormalizedRawCode word)

def machineNearbyCoordinateLogComplementRawCode
    (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (pair (machineNearbyCoordinatePrecisionRuler word)
      (machineNearbyCoordinateComplementCode word))

def machineNearbyCoordinateLogXRawCode (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (pair (machineNearbyCoordinatePrecisionRuler word)
      (machineNearbyCoordinateXCode word))

def machineNearbyCoordinateTauTimesXRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineNearbyCoordinateTauRawCode word)
      (machineNearbyCoordinateXCode word))

def machineNearbyCoordinateWeightedLogXRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineNearbyCoordinateTauTimesXRawCode word)
      (machineNearbyCoordinateLogXRawCode word))

def machineNearbyCoordinateLowerRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineNearbyCoordinateLogComplementRawCode word)
      (machineNearbyCoordinateWeightedLogXRawCode word))

theorem machineNearbyCoordinatePrecisionRuler_mem_FP :
    machineNearbyCoordinatePrecisionRuler ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineNearbyCoordinatePayload_mem_FP :
    machineNearbyCoordinatePayload ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineNearbyCoordinateTauRawCode_mem_FP :
    machineNearbyCoordinateTauRawCode ∈ Complexity.FP := by
  simpa only [machineNearbyCoordinateTauRawCode] using
    machineCompose_mem_FP machineNearbyCoordinatePayload_mem_FP
      machinePairFirst_mem_FP

theorem machineNearbyCoordinateXCode_mem_FP :
    machineNearbyCoordinateXCode ∈ Complexity.FP := by
  simpa only [machineNearbyCoordinateXCode] using
    machineCompose_mem_FP machineNearbyCoordinatePayload_mem_FP
      machinePairSecond_mem_FP

theorem machineNearbyCoordinateNegXRawCode_mem_FP :
    machineNearbyCoordinateNegXRawCode ∈ Complexity.FP := by
  simpa only [machineNearbyCoordinateNegXRawCode] using
    machineCompose_mem_FP machineNearbyCoordinateXCode_mem_FP
      machineRawRatNegCode_mem_FP

theorem machineNearbyCoordinateComplementUnnormalizedRawCode_mem_FP :
    machineNearbyCoordinateComplementUnnormalizedRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP (machineConst_mem_FP rawRatOneCode)
    machineNearbyCoordinateNegXRawCode_mem_FP
  simpa only [machineNearbyCoordinateComplementUnnormalizedRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineNearbyCoordinateComplementCode_mem_FP :
    machineNearbyCoordinateComplementCode ∈ Complexity.FP := by
  simpa only [machineNearbyCoordinateComplementCode] using
    machineCompose_mem_FP
      machineNearbyCoordinateComplementUnnormalizedRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineNearbyCoordinateLogComplementRawCode_mem_FP :
    machineNearbyCoordinateLogComplementRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineNearbyCoordinatePrecisionRuler_mem_FP
    machineNearbyCoordinateComplementCode_mem_FP
  simpa only [machineNearbyCoordinateLogComplementRawCode] using
    machineCompose_mem_FP hpair machineScheduledLogLowerRawCode_mem_FP

theorem machineNearbyCoordinateLogXRawCode_mem_FP :
    machineNearbyCoordinateLogXRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineNearbyCoordinatePrecisionRuler_mem_FP
    machineNearbyCoordinateXCode_mem_FP
  simpa only [machineNearbyCoordinateLogXRawCode] using
    machineCompose_mem_FP hpair machineScheduledLogLowerRawCode_mem_FP

theorem machineNearbyCoordinateTauTimesXRawCode_mem_FP :
    machineNearbyCoordinateTauTimesXRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineNearbyCoordinateTauRawCode_mem_FP
    machineNearbyCoordinateXCode_mem_FP
  simpa only [machineNearbyCoordinateTauTimesXRawCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineNearbyCoordinateWeightedLogXRawCode_mem_FP :
    machineNearbyCoordinateWeightedLogXRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineNearbyCoordinateTauTimesXRawCode_mem_FP
    machineNearbyCoordinateLogXRawCode_mem_FP
  simpa only [machineNearbyCoordinateWeightedLogXRawCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineNearbyCoordinateLowerRawCode_mem_FP :
    machineNearbyCoordinateLowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineNearbyCoordinateLogComplementRawCode_mem_FP
    machineNearbyCoordinateWeightedLogXRawCode_mem_FP
  simpa only [machineNearbyCoordinateLowerRawCode] using
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

def rawNearbyCoordinateComplement (x : ℚ) : RawRat :=
  RawRat.one.add (rawRatOfRat x).neg

def rawNearbyCoordinateLower (tau : RawRat) (x : ℚ) (p : ℕ) : RawRat :=
  (rawScheduledLogLower (1 - x) p).add
    ((tau.mul (rawRatOfRat x)).mul (rawScheduledLogLower x p))

@[simp] theorem machineNearbyCoordinateComplementUnnormalizedRawCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateComplementUnnormalizedRawCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (rawNearbyCoordinateComplement x) := by
  rw [machineNearbyCoordinateComplementUnnormalizedRawCode,
    machineNearbyCoordinateNegXRawCode,
    machineNearbyCoordinateXCode, machineNearbyCoordinatePayload]
  simp only [machinePairSecond_pair, machineRawRatNegCode_encode,
    ← rawRatBinaryCode_rawRatOfRat, rawRatOneCode]
  rw [machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineNearbyCoordinateComplementCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateComplementCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (rawRatOfRat (1 - x)) := by
  rw [machineNearbyCoordinateComplementCode,
    machineNearbyCoordinateComplementUnnormalizedRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  apply congrArg rationalEntryBinaryCode
  rw [binaryNormalizeRawRat_eq_value]
  simp [rawNearbyCoordinateComplement, RawRat.value_add,
    RawRat.value_one, RawRat.value_neg, rawRatOfRat_value]
  ring

@[simp] theorem machineNearbyCoordinateLogComplementRawCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateLogComplementRawCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (rawScheduledLogLower (1 - x) p) := by
  rw [machineNearbyCoordinateLogComplementRawCode]
  simp only [machineNearbyCoordinatePrecisionRuler,
    machinePairFirst_pair, machineNearbyCoordinateComplementCode_encode,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineNearbyCoordinateLogXRawCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateLogXRawCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (rawScheduledLogLower x p) := by
  rw [machineNearbyCoordinateLogXRawCode]
  simp only [machineNearbyCoordinatePrecisionRuler,
    machinePairFirst_pair, machineNearbyCoordinateXCode,
    machineNearbyCoordinatePayload, machinePairSecond_pair,
    ← rawRatBinaryCode_rawRatOfRat,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineNearbyCoordinateTauTimesXRawCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateTauTimesXRawCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (tau.mul (rawRatOfRat x)) := by
  rw [machineNearbyCoordinateTauTimesXRawCode]
  simp only [machineNearbyCoordinateTauRawCode,
    machineNearbyCoordinateXCode, machineNearbyCoordinatePayload,
    machinePairSecond_pair, machinePairFirst_pair,
    ← rawRatBinaryCode_rawRatOfRat, machineRawRatMulCode_encode]

@[simp] theorem machineNearbyCoordinateLowerRawCode_encode
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    machineNearbyCoordinateLowerRawCode
        (pair (List.replicate p true)
          (pair (rawRatBinaryCode tau) (rationalEntryBinaryCode x))) =
      rawRatBinaryCode (rawNearbyCoordinateLower tau x p) := by
  rw [machineNearbyCoordinateLowerRawCode,
    machineNearbyCoordinateLogComplementRawCode_encode,
    machineNearbyCoordinateWeightedLogXRawCode,
    machineNearbyCoordinateTauTimesXRawCode_encode,
    machineNearbyCoordinateLogXRawCode_encode,
    machineRawRatMulCode_encode, machineRawRatAddCode_encode]
  rfl

theorem rawNearbyCoordinateLower_value
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    (rawNearbyCoordinateLower tau x p).value =
      directedNearbyCoordinateLower tau.value x p := by
  simp [rawNearbyCoordinateLower, directedNearbyCoordinateLower,
    RawRat.value_add, RawRat.value_mul, rawRatOfRat_value,
    rawScheduledLogLower_value]

end BeyondBethe
