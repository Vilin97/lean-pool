/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorCutEntry
import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledLog
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalization

/-!
# Finite-word lower endpoint for one directed Bethe objective coordinate

This file compiles the three scheduled logarithms and the exact rational
arithmetic in `directedNegativeObjectiveCoordinateLower` into one ordinary
bitstring machine.  The complement `1-x` is normalized before it is passed
to the logarithm routine, so the scheduled-log correctness theorem applies
to the canonical reduced rational rather than an unreduced subtraction.
-/

namespace BeyondBethe

open Complexity

def machineDirectedObjectiveCoordinatePrecision
    (word : List Bool) : List Bool := machinePairFirst word

def machineDirectedObjectiveCoordinateRest
    (word : List Bool) : List Bool := machinePairSecond word

def machineDirectedObjectiveCoordinateTau
    (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedObjectiveCoordinateRest word)

def machineDirectedObjectiveCoordinateA
    (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machineDirectedObjectiveCoordinateRest word))

def machineDirectedObjectiveCoordinateX
    (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond
    (machineDirectedObjectiveCoordinateRest word))

def machineDirectedObjectiveCoordinateComplementRaw
    (word : List Bool) : List Bool :=
  machineRawRatSubCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineDirectedObjectiveCoordinateX word))

def machineDirectedObjectiveCoordinateComplement
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineDirectedObjectiveCoordinateComplementRaw word)

def machineDirectedObjectiveCoordinateLogAInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedObjectiveCoordinatePrecision word)
    (machineDirectedObjectiveCoordinateA word)

def machineDirectedObjectiveCoordinateLogXInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedObjectiveCoordinatePrecision word)
    (machineDirectedObjectiveCoordinateX word)

def machineDirectedObjectiveCoordinateLogComplementInput
    (word : List Bool) : List Bool :=
  pair (machineDirectedObjectiveCoordinatePrecision word)
    (machineDirectedObjectiveCoordinateComplement word)

def machineDirectedObjectiveCoordinateLogAUpper
    (word : List Bool) : List Bool :=
  machineScheduledLogUpperRawCode
    (machineDirectedObjectiveCoordinateLogAInput word)

def machineDirectedObjectiveCoordinateLogXLower
    (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (machineDirectedObjectiveCoordinateLogXInput word)

def machineDirectedObjectiveCoordinateLogComplementUpper
    (word : List Bool) : List Bool :=
  machineScheduledLogUpperRawCode
    (machineDirectedObjectiveCoordinateLogComplementInput word)

def machineDirectedObjectiveCoordinateNegX
    (word : List Bool) : List Bool :=
  machineRawRatNegCode (machineDirectedObjectiveCoordinateX word)

def machineDirectedObjectiveCoordinateFirstTerm
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedObjectiveCoordinateNegX word)
      (machineDirectedObjectiveCoordinateLogAUpper word))

def machineDirectedObjectiveCoordinateOnePlusTau
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineDirectedObjectiveCoordinateTau word))

def machineDirectedObjectiveCoordinateMiddleScale
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedObjectiveCoordinateOnePlusTau word)
      (machineDirectedObjectiveCoordinateX word))

def machineDirectedObjectiveCoordinateMiddleTerm
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedObjectiveCoordinateMiddleScale word)
      (machineDirectedObjectiveCoordinateLogXLower word))

def machineDirectedObjectiveCoordinateComplementProduct
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedObjectiveCoordinateComplement word)
      (machineDirectedObjectiveCoordinateLogComplementUpper word))

def machineDirectedObjectiveCoordinateLastTerm
    (word : List Bool) : List Bool :=
  machineRawRatNegCode
    (machineDirectedObjectiveCoordinateComplementProduct word)

def machineDirectedObjectiveCoordinateFirstTwo
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedObjectiveCoordinateFirstTerm word)
      (machineDirectedObjectiveCoordinateMiddleTerm word))

def machineDirectedNegativeObjectiveCoordinateLowerRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedObjectiveCoordinateFirstTwo word)
      (machineDirectedObjectiveCoordinateLastTerm word))

theorem machineDirectedObjectiveCoordinatePrecision_mem_FP :
    machineDirectedObjectiveCoordinatePrecision ∈ FP := machinePairFirst_mem_FP

theorem machineDirectedObjectiveCoordinateRest_mem_FP :
    machineDirectedObjectiveCoordinateRest ∈ FP := machinePairSecond_mem_FP

theorem machineDirectedObjectiveCoordinateTau_mem_FP :
    machineDirectedObjectiveCoordinateTau ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateTau] using!
    machineCompose_mem_FP machineDirectedObjectiveCoordinateRest_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedObjectiveCoordinateA_mem_FP :
    machineDirectedObjectiveCoordinateA ∈ FP := by
  have htail := machineCompose_mem_FP
    machineDirectedObjectiveCoordinateRest_mem_FP machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveCoordinateA] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineDirectedObjectiveCoordinateX_mem_FP :
    machineDirectedObjectiveCoordinateX ∈ FP := by
  have htail := machineCompose_mem_FP
    machineDirectedObjectiveCoordinateRest_mem_FP machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveCoordinateX] using!
    machineCompose_mem_FP htail machinePairSecond_mem_FP

theorem machineDirectedObjectiveCoordinateComplementRaw_mem_FP :
    machineDirectedObjectiveCoordinateComplementRaw ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineDirectedObjectiveCoordinateX_mem_FP
  simpa only [machineDirectedObjectiveCoordinateComplementRaw] using!
    machineCompose_mem_FP hinput machineRawRatSubCode_mem_FP

theorem machineDirectedObjectiveCoordinateComplement_mem_FP :
    machineDirectedObjectiveCoordinateComplement ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateComplement] using!
    machineCompose_mem_FP
      machineDirectedObjectiveCoordinateComplementRaw_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineDirectedObjectiveCoordinateLogAInput_mem_FP :
    machineDirectedObjectiveCoordinateLogAInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveCoordinatePrecision_mem_FP
    machineDirectedObjectiveCoordinateA_mem_FP

theorem machineDirectedObjectiveCoordinateLogXInput_mem_FP :
    machineDirectedObjectiveCoordinateLogXInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveCoordinatePrecision_mem_FP
    machineDirectedObjectiveCoordinateX_mem_FP

theorem machineDirectedObjectiveCoordinateLogComplementInput_mem_FP :
    machineDirectedObjectiveCoordinateLogComplementInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveCoordinatePrecision_mem_FP
    machineDirectedObjectiveCoordinateComplement_mem_FP

theorem machineDirectedObjectiveCoordinateLogAUpper_mem_FP :
    machineDirectedObjectiveCoordinateLogAUpper ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateLogAUpper] using!
    machineCompose_mem_FP machineDirectedObjectiveCoordinateLogAInput_mem_FP
      machineScheduledLogUpperRawCode_mem_FP

theorem machineDirectedObjectiveCoordinateLogXLower_mem_FP :
    machineDirectedObjectiveCoordinateLogXLower ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateLogXLower] using!
    machineCompose_mem_FP machineDirectedObjectiveCoordinateLogXInput_mem_FP
      machineScheduledLogLowerRawCode_mem_FP

theorem machineDirectedObjectiveCoordinateLogComplementUpper_mem_FP :
    machineDirectedObjectiveCoordinateLogComplementUpper ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateLogComplementUpper] using!
    machineCompose_mem_FP
      machineDirectedObjectiveCoordinateLogComplementInput_mem_FP
      machineScheduledLogUpperRawCode_mem_FP

theorem machineDirectedObjectiveCoordinateNegX_mem_FP :
    machineDirectedObjectiveCoordinateNegX ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateNegX] using!
    machineCompose_mem_FP machineDirectedObjectiveCoordinateX_mem_FP
      machineRawRatNegCode_mem_FP

theorem machineDirectedObjectiveCoordinateFirstTerm_mem_FP :
    machineDirectedObjectiveCoordinateFirstTerm ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateNegX_mem_FP
    machineDirectedObjectiveCoordinateLogAUpper_mem_FP
  simpa only [machineDirectedObjectiveCoordinateFirstTerm] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectedObjectiveCoordinateOnePlusTau_mem_FP :
    machineDirectedObjectiveCoordinateOnePlusTau ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineDirectedObjectiveCoordinateTau_mem_FP
  simpa only [machineDirectedObjectiveCoordinateOnePlusTau] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedObjectiveCoordinateMiddleScale_mem_FP :
    machineDirectedObjectiveCoordinateMiddleScale ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateOnePlusTau_mem_FP
    machineDirectedObjectiveCoordinateX_mem_FP
  simpa only [machineDirectedObjectiveCoordinateMiddleScale] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectedObjectiveCoordinateMiddleTerm_mem_FP :
    machineDirectedObjectiveCoordinateMiddleTerm ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateMiddleScale_mem_FP
    machineDirectedObjectiveCoordinateLogXLower_mem_FP
  simpa only [machineDirectedObjectiveCoordinateMiddleTerm] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectedObjectiveCoordinateComplementProduct_mem_FP :
    machineDirectedObjectiveCoordinateComplementProduct ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateComplement_mem_FP
    machineDirectedObjectiveCoordinateLogComplementUpper_mem_FP
  simpa only [machineDirectedObjectiveCoordinateComplementProduct] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectedObjectiveCoordinateLastTerm_mem_FP :
    machineDirectedObjectiveCoordinateLastTerm ∈ FP := by
  simpa only [machineDirectedObjectiveCoordinateLastTerm] using!
    machineCompose_mem_FP
      machineDirectedObjectiveCoordinateComplementProduct_mem_FP
      machineRawRatNegCode_mem_FP

theorem machineDirectedObjectiveCoordinateFirstTwo_mem_FP :
    machineDirectedObjectiveCoordinateFirstTwo ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateFirstTerm_mem_FP
    machineDirectedObjectiveCoordinateMiddleTerm_mem_FP
  simpa only [machineDirectedObjectiveCoordinateFirstTwo] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedNegativeObjectiveCoordinateLowerRawCode_mem_FP :
    machineDirectedNegativeObjectiveCoordinateLowerRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateFirstTwo_mem_FP
    machineDirectedObjectiveCoordinateLastTerm_mem_FP
  simpa only [machineDirectedNegativeObjectiveCoordinateLowerRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

def machineDirectedObjectiveCoordinateCanonicalWord
    (tau a x : ℚ) (p : ℕ) : List Bool :=
  pair (List.replicate p true)
    (pair (rawRatBinaryCode (rawRatOfRat tau))
      (pair (rawRatBinaryCode (rawRatOfRat a))
        (rawRatBinaryCode (rawRatOfRat x))))

def rawDirectedNegativeObjectiveCoordinateLower
    (tau a x : ℚ) (p : ℕ) : RawRat :=
  let rawTau := rawRatOfRat tau
  let rawX := rawRatOfRat x
  let rawComplement := rawRatOfRat (1 - x)
  let first := rawX.neg.mul (rawScheduledLogUpper a p)
  let middle := (RawRat.one.add rawTau).mul rawX |>.mul
    (rawScheduledLogLower x p)
  let last := (rawComplement.mul
    (rawScheduledLogUpper (1 - x) p)).neg
  (first.add middle).add last

@[simp] theorem machineDirectedObjectiveCoordinatePrecision_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinatePrecision
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      List.replicate p true := by
  simp [machineDirectedObjectiveCoordinatePrecision,
    machineDirectedObjectiveCoordinateCanonicalWord]

@[simp] theorem machineDirectedObjectiveCoordinateTau_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateTau
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawRatOfRat tau) := by
  simp [machineDirectedObjectiveCoordinateTau,
    machineDirectedObjectiveCoordinateRest,
    machineDirectedObjectiveCoordinateCanonicalWord]

@[simp] theorem machineDirectedObjectiveCoordinateA_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateA
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawRatOfRat a) := by
  simp [machineDirectedObjectiveCoordinateA,
    machineDirectedObjectiveCoordinateRest,
    machineDirectedObjectiveCoordinateCanonicalWord]

@[simp] theorem machineDirectedObjectiveCoordinateX_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateX
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawRatOfRat x) := by
  simp [machineDirectedObjectiveCoordinateX,
    machineDirectedObjectiveCoordinateRest,
    machineDirectedObjectiveCoordinateCanonicalWord]

@[simp] theorem machineDirectedObjectiveCoordinateComplement_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateComplement
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawRatOfRat (1 - x)) := by
  rw [machineDirectedObjectiveCoordinateComplement,
    machineDirectedObjectiveCoordinateComplementRaw,
    machineDirectedObjectiveCoordinateX,
    machineDirectedObjectiveCoordinateRest,
    machineDirectedObjectiveCoordinateCanonicalWord]
  simp only [machinePairSecond_pair,
    machineRawRatSubCode_encode,
    machineNormalizeRawRatEntryCode_encode]
  rw [rawRatBinaryCode_rawRatOfRat]
  congr 1
  simp [binaryNormalizeRawRat_eq_value, RawRat.value_sub,
    rawRatOfRat_value]

@[simp] theorem machineDirectedObjectiveCoordinateLogAUpper_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateLogAUpper
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawScheduledLogUpper a p) := by
  rw [machineDirectedObjectiveCoordinateLogAUpper,
    machineDirectedObjectiveCoordinateLogAInput,
    machineDirectedObjectiveCoordinatePrecision_encode,
    machineDirectedObjectiveCoordinateA_encode,
    machineScheduledLogUpperRawCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateLogXLower_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateLogXLower
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawScheduledLogLower x p) := by
  rw [machineDirectedObjectiveCoordinateLogXLower,
    machineDirectedObjectiveCoordinateLogXInput,
    machineDirectedObjectiveCoordinatePrecision_encode,
    machineDirectedObjectiveCoordinateX_encode,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateLogComplementUpper_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateLogComplementUpper
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawScheduledLogUpper (1 - x) p) := by
  rw [machineDirectedObjectiveCoordinateLogComplementUpper,
    machineDirectedObjectiveCoordinateLogComplementInput,
    machineDirectedObjectiveCoordinatePrecision_encode,
    machineDirectedObjectiveCoordinateComplement_encode,
    machineScheduledLogUpperRawCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateNegX_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateNegX
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawRatOfRat x).neg := by
  rw [machineDirectedObjectiveCoordinateNegX,
    machineDirectedObjectiveCoordinateX_encode,
    machineRawRatNegCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateFirstTerm_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateFirstTerm
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((rawRatOfRat x).neg.mul (rawScheduledLogUpper a p)) := by
  rw [machineDirectedObjectiveCoordinateFirstTerm,
    machineDirectedObjectiveCoordinateNegX_encode,
    machineDirectedObjectiveCoordinateLogAUpper_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateOnePlusTau_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateOnePlusTau
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (RawRat.one.add (rawRatOfRat tau)) := by
  rw [machineDirectedObjectiveCoordinateOnePlusTau,
    machineDirectedObjectiveCoordinateTau_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateMiddleScale_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateMiddleScale
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((RawRat.one.add (rawRatOfRat tau)).mul (rawRatOfRat x)) := by
  rw [machineDirectedObjectiveCoordinateMiddleScale,
    machineDirectedObjectiveCoordinateOnePlusTau_encode,
    machineDirectedObjectiveCoordinateX_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateMiddleTerm_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateMiddleTerm
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        (((RawRat.one.add (rawRatOfRat tau)).mul (rawRatOfRat x)).mul
          (rawScheduledLogLower x p)) := by
  rw [machineDirectedObjectiveCoordinateMiddleTerm,
    machineDirectedObjectiveCoordinateMiddleScale_encode,
    machineDirectedObjectiveCoordinateLogXLower_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateComplementProduct_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateComplementProduct
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((rawRatOfRat (1 - x)).mul
          (rawScheduledLogUpper (1 - x) p)) := by
  rw [machineDirectedObjectiveCoordinateComplementProduct,
    machineDirectedObjectiveCoordinateComplement_encode,
    machineDirectedObjectiveCoordinateLogComplementUpper_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateLastTerm_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateLastTerm
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((rawRatOfRat (1 - x)).mul
          (rawScheduledLogUpper (1 - x) p)).neg := by
  rw [machineDirectedObjectiveCoordinateLastTerm,
    machineDirectedObjectiveCoordinateComplementProduct_encode,
    machineRawRatNegCode_encode]

@[simp] theorem machineDirectedObjectiveCoordinateFirstTwo_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedObjectiveCoordinateFirstTwo
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        (((rawRatOfRat x).neg.mul (rawScheduledLogUpper a p)).add
          (((RawRat.one.add (rawRatOfRat tau)).mul (rawRatOfRat x)).mul
            (rawScheduledLogLower x p))) := by
  rw [machineDirectedObjectiveCoordinateFirstTwo,
    machineDirectedObjectiveCoordinateFirstTerm_encode,
    machineDirectedObjectiveCoordinateMiddleTerm_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineDirectedNegativeObjectiveCoordinateLowerRawCode_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedNegativeObjectiveCoordinateLowerRawCode
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        (rawDirectedNegativeObjectiveCoordinateLower tau a x p) := by
  rw [machineDirectedNegativeObjectiveCoordinateLowerRawCode,
    machineDirectedObjectiveCoordinateFirstTwo_encode,
    machineDirectedObjectiveCoordinateLastTerm_encode,
    machineRawRatAddCode_encode]
  rfl

theorem rawDirectedNegativeObjectiveCoordinateLower_value
    (tau a x : ℚ) (p : ℕ) :
    (rawDirectedNegativeObjectiveCoordinateLower tau a x p).value =
      directedNegativeObjectiveCoordinateLower tau a x p := by
  simp [rawDirectedNegativeObjectiveCoordinateLower,
    directedNegativeObjectiveCoordinateLower,
    RawRat.value_add, RawRat.value_mul, RawRat.value_neg,
    RawRat.value_one, rawRatOfRat_value,
    rawScheduledLogLower_value, rawScheduledLogUpper_value]
  ring

end BeyondBethe
