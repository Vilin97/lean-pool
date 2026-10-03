/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeObjectiveCoordinate

/-!
# Finite-word lower endpoint for one directed Bethe gradient coordinate

This file compiles the lower endpoint

`-logUpper(a) + (1+tau) logLower(x) + logLower(1-x) + (2+tau)`

into an ordinary finite-word machine.  It deliberately reuses the canonical
input parser and normalized complement from the objective-coordinate machine,
so the two implementations cannot silently disagree about input layout or
about the representation of `1-x`.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Negates the directed upper approximation to the logarithm of the matrix coefficient. -/
def machineDirectedGradientCoordinateNegLogA
    (word : List Bool) : List Bool :=
  machineRawRatNegCode
    (machineDirectedObjectiveCoordinateLogAUpper word)

/-- Multiplies the directed lower approximation to `log x` by `1 + tau`. -/
def machineDirectedGradientCoordinateScaledLogX
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineDirectedObjectiveCoordinateOnePlusTau word)
      (machineDirectedObjectiveCoordinateLogXLower word))

/-- Computes the directed lower logarithm approximation for the complementary coordinate `1 -
x`. -/
def machineDirectedGradientCoordinateLogComplementLower
    (word : List Bool) : List Bool :=
  machineScheduledLogLowerRawCode
    (machineDirectedObjectiveCoordinateLogComplementInput word)

/-- Adds the negated coefficient logarithm and the scaled coordinate logarithm. -/
def machineDirectedGradientCoordinateFirstTwo
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedGradientCoordinateNegLogA word)
      (machineDirectedGradientCoordinateScaledLogX word))

/-- Adds the complementary-coordinate logarithm to the first two gradient terms. -/
def machineDirectedGradientCoordinateFirstThree
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedGradientCoordinateFirstTwo word)
      (machineDirectedGradientCoordinateLogComplementLower word))

/-- Computes the raw-rational constant term `2 + tau` in the negative-gradient formula. -/
def machineDirectedGradientCoordinateTwoPlusTau
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineDirectedObjectiveCoordinateOnePlusTau word))

/-- Combines the three directed logarithm terms with `2 + tau` into a negative-gradient
approximation. -/
def machineDirectedNegativeGradientLowerRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedGradientCoordinateFirstThree word)
      (machineDirectedGradientCoordinateTwoPlusTau word))

theorem machineDirectedGradientCoordinateNegLogA_mem_FP :
    machineDirectedGradientCoordinateNegLogA ∈ FP := by
  simpa only [machineDirectedGradientCoordinateNegLogA] using!
    machineCompose_mem_FP machineDirectedObjectiveCoordinateLogAUpper_mem_FP
      machineRawRatNegCode_mem_FP

theorem machineDirectedGradientCoordinateScaledLogX_mem_FP :
    machineDirectedGradientCoordinateScaledLogX ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedObjectiveCoordinateOnePlusTau_mem_FP
    machineDirectedObjectiveCoordinateLogXLower_mem_FP
  simpa only [machineDirectedGradientCoordinateScaledLogX] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineDirectedGradientCoordinateLogComplementLower_mem_FP :
    machineDirectedGradientCoordinateLogComplementLower ∈ FP := by
  simpa only [machineDirectedGradientCoordinateLogComplementLower] using!
    machineCompose_mem_FP
      machineDirectedObjectiveCoordinateLogComplementInput_mem_FP
      machineScheduledLogLowerRawCode_mem_FP

theorem machineDirectedGradientCoordinateFirstTwo_mem_FP :
    machineDirectedGradientCoordinateFirstTwo ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedGradientCoordinateNegLogA_mem_FP
    machineDirectedGradientCoordinateScaledLogX_mem_FP
  simpa only [machineDirectedGradientCoordinateFirstTwo] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedGradientCoordinateFirstThree_mem_FP :
    machineDirectedGradientCoordinateFirstThree ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedGradientCoordinateFirstTwo_mem_FP
    machineDirectedGradientCoordinateLogComplementLower_mem_FP
  simpa only [machineDirectedGradientCoordinateFirstThree] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedGradientCoordinateTwoPlusTau_mem_FP :
    machineDirectedGradientCoordinateTwoPlusTau ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineDirectedObjectiveCoordinateOnePlusTau_mem_FP
  simpa only [machineDirectedGradientCoordinateTwoPlusTau] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedNegativeGradientLowerRawCode_mem_FP :
    machineDirectedNegativeGradientLowerRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineDirectedGradientCoordinateFirstThree_mem_FP
    machineDirectedGradientCoordinateTwoPlusTau_mem_FP
  simpa only [machineDirectedNegativeGradientLowerRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

/-- The raw formula `-logUpper(a) + (1+tau)*logLower(x) + logLower(1-x) + 2+tau` at precision
`p`. -/
def rawDirectedNegativeGradientLower
    (tau a x : ℚ) (p : ℕ) : RawRat :=
  let rawTau := rawRatOfRat tau
  let negLogA := (rawScheduledLogUpper a p).neg
  let scaledLogX := (RawRat.one.add rawTau).mul
    (rawScheduledLogLower x p)
  let logComplement := rawScheduledLogLower (1 - x) p
  let twoPlusTau := RawRat.one.add (RawRat.one.add rawTau)
  ((negLogA.add scaledLogX).add logComplement).add twoPlusTau

@[simp] theorem machineDirectedGradientCoordinateNegLogA_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateNegLogA
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawScheduledLogUpper a p).neg := by
  rw [machineDirectedGradientCoordinateNegLogA,
    machineDirectedObjectiveCoordinateLogAUpper_encode,
    machineRawRatNegCode_encode]

@[simp] theorem machineDirectedGradientCoordinateScaledLogX_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateScaledLogX
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((RawRat.one.add (rawRatOfRat tau)).mul
          (rawScheduledLogLower x p)) := by
  rw [machineDirectedGradientCoordinateScaledLogX,
    machineDirectedObjectiveCoordinateOnePlusTau_encode,
    machineDirectedObjectiveCoordinateLogXLower_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineDirectedGradientCoordinateLogComplementLower_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateLogComplementLower
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawScheduledLogLower (1 - x) p) := by
  rw [machineDirectedGradientCoordinateLogComplementLower,
    machineDirectedObjectiveCoordinateLogComplementInput,
    machineDirectedObjectiveCoordinatePrecision_encode,
    machineDirectedObjectiveCoordinateComplement_encode,
    machineScheduledLogLowerRawCode_encode]

@[simp] theorem machineDirectedGradientCoordinateFirstTwo_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateFirstTwo
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        ((rawScheduledLogUpper a p).neg.add
          ((RawRat.one.add (rawRatOfRat tau)).mul
            (rawScheduledLogLower x p))) := by
  rw [machineDirectedGradientCoordinateFirstTwo,
    machineDirectedGradientCoordinateNegLogA_encode,
    machineDirectedGradientCoordinateScaledLogX_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineDirectedGradientCoordinateFirstThree_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateFirstThree
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        (((rawScheduledLogUpper a p).neg.add
          ((RawRat.one.add (rawRatOfRat tau)).mul
            (rawScheduledLogLower x p))).add
          (rawScheduledLogLower (1 - x) p)) := by
  rw [machineDirectedGradientCoordinateFirstThree,
    machineDirectedGradientCoordinateFirstTwo_encode,
    machineDirectedGradientCoordinateLogComplementLower_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineDirectedGradientCoordinateTwoPlusTau_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedGradientCoordinateTwoPlusTau
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode
        (RawRat.one.add (RawRat.one.add (rawRatOfRat tau))) := by
  rw [machineDirectedGradientCoordinateTwoPlusTau,
    machineDirectedObjectiveCoordinateOnePlusTau_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineDirectedNegativeGradientLowerRawCode_encode
    (tau a x : ℚ) (p : ℕ) :
    machineDirectedNegativeGradientLowerRawCode
        (machineDirectedObjectiveCoordinateCanonicalWord tau a x p) =
      rawRatBinaryCode (rawDirectedNegativeGradientLower tau a x p) := by
  rw [machineDirectedNegativeGradientLowerRawCode,
    machineDirectedGradientCoordinateFirstThree_encode,
    machineDirectedGradientCoordinateTwoPlusTau_encode,
    machineRawRatAddCode_encode]
  rfl

theorem rawDirectedNegativeGradientLower_value
    (tau a x : ℚ) (p : ℕ) :
    (rawDirectedNegativeGradientLower tau a x p).value =
      directedNegativeGradientLower tau a x p := by
  simp [rawDirectedNegativeGradientLower,
    directedNegativeGradientLower, RawRat.value_add, RawRat.value_mul,
    RawRat.value_neg, RawRat.value_one, rawRatOfRat_value,
    rawScheduledLogLower_value, rawScheduledLogUpper_value]
  ring

end BeyondBethe
