/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorL1

/-!
# Polynomial-time coefficients for the rational ellipsoid update

The square-root-free central update uses three dimension-dependent rational
coefficients.  This module constructs them from the ordinary little-endian
binary word for the dimension, using only the verified unreduced rational
arithmetic machines.  The raw formulas are kept explicit so that no field
operation is hidden in the executable layer.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- The raw-rational constant one used in ellipsoid updates. -/
def rawEllipsoidOne : RawRat := RawRat.ofNat 1
/-- The raw-rational constant two used in ellipsoid updates. -/
def rawEllipsoidTwo : RawRat := RawRat.ofNat 2
/-- The raw-rational constant four used in ellipsoid updates. -/
def rawEllipsoidFour : RawRat := RawRat.ofNat 4

/-- Embeds the ellipsoid dimension as a raw rational. -/
def rawEllipsoidDimension (d : ℕ) : RawRat := RawRat.ofNat d

/-- The square of the ellipsoid dimension as a raw rational. -/
def rawEllipsoidDimensionSquare (d : ℕ) : RawRat :=
  (rawEllipsoidDimension d).mul (rawEllipsoidDimension d)

/-- Four times the squared ellipsoid dimension as a raw rational. -/
def rawEllipsoidFourDimensionSquare (d : ℕ) : RawRat :=
  rawEllipsoidFour.mul (rawEllipsoidDimensionSquare d)

/-- The raw-rational update parameter `alpha = 1/(4*d^2)`. -/
def rawEllipsoidAlpha (d : ℕ) : RawRat :=
  rawEllipsoidOne.div (rawEllipsoidFourDimensionSquare d)

/-- The square of the ellipsoid update parameter `alpha`. -/
def rawEllipsoidAlphaSquare (d : ℕ) : RawRat :=
  (rawEllipsoidAlpha d).mul (rawEllipsoidAlpha d)

/-- Twice the square of the ellipsoid update parameter `alpha`. -/
def rawEllipsoidTwiceAlphaSquare (d : ℕ) : RawRat :=
  rawEllipsoidTwo.mul (rawEllipsoidAlphaSquare d)

/-- The perpendicular update scale `1 + 2*alpha^2`. -/
def rawEllipsoidPerpScale (d : ℕ) : RawRat :=
  rawEllipsoidOne.add (rawEllipsoidTwiceAlphaSquare d)

/-- The update parameter `alpha` divided by the ellipsoid dimension. -/
def rawEllipsoidAlphaOverDimension (d : ℕ) : RawRat :=
  (rawEllipsoidAlpha d).div (rawEllipsoidDimension d)

/-- The parallel update scale `1 - alpha/d`. -/
def rawEllipsoidParallelScale (d : ℕ) : RawRat :=
  rawEllipsoidOne.sub (rawEllipsoidAlphaOverDimension d)

/-! ## Finite-word formulas -/

/-- Encodes binary dimension bits as a nonnegative raw rational with denominator one. -/
def machineEllipsoidDimensionRawCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode word) [true]

/-- Squares the encoded raw-rational ellipsoid dimension. -/
def machineEllipsoidDimensionSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineEllipsoidDimensionRawCode word)
      (machineEllipsoidDimensionRawCode word))

/-- Computes four times the encoded squared dimension. -/
def machineEllipsoidFourDimensionSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawEllipsoidFour)
      (machineEllipsoidDimensionSquareRawCode word))

/-- Computes the encoded update parameter `1/(4*d^2)`. -/
def machineEllipsoidAlphaRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode rawEllipsoidOne)
      (machineEllipsoidFourDimensionSquareRawCode word))

/-- Squares the encoded ellipsoid update parameter. -/
def machineEllipsoidAlphaSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineEllipsoidAlphaRawCode word)
      (machineEllipsoidAlphaRawCode word))

/-- Computes twice the encoded squared update parameter. -/
def machineEllipsoidTwiceAlphaSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawEllipsoidTwo)
      (machineEllipsoidAlphaSquareRawCode word))

/-- Computes the encoded perpendicular scale `1 + 2*alpha^2`. -/
def machineEllipsoidPerpScaleRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawEllipsoidOne)
      (machineEllipsoidTwiceAlphaSquareRawCode word))

/-- Divides the encoded update parameter by the dimension. -/
def machineEllipsoidAlphaOverDimensionRawCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineEllipsoidAlphaRawCode word)
      (machineEllipsoidDimensionRawCode word))

/-- Computes the encoded parallel scale `1 - alpha/d`. -/
def machineEllipsoidParallelScaleRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawEllipsoidOne)
      (machineRawRatNegCode
        (machineEllipsoidAlphaOverDimensionRawCode word)))

/-- Normalizes the ellipsoid update parameter into a rational entry code. -/
def machineEllipsoidAlphaEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineEllipsoidAlphaRawCode word)

/-- Normalizes the perpendicular update scale into a rational entry code. -/
def machineEllipsoidPerpScaleEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineEllipsoidPerpScaleRawCode word)

/-- Normalizes the parallel update scale into a rational entry code. -/
def machineEllipsoidParallelScaleEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineEllipsoidParallelScaleRawCode word)

/-! ## Polynomial-time closure -/

theorem machineEllipsoidDimensionRawCode_mem_FP :
    machineEllipsoidDimensionRawCode ∈ FP := by
  exact machinePair_mem_FP
    (machineCompose_mem_FP id_mem_FP machineNaturalIntegerCode_mem_FP)
    (machineConst_mem_FP [true])

theorem machineEllipsoidDimensionSquareRawCode_mem_FP :
    machineEllipsoidDimensionSquareRawCode ∈ FP := by
  simpa only [machineEllipsoidDimensionSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineEllipsoidDimensionRawCode_mem_FP
        machineEllipsoidDimensionRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineEllipsoidFourDimensionSquareRawCode_mem_FP :
    machineEllipsoidFourDimensionSquareRawCode ∈ FP := by
  simpa only [machineEllipsoidFourDimensionSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidFour))
        machineEllipsoidDimensionSquareRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineEllipsoidAlphaRawCode_mem_FP :
    machineEllipsoidAlphaRawCode ∈ FP := by
  simpa only [machineEllipsoidAlphaRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidOne))
        machineEllipsoidFourDimensionSquareRawCode_mem_FP)
      machineRawRatDivCode_mem_FP

theorem machineEllipsoidAlphaSquareRawCode_mem_FP :
    machineEllipsoidAlphaSquareRawCode ∈ FP := by
  simpa only [machineEllipsoidAlphaSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineEllipsoidAlphaRawCode_mem_FP
        machineEllipsoidAlphaRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineEllipsoidTwiceAlphaSquareRawCode_mem_FP :
    machineEllipsoidTwiceAlphaSquareRawCode ∈ FP := by
  simpa only [machineEllipsoidTwiceAlphaSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidTwo))
        machineEllipsoidAlphaSquareRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineEllipsoidPerpScaleRawCode_mem_FP :
    machineEllipsoidPerpScaleRawCode ∈ FP := by
  simpa only [machineEllipsoidPerpScaleRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidOne))
        machineEllipsoidTwiceAlphaSquareRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineEllipsoidAlphaOverDimensionRawCode_mem_FP :
    machineEllipsoidAlphaOverDimensionRawCode ∈ FP := by
  simpa only [machineEllipsoidAlphaOverDimensionRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineEllipsoidAlphaRawCode_mem_FP
        machineEllipsoidDimensionRawCode_mem_FP)
      machineRawRatDivCode_mem_FP

theorem machineEllipsoidParallelScaleRawCode_mem_FP :
    machineEllipsoidParallelScaleRawCode ∈ FP := by
  have hneg := machineCompose_mem_FP
    machineEllipsoidAlphaOverDimensionRawCode_mem_FP
    machineRawRatNegCode_mem_FP
  simpa only [machineEllipsoidParallelScaleRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidOne))
        hneg)
      machineRawRatAddCode_mem_FP

theorem machineEllipsoidAlphaEntryCode_mem_FP :
    machineEllipsoidAlphaEntryCode ∈ FP := by
  simpa only [machineEllipsoidAlphaEntryCode] using!
    machineCompose_mem_FP machineEllipsoidAlphaRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineEllipsoidPerpScaleEntryCode_mem_FP :
    machineEllipsoidPerpScaleEntryCode ∈ FP := by
  simpa only [machineEllipsoidPerpScaleEntryCode] using!
    machineCompose_mem_FP machineEllipsoidPerpScaleRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineEllipsoidParallelScaleEntryCode_mem_FP :
    machineEllipsoidParallelScaleEntryCode ∈ FP := by
  simpa only [machineEllipsoidParallelScaleEntryCode] using!
    machineCompose_mem_FP machineEllipsoidParallelScaleRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

/-! ## Exact semantics -/

@[simp] theorem machineEllipsoidDimensionRawCode_encode (d : ℕ) :
    machineEllipsoidDimensionRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidDimension d) := by
  rw [machineEllipsoidDimensionRawCode,
    machineNaturalIntegerCode_natBits]
  simp [rawEllipsoidDimension, RawRat.ofNat, rawRatBinaryCode]

@[simp] theorem machineEllipsoidDimensionSquareRawCode_encode (d : ℕ) :
    machineEllipsoidDimensionSquareRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidDimensionSquare d) := by
  rw [machineEllipsoidDimensionSquareRawCode,
    machineEllipsoidDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineEllipsoidFourDimensionSquareRawCode_encode (d : ℕ) :
    machineEllipsoidFourDimensionSquareRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidFourDimensionSquare d) := by
  rw [machineEllipsoidFourDimensionSquareRawCode,
    machineEllipsoidDimensionSquareRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineEllipsoidAlphaRawCode_encode (d : ℕ) :
    machineEllipsoidAlphaRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidAlpha d) := by
  rw [machineEllipsoidAlphaRawCode,
    machineEllipsoidFourDimensionSquareRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineEllipsoidAlphaSquareRawCode_encode (d : ℕ) :
    machineEllipsoidAlphaSquareRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidAlphaSquare d) := by
  rw [machineEllipsoidAlphaSquareRawCode,
    machineEllipsoidAlphaRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineEllipsoidTwiceAlphaSquareRawCode_encode (d : ℕ) :
    machineEllipsoidTwiceAlphaSquareRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidTwiceAlphaSquare d) := by
  rw [machineEllipsoidTwiceAlphaSquareRawCode,
    machineEllipsoidAlphaSquareRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineEllipsoidPerpScaleRawCode_encode (d : ℕ) :
    machineEllipsoidPerpScaleRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidPerpScale d) := by
  rw [machineEllipsoidPerpScaleRawCode,
    machineEllipsoidTwiceAlphaSquareRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineEllipsoidAlphaOverDimensionRawCode_encode (d : ℕ) :
    machineEllipsoidAlphaOverDimensionRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidAlphaOverDimension d) := by
  rw [machineEllipsoidAlphaOverDimensionRawCode,
    machineEllipsoidAlphaRawCode_encode,
    machineEllipsoidDimensionRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineEllipsoidParallelScaleRawCode_encode (d : ℕ) :
    machineEllipsoidParallelScaleRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidParallelScale d) := by
  rw [machineEllipsoidParallelScaleRawCode,
    machineEllipsoidAlphaOverDimensionRawCode_encode,
    machineRawRatNegCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem rawEllipsoidDimension_value (d : ℕ) :
    (rawEllipsoidDimension d).value = d := by
  simp [rawEllipsoidDimension]

@[simp] theorem rawEllipsoidAlpha_value (d : ℕ) :
    (rawEllipsoidAlpha d).value = rationalEllipsoidAlpha d := by
  simp [rawEllipsoidAlpha, rawEllipsoidFourDimensionSquare,
    rawEllipsoidDimensionSquare, rawEllipsoidFour, rawEllipsoidOne,
    rationalEllipsoidAlpha]
  ring

@[simp] theorem rawEllipsoidPerpScale_value (d : ℕ) :
    (rawEllipsoidPerpScale d).value = rationalEllipsoidPerpScale d := by
  simp [rawEllipsoidPerpScale, rawEllipsoidTwiceAlphaSquare,
    rawEllipsoidAlphaSquare, rawEllipsoidTwo, rawEllipsoidOne,
    rationalEllipsoidPerpScale, pow_two]

@[simp] theorem rawEllipsoidParallelScale_value (d : ℕ) :
    (rawEllipsoidParallelScale d).value =
      rationalEllipsoidParallelScale d := by
  simp [rawEllipsoidParallelScale, rawEllipsoidAlphaOverDimension,
    rawEllipsoidOne, rationalEllipsoidParallelScale]

@[simp] theorem machineEllipsoidAlphaEntryCode_encode (d : ℕ) :
    machineEllipsoidAlphaEntryCode d.bits =
      rationalEntryBinaryCode (rationalEllipsoidAlpha d) := by
  rw [machineEllipsoidAlphaEntryCode,
    machineEllipsoidAlphaRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawEllipsoidAlpha_value]

@[simp] theorem machineEllipsoidPerpScaleEntryCode_encode (d : ℕ) :
    machineEllipsoidPerpScaleEntryCode d.bits =
      rationalEntryBinaryCode (rationalEllipsoidPerpScale d) := by
  rw [machineEllipsoidPerpScaleEntryCode,
    machineEllipsoidPerpScaleRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawEllipsoidPerpScale_value]

@[simp] theorem machineEllipsoidParallelScaleEntryCode_encode (d : ℕ) :
    machineEllipsoidParallelScaleEntryCode d.bits =
      rationalEntryBinaryCode (rationalEllipsoidParallelScale d) := by
  rw [machineEllipsoidParallelScaleEntryCode,
    machineEllipsoidParallelScaleRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawEllipsoidParallelScale_value]

end BeyondBethe
