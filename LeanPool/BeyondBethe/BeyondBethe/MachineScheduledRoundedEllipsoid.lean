/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDyadicFloorMatrix

/-!
# Polynomial-time scheduled rounded ellipsoid update

This module implements the determinant-independent rounded state transition.
The center and basis are floored at a unary precision.  The rounded basis is
then left-multiplied by an explicitly constructed scalar diagonal matrix,
which realizes the prescribed inflation without another matrix mapper.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Represent the rounding-inflation denominator `1024 * d^4` as a raw rational. -/
def rawRoundedInflationDenominator (d : ℕ) : RawRat :=
  (RawRat.ofNat 1024).mul
    ((rawEllipsoidDimensionSquare d).mul
      (rawEllipsoidDimensionSquare d))

/-- Represent the inflation amount `1 / (1024 * d^4)` using total raw-rational division. -/
def rawRoundedInflation (d : ℕ) : RawRat :=
  rawEllipsoidOne.div (rawRoundedInflationDenominator d)

/-- Add one to the raw rounding-inflation amount to obtain the basis scale factor. -/
def rawRoundedInflationFactor (d : ℕ) : RawRat :=
  rawEllipsoidOne.add (rawRoundedInflation d)

@[simp] theorem rawRoundedInflation_value (d : ℕ) :
    (rawRoundedInflation d).value = roundedEllipsoidInflation d := by
  simp [rawRoundedInflation, rawRoundedInflationDenominator,
    roundedEllipsoidInflation, rawEllipsoidDimensionSquare,
    rawEllipsoidOne, RawRat.value_one, RawRat.value_ofNat]
  ring

@[simp] theorem rawRoundedInflationFactor_value (d : ℕ) :
    (rawRoundedInflationFactor d).value =
      1 + roundedEllipsoidInflation d := by
  simp [rawRoundedInflationFactor, rawEllipsoidOne,
    RawRat.value_one, RawRat.value_ofNat]

/-- Extract the unary precision ruler from a scheduled ellipsoid-rounding input. -/
def machineScheduledRoundPrecision (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the encoded ellipsoid state from a scheduled-rounding input. -/
def machineScheduledRoundState (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the binary dimension from the ellipsoid state being rounded. -/
def machineScheduledRoundDimensionBits (word : List Bool) : List Bool :=
  machineRationalEllipsoidDimensionWord (machineScheduledRoundState word)

/-- Convert the ellipsoid dimension to unary, bounded by the encoded state length. -/
def machineScheduledRoundDimensionUnary (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineScheduledRoundState word)
      (machineScheduledRoundDimensionBits word))

/-- Extract the rational center-vector code from the ellipsoid state being rounded. -/
def machineScheduledRoundCenter (word : List Bool) : List Bool :=
  machineRationalEllipsoidCenterWord (machineScheduledRoundState word)

/-- Extract the rational basis-matrix code from the ellipsoid state being rounded. -/
def machineScheduledRoundBasis (word : List Bool) : List Bool :=
  machineRationalEllipsoidBasisWord (machineScheduledRoundState word)

/-- Convert a binary dimension word into its raw-rational scalar code. -/
def machineRoundedInflationDimensionRawCode
    (word : List Bool) : List Bool :=
  machineEllipsoidDimensionRawCode word

/-- Square the encoded dimension using raw-rational multiplication. -/
def machineRoundedInflationDimensionSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineRoundedInflationDimensionRawCode word)
      (machineRoundedInflationDimensionRawCode word))

/-- Square the raw dimension square to encode its fourth power. -/
def machineRoundedInflationDimensionFourthRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineRoundedInflationDimensionSquareRawCode word)
      (machineRoundedInflationDimensionSquareRawCode word))

/-- Multiply the encoded fourth power of the dimension by 1024 to form the inflation
denominator. -/
def machineRoundedInflationDenominatorRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode (RawRat.ofNat 1024))
      (machineRoundedInflationDimensionFourthRawCode word))

/-- Divide raw rational one by the encoded inflation denominator. -/
def machineRoundedInflationRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode rawEllipsoidOne)
      (machineRoundedInflationDenominatorRawCode word))

/-- Add raw rational one to the encoded inflation amount. -/
def machineRoundedInflationFactorRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawEllipsoidOne)
      (machineRoundedInflationRawCode word))

/-- Normalize the raw inflation factor into a rational matrix-entry code. -/
def machineRoundedInflationFactorEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineRoundedInflationFactorRawCode word)

/-- Floor the ellipsoid center coordinates at the scheduled dyadic precision. -/
def machineScheduledRoundCenterCode (word : List Bool) : List Bool :=
  machineDyadicFloorVectorCode
    (pair (machineScheduledRoundPrecision word)
      (machineScheduledRoundCenter word))

/-- Floor the ellipsoid basis entries at the scheduled dyadic precision. -/
def machineScheduledRoundFlooredBasisCode
    (word : List Bool) : List Bool :=
  machineDyadicFloorMatrixCode
    (pair (machineScheduledRoundPrecision word)
      (machineScheduledRoundBasis word))

/-- Construct the scalar diagonal matrix whose diagonal is the normalized rounding-inflation
factor. -/
def machineScheduledRoundInflationDiagonalCode
    (word : List Bool) : List Bool :=
  machineDiagonalBasisRowsCode
    (pair (machineScheduledRoundDimensionUnary word)
      (machineRoundedInflationFactorEntryCode
        (machineScheduledRoundDimensionBits word)))

/-- Left-multiply the dyadically floored basis by the scalar inflation diagonal matrix. -/
def machineScheduledRoundBasisCode (word : List Bool) : List Bool :=
  machineRationalMatrixMulCode
    (pair (machineScheduledRoundDimensionUnary word)
      (pair (machineScheduledRoundInflationDiagonalCode word)
        (machineScheduledRoundFlooredBasisCode word)))

/-- Input: `pair precisionUnary rationalEllipsoidStateBinaryCode`. -/
def machineScheduledRoundedEllipsoidCode (word : List Bool) : List Bool :=
  pair (machineScheduledRoundDimensionBits word)
    (pair (machineScheduledRoundCenterCode word)
      (machineScheduledRoundBasisCode word))

/-! ## Polynomial-time closure -/

theorem machineScheduledRoundPrecision_mem_FP :
    machineScheduledRoundPrecision ∈ FP := machinePairFirst_mem_FP

theorem machineScheduledRoundState_mem_FP :
    machineScheduledRoundState ∈ FP := machinePairSecond_mem_FP

theorem machineScheduledRoundDimensionBits_mem_FP :
    machineScheduledRoundDimensionBits ∈ FP := by
  simpa only [machineScheduledRoundDimensionBits] using!
    machineCompose_mem_FP machineScheduledRoundState_mem_FP
      machineRationalEllipsoidDimensionWord_mem_FP

theorem machineScheduledRoundDimensionUnary_mem_FP :
    machineScheduledRoundDimensionUnary ∈ FP := by
  have hinput := machinePair_mem_FP machineScheduledRoundState_mem_FP
    machineScheduledRoundDimensionBits_mem_FP
  simpa only [machineScheduledRoundDimensionUnary] using!
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineScheduledRoundCenter_mem_FP :
    machineScheduledRoundCenter ∈ FP := by
  simpa only [machineScheduledRoundCenter] using!
    machineCompose_mem_FP machineScheduledRoundState_mem_FP
      machineRationalEllipsoidCenterWord_mem_FP

theorem machineScheduledRoundBasis_mem_FP :
    machineScheduledRoundBasis ∈ FP := by
  simpa only [machineScheduledRoundBasis] using!
    machineCompose_mem_FP machineScheduledRoundState_mem_FP
      machineRationalEllipsoidBasisWord_mem_FP

theorem machineRoundedInflationDimensionRawCode_mem_FP :
    machineRoundedInflationDimensionRawCode ∈ FP :=
  machineEllipsoidDimensionRawCode_mem_FP

theorem machineRoundedInflationDimensionSquareRawCode_mem_FP :
    machineRoundedInflationDimensionSquareRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRoundedInflationDimensionRawCode_mem_FP
    machineRoundedInflationDimensionRawCode_mem_FP
  simpa only [machineRoundedInflationDimensionSquareRawCode] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineRoundedInflationDimensionFourthRawCode_mem_FP :
    machineRoundedInflationDimensionFourthRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRoundedInflationDimensionSquareRawCode_mem_FP
    machineRoundedInflationDimensionSquareRawCode_mem_FP
  simpa only [machineRoundedInflationDimensionFourthRawCode] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineRoundedInflationDenominatorRawCode_mem_FP :
    machineRoundedInflationDenominatorRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (RawRat.ofNat 1024)))
    machineRoundedInflationDimensionFourthRawCode_mem_FP
  simpa only [machineRoundedInflationDenominatorRawCode] using!
    machineCompose_mem_FP hinput machineRawRatMulCode_mem_FP

theorem machineRoundedInflationRawCode_mem_FP :
    machineRoundedInflationRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidOne))
    machineRoundedInflationDenominatorRawCode_mem_FP
  simpa only [machineRoundedInflationRawCode] using!
    machineCompose_mem_FP hinput machineRawRatDivCode_mem_FP

theorem machineRoundedInflationFactorRawCode_mem_FP :
    machineRoundedInflationFactorRawCode ∈ FP := by
  have hinput := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawEllipsoidOne))
    machineRoundedInflationRawCode_mem_FP
  simpa only [machineRoundedInflationFactorRawCode] using!
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineRoundedInflationFactorEntryCode_mem_FP :
    machineRoundedInflationFactorEntryCode ∈ FP := by
  simpa only [machineRoundedInflationFactorEntryCode] using!
    machineCompose_mem_FP machineRoundedInflationFactorRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineScheduledRoundCenterCode_mem_FP :
    machineScheduledRoundCenterCode ∈ FP := by
  have hinput := machinePair_mem_FP machineScheduledRoundPrecision_mem_FP
    machineScheduledRoundCenter_mem_FP
  simpa only [machineScheduledRoundCenterCode] using!
    machineCompose_mem_FP hinput machineDyadicFloorVectorCode_mem_FP

theorem machineScheduledRoundFlooredBasisCode_mem_FP :
    machineScheduledRoundFlooredBasisCode ∈ FP := by
  have hinput := machinePair_mem_FP machineScheduledRoundPrecision_mem_FP
    machineScheduledRoundBasis_mem_FP
  simpa only [machineScheduledRoundFlooredBasisCode] using!
    machineCompose_mem_FP hinput machineDyadicFloorMatrixCode_mem_FP

theorem machineScheduledRoundInflationDiagonalCode_mem_FP :
    machineScheduledRoundInflationDiagonalCode ∈ FP := by
  have hfactor := machineCompose_mem_FP
    machineScheduledRoundDimensionBits_mem_FP
    machineRoundedInflationFactorEntryCode_mem_FP
  have hinput := machinePair_mem_FP
    machineScheduledRoundDimensionUnary_mem_FP hfactor
  simpa only [machineScheduledRoundInflationDiagonalCode] using!
    machineCompose_mem_FP hinput machineDiagonalBasisRowsCode_mem_FP

theorem machineScheduledRoundBasisCode_mem_FP :
    machineScheduledRoundBasisCode ∈ FP := by
  have hinput := machinePair_mem_FP
    machineScheduledRoundDimensionUnary_mem_FP
    (machinePair_mem_FP
      machineScheduledRoundInflationDiagonalCode_mem_FP
      machineScheduledRoundFlooredBasisCode_mem_FP)
  simpa only [machineScheduledRoundBasisCode] using!
    machineCompose_mem_FP hinput machineRationalMatrixMulCode_mem_FP

theorem machineScheduledRoundedEllipsoidCode_mem_FP :
    machineScheduledRoundedEllipsoidCode ∈ FP :=
  machinePair_mem_FP machineScheduledRoundDimensionBits_mem_FP
    (machinePair_mem_FP machineScheduledRoundCenterCode_mem_FP
      machineScheduledRoundBasisCode_mem_FP)

/-! ## Exact semantics -/

@[simp] theorem machineScheduledRoundDimensionUnary_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundDimensionUnary
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      List.replicate d true := by
  rw [machineScheduledRoundDimensionUnary]
  simp only [machineScheduledRoundState, machinePairSecond_pair,
    machineScheduledRoundDimensionBits,
    machineRationalEllipsoidDimensionWord_encode]
  exact machineBoundedUnary_encode_of_le
    (rationalEllipsoidStateBinaryCode E) d
    (rationalEllipsoid_dimension_le_state_code_length E)

@[simp] theorem machineRoundedInflationDimensionRawCode_encode (d : ℕ) :
    machineRoundedInflationDimensionRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidDimension d) := by
  exact machineEllipsoidDimensionRawCode_encode d

@[simp] theorem machineRoundedInflationDimensionSquareRawCode_encode
    (d : ℕ) :
    machineRoundedInflationDimensionSquareRawCode d.bits =
      rawRatBinaryCode (rawEllipsoidDimensionSquare d) := by
  rw [machineRoundedInflationDimensionSquareRawCode]
  simp only [machineRoundedInflationDimensionRawCode_encode,
    machineRawRatMulCode_encode, rawEllipsoidDimensionSquare]

@[simp] theorem machineRoundedInflationDimensionFourthRawCode_encode
    (d : ℕ) :
    machineRoundedInflationDimensionFourthRawCode d.bits =
      rawRatBinaryCode ((rawEllipsoidDimensionSquare d).mul
        (rawEllipsoidDimensionSquare d)) := by
  rw [machineRoundedInflationDimensionFourthRawCode]
  simp only [machineRoundedInflationDimensionSquareRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineRoundedInflationDenominatorRawCode_encode (d : ℕ) :
    machineRoundedInflationDenominatorRawCode d.bits =
      rawRatBinaryCode (rawRoundedInflationDenominator d) := by
  rw [machineRoundedInflationDenominatorRawCode]
  simp only [machineRoundedInflationDimensionFourthRawCode_encode,
    machineRawRatMulCode_encode, rawRoundedInflationDenominator]

@[simp] theorem machineRoundedInflationRawCode_encode (d : ℕ) :
    machineRoundedInflationRawCode d.bits =
      rawRatBinaryCode (rawRoundedInflation d) := by
  rw [machineRoundedInflationRawCode]
  simp only [machineRoundedInflationDenominatorRawCode_encode,
    machineRawRatDivCode_encode, rawRoundedInflation]

@[simp] theorem machineRoundedInflationFactorRawCode_encode (d : ℕ) :
    machineRoundedInflationFactorRawCode d.bits =
      rawRatBinaryCode (rawRoundedInflationFactor d) := by
  rw [machineRoundedInflationFactorRawCode]
  simp only [machineRoundedInflationRawCode_encode,
    machineRawRatAddCode_encode, rawRoundedInflationFactor]

@[simp] theorem machineRoundedInflationFactorEntryCode_encode (d : ℕ) :
    machineRoundedInflationFactorEntryCode d.bits =
      rationalEntryBinaryCode (1 + roundedEllipsoidInflation d) := by
  rw [machineRoundedInflationFactorEntryCode,
    machineRoundedInflationFactorRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    rawRoundedInflationFactor_value]

@[simp] theorem machineScheduledRoundCenterCode_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundCenterCode
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      rationalFiniteVectorCode (dyadicFloorVector p E.center) := by
  rw [machineScheduledRoundCenterCode]
  simp only [machineScheduledRoundPrecision, machinePairFirst_pair,
    machineScheduledRoundCenter, machineScheduledRoundState,
    machinePairSecond_pair, machineRationalEllipsoidCenterWord_encode]
  change machineDyadicFloorVectorCode
      (dyadicFloorVectorCanonicalWord p E.center) = _
  rw [machineDyadicFloorVectorCode_encode]

@[simp] theorem machineScheduledRoundFlooredBasisCode_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundFlooredBasisCode
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      rationalSquareMatrixRowsCode (dyadicFloorMatrix p E.basis) := by
  rw [machineScheduledRoundFlooredBasisCode]
  simp only [machineScheduledRoundPrecision, machinePairFirst_pair,
    machineScheduledRoundBasis, machineScheduledRoundState,
    machinePairSecond_pair, machineRationalEllipsoidBasisWord_encode]
  change machineDyadicFloorMatrixCode
      (dyadicFloorMatrixCanonicalWord p E.basis) = _
  rw [machineDyadicFloorMatrixCode_encode]

@[simp] theorem machineScheduledRoundInflationDiagonalCode_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundInflationDiagonalCode
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      rationalSquareMatrixRowsCode
        (rationalBallEllipsoid d 0
          (1 + roundedEllipsoidInflation d)).basis := by
  rw [machineScheduledRoundInflationDiagonalCode]
  simp only [machineScheduledRoundDimensionUnary_encode,
    machineScheduledRoundDimensionBits, machineScheduledRoundState,
    machinePairSecond_pair, machineRationalEllipsoidDimensionWord_encode,
    machineRoundedInflationFactorEntryCode_encode]
  exact machineDiagonalBasisRowsCode_encode d
    (1 + roundedEllipsoidInflation d)

theorem rationalMatrixMul_inflationDiagonal {d : ℕ}
    (s : ℚ) (A : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixMul (rationalBallEllipsoid d 0 s).basis A =
      fun i j ↦ s * A i j := by
  rw [rationalMatrixMul_eq_matrix_mul,
    rationalBallEllipsoid_basis]
  ext i j
  rw [Matrix.diagonal_mul]

@[simp] theorem machineScheduledRoundBasisCode_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundBasisCode
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      rationalSquareMatrixRowsCode
        (scheduledRoundedEllipsoid p E).basis := by
  rw [machineScheduledRoundBasisCode]
  simp only [machineScheduledRoundDimensionUnary_encode,
    machineScheduledRoundInflationDiagonalCode_encode,
    machineScheduledRoundFlooredBasisCode_encode]
  change machineRationalMatrixMulCode
      (rationalMatrixMulCanonicalWord
        (rationalBallEllipsoid d 0
          (1 + roundedEllipsoidInflation d)).basis
        (dyadicFloorMatrix p E.basis)) = _
  rw [machineRationalMatrixMulCode_encode,
    rationalMatrixMul_inflationDiagonal]
  rfl

@[simp] theorem machineScheduledRoundedEllipsoidCode_encode {d : ℕ}
    (p : ℕ) (E : RationalEllipsoidState d) :
    machineScheduledRoundedEllipsoidCode
        (pair (List.replicate p true)
          (rationalEllipsoidStateBinaryCode E)) =
      rationalEllipsoidStateBinaryCode
        (scheduledRoundedEllipsoid p E) := by
  rw [machineScheduledRoundedEllipsoidCode,
    machineScheduledRoundCenterCode_encode,
    machineScheduledRoundBasisCode_encode]
  simp [machineScheduledRoundDimensionBits,
    machineScheduledRoundState, machineRationalEllipsoidDimensionWord,
    rationalEllipsoidStateBinaryCode,
    scheduledRoundedEllipsoid]

/-! ## Exact central update followed by scheduled rounding -/

/-- Extract the precision ruler for a central ellipsoid update followed by rounding. -/
def machineScheduledCentralPrecision (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the paired ellipsoid state and cut used by the exact central update. -/
def machineScheduledCentralStateAndCut (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Perform the exact rational central ellipsoid update and then round at the supplied
precision. -/
def machineScheduledRoundedEllipsoidCentralUpdateCode
    (word : List Bool) : List Bool :=
  machineScheduledRoundedEllipsoidCode
    (pair (machineScheduledCentralPrecision word)
      (machineRationalEllipsoidCentralUpdateCode
        (machineScheduledCentralStateAndCut word)))

theorem machineScheduledCentralPrecision_mem_FP :
    machineScheduledCentralPrecision ∈ FP := machinePairFirst_mem_FP

theorem machineScheduledCentralStateAndCut_mem_FP :
    machineScheduledCentralStateAndCut ∈ FP := machinePairSecond_mem_FP

theorem machineScheduledRoundedEllipsoidCentralUpdateCode_mem_FP :
    machineScheduledRoundedEllipsoidCentralUpdateCode ∈ FP := by
  have hupdate := machineCompose_mem_FP
    machineScheduledCentralStateAndCut_mem_FP
    machineRationalEllipsoidCentralUpdateCode_mem_FP
  have hinput := machinePair_mem_FP machineScheduledCentralPrecision_mem_FP
    hupdate
  simpa only [machineScheduledRoundedEllipsoidCentralUpdateCode] using!
    machineCompose_mem_FP hinput machineScheduledRoundedEllipsoidCode_mem_FP

@[simp] theorem machineScheduledRoundedEllipsoidCentralUpdateCode_encode
    {d : ℕ} (p : ℕ) (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineScheduledRoundedEllipsoidCentralUpdateCode
        (pair (List.replicate p true)
          (pair (rationalEllipsoidStateBinaryCode E)
            (rationalFiniteVectorCode a))) =
      rationalEllipsoidStateBinaryCode
        (scheduledRoundedEllipsoidCentralUpdate p E a) := by
  rw [machineScheduledRoundedEllipsoidCentralUpdateCode]
  simp only [machineScheduledCentralPrecision, machinePairFirst_pair,
    machineScheduledCentralStateAndCut, machinePairSecond_pair,
    machineRationalEllipsoidCentralUpdateCode_encode]
  rw [machineScheduledRoundedEllipsoidCode_encode]
  rfl

end BeyondBethe
