/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryListInit
public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorCutVector
public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheHeightNormal
public import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedEpigraphNormal
public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheHeightCap
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidEncoding
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalPower
public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerInteriorScale
public import LeanPool.BeyondBethe.BeyondBethe.BetheEpigraphFeasibility

/-!
# A finite-word oracle for the bounded Bethe epigraph

The input contains the unary reduced dimension and precision, the rational
regularization parameter, floor and height cap, the input matrix, and a
rational ellipsoid state.  The machine performs the three oracle branches in
their mathematical order: an exact floor scan, the exact height-cap test, and
the directed nonlinear objective test.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Public input layout and accessors -/

/-- Input layout:
`pair mUnary (pair pUnary (pair tauRaw (pair deltaRaw
  (pair upperRaw (pair matrixCode ellipsoidCode)))))`. -/
def machineBetheOracleDimension (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extract the oracle input payload following the dimension word. -/
def machineBetheOracleRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extract the precision ruler from a Bethe oracle input word. -/
def machineBetheOraclePrecision (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheOracleRest word)

/-- Extract the oracle payload following the precision ruler. -/
def machineBetheOracleAfterPrecision (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheOracleRest word)

/-- Extract the encoded regularization parameter from a Bethe oracle input word. -/
def machineBetheOracleTau (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheOracleAfterPrecision word)

/-- Extract the oracle payload following the regularization parameter. -/
def machineBetheOracleAfterTau (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheOracleAfterPrecision word)

/-- Extract the encoded affine-coordinate floor from a Bethe oracle input word. -/
def machineBetheOracleDelta (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheOracleAfterTau word)

/-- Extract the oracle payload following the coordinate floor. -/
def machineBetheOracleAfterDelta (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheOracleAfterTau word)

/-- Extract the encoded epigraph height cap from a Bethe oracle input word. -/
def machineBetheOracleUpper (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheOracleAfterDelta word)

/-- Extract the matrix and ellipsoid payload following the height cap. -/
def machineBetheOracleAfterUpper (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheOracleAfterDelta word)

/-- Extract the encoded rational matrix from a Bethe oracle input word. -/
def machineBetheOracleMatrix (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheOracleAfterUpper word)

/-- Extract the encoded rational ellipsoid state from a Bethe oracle input word. -/
def machineBetheOracleEllipsoid (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheOracleAfterUpper word)

/-- Extract the encoded center vector of the oracle ellipsoid. -/
def machineBetheOracleCenter (word : List Bool) : List Bool :=
  machineRationalEllipsoidCenterWord (machineBetheOracleEllipsoid word)

/-- Remove the final epigraph-height coordinate from the encoded center vector. -/
def machineBetheOracleBase (word : List Bool) : List Bool :=
  machineBinaryListInit (machineBetheOracleCenter word)

theorem machineBetheOracleDimension_mem_FP :
    machineBetheOracleDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheOracleRest_mem_FP :
    machineBetheOracleRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheOraclePrecision_mem_FP :
    machineBetheOraclePrecision ∈ FP := by
  simpa only [machineBetheOraclePrecision] using!
    machineCompose_mem_FP machineBetheOracleRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheOracleAfterPrecision_mem_FP :
    machineBetheOracleAfterPrecision ∈ FP := by
  simpa only [machineBetheOracleAfterPrecision] using!
    machineCompose_mem_FP machineBetheOracleRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheOracleTau_mem_FP : machineBetheOracleTau ∈ FP := by
  simpa only [machineBetheOracleTau] using!
    machineCompose_mem_FP machineBetheOracleAfterPrecision_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheOracleAfterTau_mem_FP :
    machineBetheOracleAfterTau ∈ FP := by
  simpa only [machineBetheOracleAfterTau] using!
    machineCompose_mem_FP machineBetheOracleAfterPrecision_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheOracleDelta_mem_FP : machineBetheOracleDelta ∈ FP := by
  simpa only [machineBetheOracleDelta] using!
    machineCompose_mem_FP machineBetheOracleAfterTau_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheOracleAfterDelta_mem_FP :
    machineBetheOracleAfterDelta ∈ FP := by
  simpa only [machineBetheOracleAfterDelta] using!
    machineCompose_mem_FP machineBetheOracleAfterTau_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheOracleUpper_mem_FP : machineBetheOracleUpper ∈ FP := by
  simpa only [machineBetheOracleUpper] using!
    machineCompose_mem_FP machineBetheOracleAfterDelta_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheOracleAfterUpper_mem_FP :
    machineBetheOracleAfterUpper ∈ FP := by
  simpa only [machineBetheOracleAfterUpper] using!
    machineCompose_mem_FP machineBetheOracleAfterDelta_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheOracleMatrix_mem_FP : machineBetheOracleMatrix ∈ FP := by
  simpa only [machineBetheOracleMatrix] using!
    machineCompose_mem_FP machineBetheOracleAfterUpper_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheOracleEllipsoid_mem_FP :
    machineBetheOracleEllipsoid ∈ FP := by
  simpa only [machineBetheOracleEllipsoid] using!
    machineCompose_mem_FP machineBetheOracleAfterUpper_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheOracleCenter_mem_FP : machineBetheOracleCenter ∈ FP := by
  simpa only [machineBetheOracleCenter] using!
    machineCompose_mem_FP machineBetheOracleEllipsoid_mem_FP
      machineRationalEllipsoidCenterWord_mem_FP

theorem machineBetheOracleBase_mem_FP : machineBetheOracleBase ∈ FP := by
  simpa only [machineBetheOracleBase] using!
    machineCompose_mem_FP machineBetheOracleCenter_mem_FP
      machineBinaryListInit_mem_FP

/-! ## Derived dimension and the three branch tests -/

/-- Convert the oracle dimension ruler to binary. -/
def machineBetheOracleDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheOracleDimension word)

/-- Compute the squared dimension, the number of free affine coordinates, in binary. -/
def machineBetheOracleBaseDimensionBits (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineBetheOracleDimensionBits word)
      (machineBetheOracleDimensionBits word))

/-- Convert the free-coordinate count to a unary ruler bounded by the base-coordinate word. -/
def machineBetheOracleBaseDimensionUnary (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineBetheOracleBase word)
      (machineBetheOracleBaseDimensionBits word))

/-- Encode the number of free affine coordinates as a raw rational with denominator one. -/
def machineBetheOracleBaseDimensionRawCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode
    (machineBetheOracleBaseDimensionBits word)) [true]

/-- Package the dimension, floor, and center base coordinates for the floor-violation scan. -/
def machineBetheOracleFloorScanInput (word : List Bool) : List Bool :=
  pair (machineBetheOracleDimension word)
    (pair (machineBetheOracleDelta word) (machineBetheOracleBase word))

/-- Run the affine-coordinate floor scan on the oracle center. -/
def machineBetheOracleFloorScanResult (word : List Bool) : List Bool :=
  machineBetheFloorScanResultCode (machineBetheOracleFloorScanInput word)

/-- Extract the bit reporting whether the floor scan found a violation. -/
def machineBetheOracleFloorFoundBit (word : List Bool) : List Bool :=
  machineHeadBit (machinePairFirst (machineBetheOracleFloorScanResult word))

/-- Extract the reported row ruler from the floor-scan result. -/
def machineBetheOracleFloorRow (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineBetheOracleFloorScanResult word))

/-- Extract the reported column ruler from the floor-scan result. -/
def machineBetheOracleFloorColumn (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machineBetheOracleFloorScanResult word))

/-- Package the base dimension, height cap, and center for the height-cap test. -/
def machineBetheOracleHeightInput (word : List Bool) : List Bool :=
  pair (machineBetheOracleBaseDimensionUnary word)
    (pair (machineBetheOracleUpper word) (machineBetheOracleCenter word))

/-- Test whether the center epigraph height violates the prescribed cap. -/
def machineBetheOracleHeightViolationBit (word : List Bool) : List Bool :=
  machineBetheHeightCapViolationBit (machineBetheOracleHeightInput word)

/-- Extract the center epigraph height as a raw-rational code. -/
def machineBetheOracleHeightRawCode (word : List Bool) : List Bool :=
  machineBetheHeightCapEntryCode (machineBetheOracleHeightInput word)

/-- The raw-rational constant sixteen used in the oracle error margin. -/
def rawBetheOracleSixteen : RawRat := RawRat.ofNat 16

/-- Compute the raw-rational code of one half raised to the oracle precision. -/
def machineBetheOracleHalfPowerRawCode (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineBetheOraclePrecision word)
      (rawRatBinaryCode rawOptimizerHalf))

/-- Compute the raw-rational error scale `16 * (1/2)^p`. -/
def machineBetheOracleScaledErrorRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawBetheOracleSixteen)
      (machineBetheOracleHalfPowerRawCode word))

/-- Multiply the directed error scale by the number of free affine coordinates. -/
def machineBetheOracleMarginRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineBetheOracleScaledErrorRawCode word)
      (machineBetheOracleBaseDimensionRawCode word))

/-- Package dimension, precision, regularization, matrix, and base coordinates for objective
evaluation. -/
def machineBetheOracleObjectiveInput (word : List Bool) : List Bool :=
  pair (machineBetheOracleDimension word)
    (pair (machineBetheOraclePrecision word)
      (pair (machineBetheOracleTau word)
        (pair (machineBetheOracleMatrix word) (machineBetheOracleBase word))))

/-- Evaluate the directed lower negative-objective sum at the oracle center base coordinates. -/
def machineBetheOracleLowerRawCode (word : List Bool) : List Bool :=
  machineDirectedNegativeObjectiveSumRawCode
    (machineBetheOracleObjectiveInput word)

/-- Add the evaluation margin to the center epigraph height. -/
def machineBetheOracleHeightPlusMarginRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineBetheOracleHeightRawCode word)
      (machineBetheOracleMarginRawCode word))

/-- Detect when the directed lower objective exceeds the center height plus the evaluation
margin. -/
def machineBetheOracleNonlinearViolationBit
    (word : List Bool) : List Bool :=
  machineNotBit
    (machineRawRatLeBit
      (pair (machineBetheOracleLowerRawCode word)
        (machineBetheOracleHeightPlusMarginRawCode word)))

theorem machineBetheOracleDimensionBits_mem_FP :
    machineBetheOracleDimensionBits ∈ FP := by
  simpa only [machineBetheOracleDimensionBits] using!
    machineCompose_mem_FP machineBetheOracleDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheOracleBaseDimensionBits_mem_FP :
    machineBetheOracleBaseDimensionBits ∈ FP := by
  have hpair := machinePair_mem_FP machineBetheOracleDimensionBits_mem_FP
    machineBetheOracleDimensionBits_mem_FP
  simpa only [machineBetheOracleBaseDimensionBits] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineBetheOracleBaseDimensionUnary_mem_FP :
    machineBetheOracleBaseDimensionUnary ∈ FP := by
  have hpair := machinePair_mem_FP machineBetheOracleBase_mem_FP
    machineBetheOracleBaseDimensionBits_mem_FP
  simpa only [machineBetheOracleBaseDimensionUnary] using!
    machineCompose_mem_FP hpair machineBoundedUnary_mem_FP

theorem machineBetheOracleBaseDimensionRawCode_mem_FP :
    machineBetheOracleBaseDimensionRawCode ∈ FP := by
  have hnum := machineCompose_mem_FP
    machineBetheOracleBaseDimensionBits_mem_FP
    machineNaturalIntegerCode_mem_FP
  exact machinePair_mem_FP hnum (machineConst_mem_FP [true])

theorem machineBetheOracleFloorScanInput_mem_FP :
    machineBetheOracleFloorScanInput ∈ FP :=
  machinePair_mem_FP machineBetheOracleDimension_mem_FP
    (machinePair_mem_FP machineBetheOracleDelta_mem_FP
      machineBetheOracleBase_mem_FP)

theorem machineBetheOracleFloorScanResult_mem_FP :
    machineBetheOracleFloorScanResult ∈ FP := by
  simpa only [machineBetheOracleFloorScanResult] using!
    machineCompose_mem_FP machineBetheOracleFloorScanInput_mem_FP
      machineBetheFloorScanResultCode_mem_FP

theorem machineBetheOracleFloorFoundBit_mem_FP :
    machineBetheOracleFloorFoundBit ∈ FP := by
  have htag := machineCompose_mem_FP machineBetheOracleFloorScanResult_mem_FP
    machinePairFirst_mem_FP
  simpa only [machineBetheOracleFloorFoundBit] using!
    machineCompose_mem_FP htag machineHeadBit_mem_FP

theorem machineBetheOracleFloorRow_mem_FP :
    machineBetheOracleFloorRow ∈ FP := by
  have hpayload := machineCompose_mem_FP
    machineBetheOracleFloorScanResult_mem_FP machinePairSecond_mem_FP
  simpa only [machineBetheOracleFloorRow] using!
    machineCompose_mem_FP hpayload machinePairFirst_mem_FP

theorem machineBetheOracleFloorColumn_mem_FP :
    machineBetheOracleFloorColumn ∈ FP := by
  have hpayload := machineCompose_mem_FP
    machineBetheOracleFloorScanResult_mem_FP machinePairSecond_mem_FP
  simpa only [machineBetheOracleFloorColumn] using!
    machineCompose_mem_FP hpayload machinePairSecond_mem_FP

theorem machineBetheOracleHeightInput_mem_FP :
    machineBetheOracleHeightInput ∈ FP :=
  machinePair_mem_FP machineBetheOracleBaseDimensionUnary_mem_FP
    (machinePair_mem_FP machineBetheOracleUpper_mem_FP
      machineBetheOracleCenter_mem_FP)

theorem machineBetheOracleHeightViolationBit_mem_FP :
    machineBetheOracleHeightViolationBit ∈ FP := by
  simpa only [machineBetheOracleHeightViolationBit] using!
    machineCompose_mem_FP machineBetheOracleHeightInput_mem_FP
      machineBetheHeightCapViolationBit_mem_FP

theorem machineBetheOracleHeightRawCode_mem_FP :
    machineBetheOracleHeightRawCode ∈ FP := by
  simpa only [machineBetheOracleHeightRawCode] using!
    machineCompose_mem_FP machineBetheOracleHeightInput_mem_FP
      machineBetheHeightCapEntryCode_mem_FP

theorem machineBetheOracleHalfPowerRawCode_mem_FP :
    machineBetheOracleHalfPowerRawCode ∈ FP := by
  have hpair := machinePair_mem_FP machineBetheOraclePrecision_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawOptimizerHalf))
  simpa only [machineBetheOracleHalfPowerRawCode] using!
    machineCompose_mem_FP hpair machineRawRatPowerCode_mem_FP

theorem machineBetheOracleScaledErrorRawCode_mem_FP :
    machineBetheOracleScaledErrorRawCode ∈ FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode rawBetheOracleSixteen))
    machineBetheOracleHalfPowerRawCode_mem_FP
  simpa only [machineBetheOracleScaledErrorRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineBetheOracleMarginRawCode_mem_FP :
    machineBetheOracleMarginRawCode ∈ FP := by
  have hpair := machinePair_mem_FP
    machineBetheOracleScaledErrorRawCode_mem_FP
    machineBetheOracleBaseDimensionRawCode_mem_FP
  simpa only [machineBetheOracleMarginRawCode] using!
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineBetheOracleObjectiveInput_mem_FP :
    machineBetheOracleObjectiveInput ∈ FP :=
  machinePair_mem_FP machineBetheOracleDimension_mem_FP
    (machinePair_mem_FP machineBetheOraclePrecision_mem_FP
      (machinePair_mem_FP machineBetheOracleTau_mem_FP
        (machinePair_mem_FP machineBetheOracleMatrix_mem_FP
          machineBetheOracleBase_mem_FP)))

theorem machineBetheOracleLowerRawCode_mem_FP :
    machineBetheOracleLowerRawCode ∈ FP := by
  simpa only [machineBetheOracleLowerRawCode] using!
    machineCompose_mem_FP machineBetheOracleObjectiveInput_mem_FP
      machineDirectedNegativeObjectiveSumRawCode_mem_FP

theorem machineBetheOracleHeightPlusMarginRawCode_mem_FP :
    machineBetheOracleHeightPlusMarginRawCode ∈ FP := by
  have hpair := machinePair_mem_FP machineBetheOracleHeightRawCode_mem_FP
    machineBetheOracleMarginRawCode_mem_FP
  simpa only [machineBetheOracleHeightPlusMarginRawCode] using!
    machineCompose_mem_FP hpair machineRawRatAddCode_mem_FP

theorem machineBetheOracleNonlinearViolationBit_mem_FP :
    machineBetheOracleNonlinearViolationBit ∈ FP := by
  have hpair := machinePair_mem_FP machineBetheOracleLowerRawCode_mem_FP
    machineBetheOracleHeightPlusMarginRawCode_mem_FP
  have hle := machineCompose_mem_FP hpair machineRawRatLeBit_mem_FP
  simpa only [machineBetheOracleNonlinearViolationBit] using!
    machineNotBit_mem_FP hle

/-! ## Cut construction and final response -/

/-- Package the dimension and violating entry indices for a floor-cut normal. -/
def machineBetheOracleFloorNormalInput (word : List Bool) : List Bool :=
  pair (machineBetheOracleDimension word)
    (pair (machineBetheOracleFloorRow word)
      (machineBetheOracleFloorColumn word))

/-- Encode a cutting response with the normal for the detected floor violation. -/
def machineBetheOracleFloorResponse (word : List Bool) : List Bool :=
  pair [true]
    (machineBetheFloorCutVectorCode (machineBetheOracleFloorNormalInput word))

/-- Encode a cutting response with the epigraph height-cap normal. -/
def machineBetheOracleHeightResponse (word : List Bool) : List Bool :=
  pair [true]
    (machineBetheHeightNormalVectorCode (machineBetheOracleDimension word))

/-- Encode a cutting response with the directed nonlinear epigraph normal. -/
def machineBetheOracleNonlinearResponse (word : List Bool) : List Bool :=
  pair [true]
    (machineDirectedEpigraphNormalVectorCode
      (machineBetheOracleObjectiveInput word))

/-- The encoded acceptance response, carrying no cut vector. -/
def machineBetheOracleAcceptResponse (_word : List Bool) : List Bool :=
  pair [false] []

/-- Choose the floor, height-cap, or nonlinear cut in that order, accepting when none is
required. -/
def machineBetheEpigraphOracleResponseCode (word : List Bool) : List Bool :=
  machineIfHead (machineBetheOracleFloorFoundBit word)
    (machineBetheOracleFloorResponse word)
    (machineIfHead (machineBetheOracleHeightViolationBit word)
      (machineBetheOracleHeightResponse word)
      (machineIfHead (machineBetheOracleNonlinearViolationBit word)
        (machineBetheOracleNonlinearResponse word)
        (machineBetheOracleAcceptResponse word)))

theorem machineBetheOracleFloorNormalInput_mem_FP :
    machineBetheOracleFloorNormalInput ∈ FP :=
  machinePair_mem_FP machineBetheOracleDimension_mem_FP
    (machinePair_mem_FP machineBetheOracleFloorRow_mem_FP
      machineBetheOracleFloorColumn_mem_FP)

theorem machineBetheOracleFloorResponse_mem_FP :
    machineBetheOracleFloorResponse ∈ FP := by
  have hnormal := machineCompose_mem_FP
    machineBetheOracleFloorNormalInput_mem_FP
    machineBetheFloorCutVectorCode_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true]) hnormal

theorem machineBetheOracleHeightResponse_mem_FP :
    machineBetheOracleHeightResponse ∈ FP := by
  have hnormal := machineCompose_mem_FP machineBetheOracleDimension_mem_FP
    machineBetheHeightNormalVectorCode_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true]) hnormal

theorem machineBetheOracleNonlinearResponse_mem_FP :
    machineBetheOracleNonlinearResponse ∈ FP := by
  have hnormal := machineCompose_mem_FP machineBetheOracleObjectiveInput_mem_FP
    machineDirectedEpigraphNormalVectorCode_mem_FP
  exact machinePair_mem_FP (machineConst_mem_FP [true]) hnormal

theorem machineBetheOracleAcceptResponse_mem_FP :
    machineBetheOracleAcceptResponse ∈ FP :=
  machineConst_mem_FP (pair [false] [])

theorem machineBetheEpigraphOracleResponseCode_mem_FP :
    machineBetheEpigraphOracleResponseCode ∈ FP := by
  have hnonlinear := machineIfHead_mem_FP
    machineBetheOracleNonlinearViolationBit_mem_FP
    machineBetheOracleNonlinearResponse_mem_FP
    machineBetheOracleAcceptResponse_mem_FP
  have hheight := machineIfHead_mem_FP
    machineBetheOracleHeightViolationBit_mem_FP
    machineBetheOracleHeightResponse_mem_FP hnonlinear
  simpa only [machineBetheEpigraphOracleResponseCode] using!
    machineIfHead_mem_FP machineBetheOracleFloorFoundBit_mem_FP
      machineBetheOracleFloorResponse_mem_FP hheight

/-! ## Canonical semantics -/

/-- The canonical Bethe oracle input word containing its scalar parameters, matrix, and
ellipsoid state. -/
def machineBetheOracleCanonicalWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate p true)
      (pair (rawRatBinaryCode (rawRatOfRat tau))
        (pair (rawRatBinaryCode delta)
          (pair (rawRatBinaryCode upper)
            (pair (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩)
              (rationalEllipsoidStateBinaryCode E))))))

theorem ofFn_epigraph_center_split {d : ℕ}
    (q : Fin (d + 1) → ℚ) :
    List.ofFn q = List.ofFn (epigraphBase q) ++ [epigraphHeight q] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 2

@[simp] theorem machineBetheOracleDimension_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleDimension
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      List.replicate m true := by
  simp [machineBetheOracleDimension, machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOraclePrecision_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOraclePrecision
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      List.replicate p true := by
  simp [machineBetheOraclePrecision, machineBetheOracleRest,
    machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleTau_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleTau
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode (rawRatOfRat tau) := by
  simp [machineBetheOracleTau, machineBetheOracleAfterPrecision,
    machineBetheOracleRest, machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleDelta_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleDelta
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode delta := by
  simp [machineBetheOracleDelta, machineBetheOracleAfterTau,
    machineBetheOracleAfterPrecision, machineBetheOracleRest,
    machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleUpper_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleUpper
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode upper := by
  simp [machineBetheOracleUpper, machineBetheOracleAfterDelta,
    machineBetheOracleAfterTau, machineBetheOracleAfterPrecision,
    machineBetheOracleRest, machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleMatrix_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleMatrix
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩ := by
  simp [machineBetheOracleMatrix, machineBetheOracleAfterUpper,
    machineBetheOracleAfterDelta, machineBetheOracleAfterTau,
    machineBetheOracleAfterPrecision, machineBetheOracleRest,
    machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleEllipsoid_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleEllipsoid
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalEllipsoidStateBinaryCode E := by
  simp [machineBetheOracleEllipsoid, machineBetheOracleAfterUpper,
    machineBetheOracleAfterDelta, machineBetheOracleAfterTau,
    machineBetheOracleAfterPrecision, machineBetheOracleRest,
    machineBetheOracleCanonicalWord]

@[simp] theorem machineBetheOracleCenter_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleCenter
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalFiniteVectorCode E.center := by
  rw [machineBetheOracleCenter, machineBetheOracleEllipsoid_encode,
    machineRationalEllipsoidCenterWord_encode]

@[simp] theorem machineBetheOracleBase_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleBase
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalFiniteVectorCode (epigraphBase E.center) := by
  rw [machineBetheOracleBase, machineBetheOracleCenter_encode,
    rationalFiniteVectorCode, ofFn_epigraph_center_split,
    machineBinaryListInit_encode]
  rfl

@[simp] theorem machineBetheOracleBaseDimensionBits_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleBaseDimensionBits
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      (m * m).bits := by
  rw [machineBetheOracleBaseDimensionBits,
    machineBetheOracleDimensionBits, machineBetheOracleDimension_encode,
    machineLengthBits_encode, List.length_replicate,
    machineBinaryMulBits_pair_natBits]

theorem betheOracle_baseDimension_le_baseCodeLength {m : ℕ}
    (q : Fin (m * m) → ℚ) :
    m * m ≤ (rationalFiniteVectorCode q).length := by
  simpa only [rationalFiniteVectorCode, List.length_ofFn] using!
    binaryListCode_listLength_le rationalEntryBinaryCode (List.ofFn q)

@[simp] theorem machineBetheOracleBaseDimensionUnary_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleBaseDimensionUnary
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      List.replicate (m * m) true := by
  rw [machineBetheOracleBaseDimensionUnary,
    machineBetheOracleBase_encode,
    machineBetheOracleBaseDimensionBits_encode]
  exact machineBoundedUnary_encode_of_le _ _
    (betheOracle_baseDimension_le_baseCodeLength (epigraphBase E.center))

@[simp] theorem machineBetheOracleBaseDimensionRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleBaseDimensionRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode (RawRat.ofNat (m * m)) := by
  rw [machineBetheOracleBaseDimensionRawCode,
    machineBetheOracleBaseDimensionBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [rawRatBinaryCode, RawRat.ofNat]

@[simp] theorem machineBetheOracleFloorScanInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorScanInput
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      machineBetheFloorScanCanonicalWord delta (epigraphBase E.center) := by
  simp [machineBetheOracleFloorScanInput,
    machineBetheFloorScanCanonicalWord]

@[simp] theorem machineBetheOracleFloorScanResult_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorScanResult
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      betheFloorScanSemanticResultCode
        (finalBetheFloorScanSemanticState delta (epigraphBase E.center)) := by
  rw [machineBetheOracleFloorScanResult,
    machineBetheOracleFloorScanInput_encode,
    machineBetheFloorScanResultCode_encode]

@[simp] theorem machineBetheOracleFloorFoundBit_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorFoundBit
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      [(finalBetheFloorScanSemanticState delta
          (epigraphBase E.center)).found] := by
  rw [machineBetheOracleFloorFoundBit,
    machineBetheOracleFloorScanResult_encode]
  simp [betheFloorScanSemanticResultCode]

@[simp] theorem machineBetheOracleFloorRow_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorRow
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      List.replicate
        (finalBetheFloorScanSemanticState delta
          (epigraphBase E.center)).row.1 true := by
  rw [machineBetheOracleFloorRow,
    machineBetheOracleFloorScanResult_encode]
  simp [betheFloorScanSemanticResultCode]

@[simp] theorem machineBetheOracleFloorColumn_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorColumn
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      List.replicate
        (finalBetheFloorScanSemanticState delta
          (epigraphBase E.center)).column.1 true := by
  rw [machineBetheOracleFloorColumn,
    machineBetheOracleFloorScanResult_encode]
  simp [betheFloorScanSemanticResultCode]

@[simp] theorem machineBetheOracleHeightInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHeightInput
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      machineBetheHeightCapCanonicalWord upper E.center := by
  simp [machineBetheOracleHeightInput,
    machineBetheHeightCapCanonicalWord]

@[simp] theorem machineBetheOracleHeightViolationBit_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHeightViolationBit
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      [decide (upper.value < epigraphHeight E.center)] := by
  rw [machineBetheOracleHeightViolationBit,
    machineBetheOracleHeightInput_encode,
    machineBetheHeightCapViolationBit_encode]
  rfl

@[simp] theorem machineBetheOracleHeightRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHeightRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode (rawRatOfRat (epigraphHeight E.center)) := by
  rw [machineBetheOracleHeightRawCode,
    machineBetheOracleHeightInput_encode,
    machineBetheHeightCapEntryCode_encode]
  rfl

/-- The raw-rational oracle margin `16 * (1/2)^p * m^2`. -/
def rawBetheOracleMargin (m p : ℕ) : RawRat :=
  (rawBetheOracleSixteen.mul (rawOptimizerHalf.pow p)).mul
    (RawRat.ofNat (m * m))

@[simp] theorem machineBetheOracleHalfPowerRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHalfPowerRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode (rawOptimizerHalf.pow p) := by
  rw [machineBetheOracleHalfPowerRawCode,
    machineBetheOraclePrecision_encode,
    machineRawRatPowerCode_encode]

@[simp] theorem machineBetheOracleScaledErrorRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleScaledErrorRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode
        (rawBetheOracleSixteen.mul (rawOptimizerHalf.pow p)) := by
  rw [machineBetheOracleScaledErrorRawCode,
    machineBetheOracleHalfPowerRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineBetheOracleMarginRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleMarginRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode (rawBetheOracleMargin m p) := by
  rw [machineBetheOracleMarginRawCode,
    machineBetheOracleScaledErrorRawCode_encode,
    machineBetheOracleBaseDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem rawBetheOracleMargin_value (m p : ℕ) :
    (rawBetheOracleMargin m p).value =
      16 * (1 / 2 : ℚ) ^ p * (m * m) := by
  simp [rawBetheOracleMargin, rawBetheOracleSixteen,
    RawRat.value_mul, RawRat.value_pow, rawOptimizerHalf_value]

@[simp] theorem machineBetheOracleObjectiveInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleObjectiveInput
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      machineDirectedObjectiveSumCanonicalWord tau A
        (epigraphBase E.center) p := by
  simp [machineBetheOracleObjectiveInput,
    machineDirectedObjectiveSumCanonicalWord]

@[simp] theorem machineBetheOracleLowerRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleLowerRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode
        (rawDirectedNegativeObjectiveSum tau A (epigraphBase E.center) p) := by
  rw [machineBetheOracleLowerRawCode,
    machineBetheOracleObjectiveInput_encode,
    machineDirectedNegativeObjectiveSumRawCode_encode]

@[simp] theorem machineBetheOracleHeightPlusMarginRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHeightPlusMarginRawCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rawRatBinaryCode
        ((rawRatOfRat (epigraphHeight E.center)).add
          (rawBetheOracleMargin m p)) := by
  rw [machineBetheOracleHeightPlusMarginRawCode,
    machineBetheOracleHeightRawCode_encode,
    machineBetheOracleMarginRawCode_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineBetheOracleNonlinearViolationBit_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleNonlinearViolationBit
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      [decide
        (epigraphHeight E.center +
            16 * (1 / 2 : ℚ) ^ p * (m * m) <
          directedNegativeObjectiveLower tau A
            (betheAffineMatrixQ (epigraphBase E.center)) p)] := by
  rw [machineBetheOracleNonlinearViolationBit,
    machineBetheOracleLowerRawCode_encode,
    machineBetheOracleHeightPlusMarginRawCode_encode,
    machineRawRatLeBit_encode, machineNotBit_one]
  rw [rawDirectedNegativeObjectiveSum_value, RawRat.value_add,
    rawRatOfRat_value, rawBetheOracleMargin_value]
  rw [← decide_not]
  simp only [not_le]

@[simp] theorem machineBetheOracleFloorNormalInput_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorNormalInput
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      machineBetheFloorCutVectorCanonicalWord
        (finalBetheFloorScanSemanticState delta
          (epigraphBase E.center)).row
        (finalBetheFloorScanSemanticState delta
          (epigraphBase E.center)).column := by
  simp [machineBetheOracleFloorNormalInput,
    machineBetheFloorCutVectorCanonicalWord]

@[simp] theorem machineBetheOracleFloorResponse_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleFloorResponse
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalCentralOracleResponseBinaryCode
        (.cut (betheFloorCutNormal
          (finalBetheFloorScanSemanticState delta
            (epigraphBase E.center)).row
          (finalBetheFloorScanSemanticState delta
            (epigraphBase E.center)).column)) := by
  rw [machineBetheOracleFloorResponse,
    machineBetheOracleFloorNormalInput_encode,
    machineBetheFloorCutVectorCode_encode_oracleNormal]
  rfl

@[simp] theorem machineBetheOracleHeightResponse_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleHeightResponse
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalCentralOracleResponseBinaryCode
        (.cut (epigraphUpperNormal (m * m))) := by
  rw [machineBetheOracleHeightResponse,
    machineBetheOracleDimension_encode,
    machineBetheHeightNormalVectorCode_encode]
  rfl

@[simp] theorem machineBetheOracleNonlinearResponse_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleNonlinearResponse
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalCentralOracleResponseBinaryCode
        (.cut (epigraphNormal
          ((betheDirectedEpigraphData tau A p).gradient
            (epigraphBase E.center)))) := by
  rw [machineBetheOracleNonlinearResponse,
    machineBetheOracleObjectiveInput_encode,
    machineDirectedEpigraphNormalVectorCode_encode_oracleNormal]
  rfl

@[simp] theorem machineBetheOracleAcceptResponse_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheOracleAcceptResponse
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalCentralOracleResponseBinaryCode
        (RationalCentralOracleResponse.accept :
          RationalCentralOracleResponse (m * m + 1)) := by
  rfl

/-- Semantic oracle implemented by the row-major machine scan.  The scan
state is exposed here only to state the exact program-correctness theorem;
the validity proof below uses its established first-violation invariant. -/
def scannedBetheBoundedEpigraphOracle {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat) :
    RationalCentralOracle (m * m + 1) :=
  fun E ↦
    let state := finalBetheFloorScanSemanticState delta
      (epigraphBase E.center)
    if state.found then
      .cut (betheFloorCutNormal state.row state.column)
    else if upper.value < epigraphHeight E.center then
      .cut (epigraphUpperNormal (m * m))
    else
      directedEpigraphOracle
        (betheDirectedEpigraphData tau A p)
        (16 * (1 / 2 : ℚ) ^ p) (m * m) E

@[simp] theorem machineBetheEpigraphOracleResponseCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat)
    (E : RationalEllipsoidState (m * m + 1)) :
    machineBetheEpigraphOracleResponseCode
        (machineBetheOracleCanonicalWord tau A p delta upper E) =
      rationalCentralOracleResponseBinaryCode
        (scannedBetheBoundedEpigraphOracle tau A p delta upper E) := by
  let state := finalBetheFloorScanSemanticState delta
    (epigraphBase E.center)
  rw [machineBetheEpigraphOracleResponseCode,
    machineBetheOracleFloorFoundBit_encode]
  change machineIfHead [state.found]
      (machineBetheOracleFloorResponse
        (machineBetheOracleCanonicalWord tau A p delta upper E))
      _ = _
  cases hfound : state.found
  · rw [machineIfHead_false]
    by_cases hheight : upper.value < epigraphHeight E.center
    · rw [machineBetheOracleHeightViolationBit_encode]
      simp only [hheight, decide_true, machineIfHead_true]
      rw [machineBetheOracleHeightResponse_encode]
      simp [scannedBetheBoundedEpigraphOracle, state, hfound, hheight]
    · rw [machineBetheOracleHeightViolationBit_encode]
      simp only [hheight, decide_false, machineIfHead_false]
      by_cases hnonlinear : epigraphHeight E.center +
          16 * (1 / 2 : ℚ) ^ p * (m * m) <
        directedNegativeObjectiveLower tau A
          (betheAffineMatrixQ (epigraphBase E.center)) p
      · rw [machineBetheOracleNonlinearViolationBit_encode]
        simp only [hnonlinear, decide_true, machineIfHead_true]
        rw [machineBetheOracleNonlinearResponse_encode]
        have hnonlinear' : epigraphHeight E.center +
            16 * (2 ^ p : ℚ)⁻¹ * (m * m) <
          directedNegativeObjectiveLower tau A
            (betheAffineMatrixQ (epigraphBase E.center)) p := by
          simpa [one_div, div_pow] using! hnonlinear
        simp [scannedBetheBoundedEpigraphOracle, state, hfound, hheight,
          directedEpigraphOracle, betheDirectedEpigraphData, hnonlinear']
      · rw [machineBetheOracleNonlinearViolationBit_encode]
        simp only [hnonlinear, decide_false, machineIfHead_false]
        rw [machineBetheOracleAcceptResponse_encode]
        have hnonlinear' : ¬(epigraphHeight E.center +
            16 * (2 ^ p : ℚ)⁻¹ * (m * m) <
          directedNegativeObjectiveLower tau A
            (betheAffineMatrixQ (epigraphBase E.center)) p) := by
          simpa [one_div, div_pow] using! hnonlinear
        simp [scannedBetheBoundedEpigraphOracle, state, hfound, hheight,
          directedEpigraphOracle, betheDirectedEpigraphData, hnonlinear']
  · rw [machineIfHead_true,
      machineBetheOracleFloorResponse_encode]
    simp [scannedBetheBoundedEpigraphOracle, state, hfound]

/-! ## Mathematical validity of the implemented scan oracle -/

theorem scannedBetheBoundedEpigraphOracle_valid {m : ℕ} (hm : 0 < m)
    {tau : ℚ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) (hA : ∀ i j, 0 < A i j)
    {delta : RawRat} (hdelta : 0 < delta.value)
    (p : ℕ) (upper : RawRat) :
    RationalCentralOracleValid
      (BetheEpigraphTarget (tau : ℝ) (fun i j ↦ (A i j : ℝ))
        (delta.value : ℝ) (upper.value : ℝ))
      (scannedBetheBoundedEpigraphOracle tau A p delta upper) := by
  intro E a hresponse
  rw [scannedBetheBoundedEpigraphOracle] at hresponse
  split at hresponse <;> rename_i hfloor
  · let state := finalBetheFloorScanSemanticState delta
      (epigraphBase E.center)
    have hfloor' : state.found = true := by simpa only [state] using! hfloor
    cases hresponse
    refine ⟨betheFloorCutNormal_ne_zero hm state.row state.column, ?_⟩
    intro z hz
    have hbelow : betheAffineMatrixQ (epigraphBase E.center)
        state.row state.column < delta.value := by
      exact finalBetheFloorScanSemanticState_found_is_below
        delta (epigraphBase E.center) hfloor'
    have htargetFloor : (delta.value : ℝ) ≤
        birkhoffAffineMap (vectorToSquareMatrix (epigraphBase z))
          state.row state.column := by
      simpa only [BetheEpigraphTarget] using! hz.1 state.row state.column
    have hcut := betheFloorCut_valid hbelow htargetFloor
    rw [finiteDot, Fin.sum_univ_castSucc] at hcut ⊢
    simpa [rationalCenterReal, epigraphBase] using! hcut.le
  · split at hresponse <;> rename_i hheight
    · cases hresponse
      refine ⟨epigraphUpperNormal_ne_zero (m * m), ?_⟩
      intro z hz
      have hdot := epigraphUpperNormal_dot_displacement z E.center
      rw [show finiteDot
          (fun i ↦ (epigraphUpperNormal (m * m) i : ℝ))
          (fun i ↦ z i - rationalCenterReal E i) =
          epigraphHeight z - (epigraphHeight E.center : ℚ) by
        simpa only [rationalCenterReal] using! hdot]
      have hzUpper : epigraphHeight z ≤ (upper.value : ℝ) := by
        simpa only [BetheEpigraphTarget] using! hz.2.2
      have hheightReal : (upper.value : ℝ) <
          ((epigraphHeight E.center : ℚ) : ℝ) := by
        exact_mod_cast hheight
      linarith
    · have hqueryFloor : ∀ i j, delta.value ≤
          betheAffineMatrixQ (epigraphBase E.center) i j := by
        apply finalBetheFloorScanSemanticState_notFound_all_above
        simpa using! hfloor
      refine ⟨directedEpigraphOracle_cut_ne_zero
        (betheDirectedEpigraphData tau A p)
        (16 * (1 / 2 : ℚ) ^ p) (m * m) E hresponse, ?_⟩
      intro z hz
      exact (betheDirectedEpigraphOracle_cut_valid hm htau0 htau1 hA
        hdelta (upper := (upper.value : ℝ)) p E hqueryFloor
        hresponse hz).2.le

theorem scannedBetheBoundedEpigraphOracle_acceptsOnly {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta upper : RawRat) :
    RationalCentralOracleAcceptsOnly
      (BetheEpigraphOracleAccepted tau A p delta.value upper.value)
      (scannedBetheBoundedEpigraphOracle tau A p delta upper) := by
  intro E hresponse
  rw [scannedBetheBoundedEpigraphOracle] at hresponse
  split at hresponse <;> rename_i hfloor
  · contradiction
  · split at hresponse <;> rename_i hheight
    · contradiction
    · rw [directedEpigraphOracle] at hresponse
      split at hresponse <;> rename_i hnonlinear
      · contradiction
      · cases hresponse
        refine ⟨?_, not_lt.mp hheight, ?_⟩
        · apply finalBetheFloorScanSemanticState_notFound_all_above
          simpa using! hfloor
        · exact not_lt.mp hnonlinear

end BeyondBethe
