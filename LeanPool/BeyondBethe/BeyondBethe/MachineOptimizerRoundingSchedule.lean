/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerFeasibilitySchedule
import LeanPool.BeyondBethe.BeyondBethe.MachineNaturalCombinators
import LeanPool.BeyondBethe.BeyondBethe.ExplicitBetheThresholdFeasibility

/-! # Machine Optimizer Rounding Schedule -/

namespace BeyondBethe

open Complexity

/-!
# Finite-word rounding precision for Bethe feasibility

The precision is the explicit zero-ball schedule proved in
`ExplicitScheduledFeasibility`.  Its inputs are the exact ellipsoid dimension,
the exact iteration budget, and canonical bit lengths of the outer radius and
of the initial state-magnitude bound.
-/

def rawOptimizerFeasibilityInitialMagnitude
    (d : ℕ) (R : RawRat) : RawRat :=
  rawOptimizerTwo.add ((RawRat.ofNat d).mul R)

def machineOptimizerFeasibilityInitialMagnitudeRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineRawRatMulCode
        (pair (machineOptimizerFeasibilityEllipsoidDimensionRawCode word)
          (machineOptimizerFeasibilityOuterRadiusRawCode word))))

def machineOptimizerFeasibilityInitialMagnitudeEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerFeasibilityInitialMagnitudeRawCode word)

def machineOptimizerFeasibilityInitialMagnitudeLengthRuler
    (word : List Bool) : List Bool :=
  machineOptimizerEntryLengthRuler
    (machineOptimizerFeasibilityInitialMagnitudeEntryCode word)

def machineOptimizerFeasibilityKBits (word : List Bool) : List Bool :=
  machineLengthBits
    (machineOptimizerFeasibilityInitialMagnitudeLengthRuler word)

def machineOptimizerFeasibilityLBits (word : List Bool) : List Bool :=
  machineBinaryMulOf machineOptimizerFeasibilityOuterLengthBits
    machineOptimizerFeasibilityDBits word

def machineOptimizerFeasibilityTwoTBits (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 2)
    machineOptimizerFeasibilityBudgetBits word

def machineOptimizerFeasibilityFirstBaseBits (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityLBits
    machineOptimizerFeasibilityTwoTBits word

def machineOptimizerFeasibilityFirstBits (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityFirstBaseBits
    (machineBinaryConst 1) word

def machineOptimizerFeasibilityThreeDBits (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 3)
    machineOptimizerFeasibilityDBits word

def machineOptimizerFeasibilitySixPlusThreeDBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf (machineBinaryConst 6)
    machineOptimizerFeasibilityThreeDBits word

def machineOptimizerFeasibilityTTimesGrowthBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf machineOptimizerFeasibilityBudgetBits
    machineOptimizerFeasibilitySixPlusThreeDBits word

def machineOptimizerFeasibilityKPlusGrowthBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityKBits
    machineOptimizerFeasibilityTTimesGrowthBits word

def machineOptimizerFeasibilityKPlusGrowthPlusThreeBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityKPlusGrowthBits
    (machineBinaryConst 3) word

def machineOptimizerFeasibilityInnerMagnitudeBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityKPlusGrowthPlusThreeBits
    machineOptimizerFeasibilityDBits word

def machineOptimizerFeasibilityDInnerMagnitudeBits
    (word : List Bool) : List Bool :=
  machineBinaryMulOf machineOptimizerFeasibilityDBits
    machineOptimizerFeasibilityInnerMagnitudeBits word

def machineOptimizerFeasibilityEightDBits (word : List Bool) : List Bool :=
  machineBinaryMulOf (machineBinaryConst 8)
    machineOptimizerFeasibilityDBits word

def machineOptimizerFeasibilityDenomFirstBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf (machineBinaryConst 12)
    machineOptimizerFeasibilityEightDBits word

def machineOptimizerFeasibilityDenomSecondBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityDenomFirstBits
    machineOptimizerFeasibilityDSquareBits word

def machineOptimizerFeasibilityDenominatorExponentBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityDenomSecondBits
    machineOptimizerFeasibilityDInnerMagnitudeBits word

def machineOptimizerFeasibilityPrecisionBaseBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityFirstBits
    machineOptimizerFeasibilityDenominatorExponentBits word

def machineOptimizerFeasibilityRoundingPrecisionBits
    (word : List Bool) : List Bool :=
  machineBinaryAddOf machineOptimizerFeasibilityPrecisionBaseBits
    (machineBinaryConst 2) word

def machineOptimizerFeasibilityRoundingGuardSource
    (word : List Bool) : List Bool :=
  machineOptimizerFeasibilityBudgetUnary word ++
    (machineOptimizerFeasibilityEllipsoidDimensionUnary word ++
      (machineOptimizerFeasibilityInitialMagnitudeLengthRuler word ++
        machineOptimizerFeasibilityOuterRadiusLengthRuler word))

def machineOptimizerFeasibilityRoundingGuard
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2
    (machineOptimizerFeasibilityRoundingGuardSource word)

def machineOptimizerFeasibilityRoundingPrecisionUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerFeasibilityRoundingGuard word)
      (machineOptimizerFeasibilityRoundingPrecisionBits word))

/-! ## Polynomial-time closure -/

theorem machineOptimizerFeasibilityInitialMagnitudeRawCode_mem_FP :
    machineOptimizerFeasibilityInitialMagnitudeRawCode ∈ FP := by
  have hproduct := machineCompose_mem_FP
    (machinePair_mem_FP
      machineOptimizerFeasibilityEllipsoidDimensionRawCode_mem_FP
      machineOptimizerFeasibilityOuterRadiusRawCode_mem_FP)
    machineRawRatMulCode_mem_FP
  simpa only [machineOptimizerFeasibilityInitialMagnitudeRawCode] using
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo)) hproduct)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerFeasibilityInitialMagnitudeEntryCode_mem_FP :
    machineOptimizerFeasibilityInitialMagnitudeEntryCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityInitialMagnitudeEntryCode] using
    machineCompose_mem_FP
      machineOptimizerFeasibilityInitialMagnitudeRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerFeasibilityInitialMagnitudeLengthRuler_mem_FP :
    machineOptimizerFeasibilityInitialMagnitudeLengthRuler ∈ FP := by
  simpa only [machineOptimizerFeasibilityInitialMagnitudeLengthRuler] using
    machineCompose_mem_FP
      machineOptimizerFeasibilityInitialMagnitudeEntryCode_mem_FP
      machineOptimizerEntryLengthRuler_mem_FP

theorem machineOptimizerFeasibilityKBits_mem_FP :
    machineOptimizerFeasibilityKBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityKBits] using
    machineCompose_mem_FP
      machineOptimizerFeasibilityInitialMagnitudeLengthRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineOptimizerFeasibilityLBits_mem_FP :
    machineOptimizerFeasibilityLBits ∈ FP :=
  machineBinaryMulOf_mem_FP
    machineOptimizerFeasibilityOuterLengthBits_mem_FP
    machineOptimizerFeasibilityDBits_mem_FP

theorem machineOptimizerFeasibilityTwoTBits_mem_FP :
    machineOptimizerFeasibilityTwoTBits ∈ FP :=
  machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 2)
    machineOptimizerFeasibilityBudgetBits_mem_FP

theorem machineOptimizerFeasibilityFirstBaseBits_mem_FP :
    machineOptimizerFeasibilityFirstBaseBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityLBits_mem_FP
    machineOptimizerFeasibilityTwoTBits_mem_FP

theorem machineOptimizerFeasibilityFirstBits_mem_FP :
    machineOptimizerFeasibilityFirstBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityFirstBaseBits_mem_FP
    (machineBinaryConst_mem_FP 1)

theorem machineOptimizerFeasibilityThreeDBits_mem_FP :
    machineOptimizerFeasibilityThreeDBits ∈ FP :=
  machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 3)
    machineOptimizerFeasibilityDBits_mem_FP

theorem machineOptimizerFeasibilitySixPlusThreeDBits_mem_FP :
    machineOptimizerFeasibilitySixPlusThreeDBits ∈ FP :=
  machineBinaryAddOf_mem_FP (machineBinaryConst_mem_FP 6)
    machineOptimizerFeasibilityThreeDBits_mem_FP

theorem machineOptimizerFeasibilityTTimesGrowthBits_mem_FP :
    machineOptimizerFeasibilityTTimesGrowthBits ∈ FP :=
  machineBinaryMulOf_mem_FP machineOptimizerFeasibilityBudgetBits_mem_FP
    machineOptimizerFeasibilitySixPlusThreeDBits_mem_FP

theorem machineOptimizerFeasibilityKPlusGrowthBits_mem_FP :
    machineOptimizerFeasibilityKPlusGrowthBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityKBits_mem_FP
    machineOptimizerFeasibilityTTimesGrowthBits_mem_FP

theorem machineOptimizerFeasibilityKPlusGrowthPlusThreeBits_mem_FP :
    machineOptimizerFeasibilityKPlusGrowthPlusThreeBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityKPlusGrowthBits_mem_FP
    (machineBinaryConst_mem_FP 3)

theorem machineOptimizerFeasibilityInnerMagnitudeBits_mem_FP :
    machineOptimizerFeasibilityInnerMagnitudeBits ∈ FP :=
  machineBinaryAddOf_mem_FP
    machineOptimizerFeasibilityKPlusGrowthPlusThreeBits_mem_FP
    machineOptimizerFeasibilityDBits_mem_FP

theorem machineOptimizerFeasibilityDInnerMagnitudeBits_mem_FP :
    machineOptimizerFeasibilityDInnerMagnitudeBits ∈ FP :=
  machineBinaryMulOf_mem_FP machineOptimizerFeasibilityDBits_mem_FP
    machineOptimizerFeasibilityInnerMagnitudeBits_mem_FP

theorem machineOptimizerFeasibilityEightDBits_mem_FP :
    machineOptimizerFeasibilityEightDBits ∈ FP :=
  machineBinaryMulOf_mem_FP (machineBinaryConst_mem_FP 8)
    machineOptimizerFeasibilityDBits_mem_FP

theorem machineOptimizerFeasibilityDenomFirstBits_mem_FP :
    machineOptimizerFeasibilityDenomFirstBits ∈ FP :=
  machineBinaryAddOf_mem_FP (machineBinaryConst_mem_FP 12)
    machineOptimizerFeasibilityEightDBits_mem_FP

theorem machineOptimizerFeasibilityDenomSecondBits_mem_FP :
    machineOptimizerFeasibilityDenomSecondBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityDenomFirstBits_mem_FP
    machineOptimizerFeasibilityDSquareBits_mem_FP

theorem machineOptimizerFeasibilityDenominatorExponentBits_mem_FP :
    machineOptimizerFeasibilityDenominatorExponentBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityDenomSecondBits_mem_FP
    machineOptimizerFeasibilityDInnerMagnitudeBits_mem_FP

theorem machineOptimizerFeasibilityPrecisionBaseBits_mem_FP :
    machineOptimizerFeasibilityPrecisionBaseBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityFirstBits_mem_FP
    machineOptimizerFeasibilityDenominatorExponentBits_mem_FP

theorem machineOptimizerFeasibilityRoundingPrecisionBits_mem_FP :
    machineOptimizerFeasibilityRoundingPrecisionBits ∈ FP :=
  machineBinaryAddOf_mem_FP machineOptimizerFeasibilityPrecisionBaseBits_mem_FP
    (machineBinaryConst_mem_FP 2)

theorem machineOptimizerFeasibilityRoundingGuardSource_mem_FP :
    machineOptimizerFeasibilityRoundingGuardSource ∈ FP := by
  simpa only [machineOptimizerFeasibilityRoundingGuardSource] using
    machineAppend_mem_FP machineOptimizerFeasibilityBudgetUnary_mem_FP
      (machineAppend_mem_FP
        machineOptimizerFeasibilityEllipsoidDimensionUnary_mem_FP
        (machineAppend_mem_FP
          machineOptimizerFeasibilityInitialMagnitudeLengthRuler_mem_FP
          machineOptimizerFeasibilityOuterRadiusLengthRuler_mem_FP))

theorem machineOptimizerFeasibilityRoundingGuard_mem_FP :
    machineOptimizerFeasibilityRoundingGuard ∈ FP := by
  simpa only [machineOptimizerFeasibilityRoundingGuard] using
    machineCompose_mem_FP
      machineOptimizerFeasibilityRoundingGuardSource_mem_FP
      (machineIteratedBinaryWidth_mem_FP 2)

theorem machineOptimizerFeasibilityRoundingPrecisionUnary_mem_FP :
    machineOptimizerFeasibilityRoundingPrecisionUnary ∈ FP := by
  simpa only [machineOptimizerFeasibilityRoundingPrecisionUnary] using
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityRoundingGuard_mem_FP
        machineOptimizerFeasibilityRoundingPrecisionBits_mem_FP)
      machineBoundedUnary_mem_FP

/-! ## Exact semantics -/

@[simp] theorem machineOptimizerFeasibilityInitialMagnitudeRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInitialMagnitudeRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode
        (rawOptimizerFeasibilityInitialMagnitude ((n - 1) ^ 2 + 1)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper)) := by
  rw [machineOptimizerFeasibilityInitialMagnitudeRawCode,
    machineOptimizerFeasibilityEllipsoidDimensionRawCode_encode,
    machineOptimizerFeasibilityOuterRadiusRawCode_encode hn,
    machineRawRatMulCode_encode, machineRawRatAddCode_encode]
  rfl

@[simp] theorem rawOptimizerFeasibilityInitialMagnitude_value
    (d : ℕ) (R : RawRat) :
    (rawOptimizerFeasibilityInitialMagnitude d R).value =
      explicitBallInitialMagnitudeBound d R.value := by
  simp [rawOptimizerFeasibilityInitialMagnitude,
    explicitBallInitialMagnitudeBound, rawOptimizerTwo]

@[simp] theorem machineOptimizerFeasibilityInitialMagnitudeLengthRuler_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInitialMagnitudeLengthRuler
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (explicitBallInitialMagnitudeExponent ((n - 1) ^ 2 + 1)
          ((rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value)) true := by
  rw [machineOptimizerFeasibilityInitialMagnitudeLengthRuler,
    machineOptimizerFeasibilityInitialMagnitudeEntryCode,
    machineOptimizerFeasibilityInitialMagnitudeRawCode_encode hn,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value,
    machineOptimizerEntryLengthRuler_encode]
  rw [rawOptimizerFeasibilityInitialMagnitude_value]
  rfl

def optimizerFeasibilityRoundingPrecision
    (d LR K T : ℕ) : ℕ :=
  (LR * d + 2 * T + 1) +
    (12 + 8 * d + d ^ 2 +
      d * (K + T * (6 + 3 * d) + 3 + d)) + 2

theorem optimizerFeasibilityRoundingPrecision_eq_explicit
    (d T : ℕ) (R : ℚ) :
    optimizerFeasibilityRoundingPrecision d (encodedBitLength ℚ R)
        (explicitBallInitialMagnitudeExponent d R) T =
      explicitBallFeasibilityPrecision d T R := by
  rw [optimizerFeasibilityRoundingPrecision,
    explicitBallFeasibilityPrecision, explicitBallInitialDetExponent,
    roundedEllipsoidPrecisionSchedule,
    roundedEllipsoidNextPrecisionBound,
    roundedEllipsoidDenominatorExponent]

@[simp] theorem machineOptimizerFeasibilityRoundingPrecisionBits_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityRoundingPrecisionBits
        (optimizerFeasibilityCallCode A upper) =
      (explicitBallFeasibilityPrecision ((n - 1) ^ 2 + 1)
        (betheThresholdFeasibilityBudget (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value)
        (rawOptimizerFeasibilityOuterRadius n
          (rationalMatrixEntryBitBound A) upper).value).bits := by
  let word := optimizerFeasibilityCallCode A upper
  let d := (n - 1) ^ 2 + 1
  let R := (rawOptimizerFeasibilityOuterRadius n
    (rationalMatrixEntryBitBound A) upper).value
  let LR := encodedBitLength ℚ R
  let K := explicitBallInitialMagnitudeExponent d R
  let T := 32 * d ^ 3 * rationalBallDyadicExponent d R
    (rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value
  have hd : machineOptimizerFeasibilityDBits word = d.bits := by
    simpa only [machineOptimizerFeasibilityDBits, word, d] using
      machineOptimizerFeasibilityEllipsoidDimensionBits_encode A upper
  have hLR : machineOptimizerFeasibilityOuterLengthBits word = LR.bits := by
    have hRuler : machineOptimizerFeasibilityOuterRadiusLengthRuler word =
        List.replicate LR true := by
      simpa only [word, LR, R] using
        machineOptimizerFeasibilityOuterRadiusLengthRuler_encode hn A upper
    rw [machineOptimizerFeasibilityOuterLengthBits, hRuler,
      machineLengthBits_encode, List.length_replicate]
  have hK : machineOptimizerFeasibilityKBits word = K.bits := by
    have hRuler :
        machineOptimizerFeasibilityInitialMagnitudeLengthRuler word =
          List.replicate K true := by
      simpa only [word, K, d, R] using
        machineOptimizerFeasibilityInitialMagnitudeLengthRuler_encode hn A upper
    rw [machineOptimizerFeasibilityKBits, hRuler,
      machineLengthBits_encode, List.length_replicate]
  have hT : machineOptimizerFeasibilityBudgetBits word = T.bits := by
    simpa only [word, T, d, R] using
      machineOptimizerFeasibilityBudgetBits_encode hn A upper
  have hL : machineOptimizerFeasibilityLBits word = (LR * d).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ hLR hd
  have h2T : machineOptimizerFeasibilityTwoTBits word = (2 * T).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hT
  have hfirstBase : machineOptimizerFeasibilityFirstBaseBits word =
      (LR * d + 2 * T).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hL h2T
  have hfirst : machineOptimizerFeasibilityFirstBits word =
      (LR * d + 2 * T + 1).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hfirstBase rfl
  have h3d : machineOptimizerFeasibilityThreeDBits word = (3 * d).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hd
  have hgrowth : machineOptimizerFeasibilitySixPlusThreeDBits word =
      (6 + 3 * d).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ rfl h3d
  have hTgrowth : machineOptimizerFeasibilityTTimesGrowthBits word =
      (T * (6 + 3 * d)).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ hT hgrowth
  have hKgrowth : machineOptimizerFeasibilityKPlusGrowthBits word =
      (K + T * (6 + 3 * d)).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hK hTgrowth
  have hKgrowth3 :
      machineOptimizerFeasibilityKPlusGrowthPlusThreeBits word =
        (K + T * (6 + 3 * d) + 3).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hKgrowth rfl
  have hinner : machineOptimizerFeasibilityInnerMagnitudeBits word =
      (K + T * (6 + 3 * d) + 3 + d).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hKgrowth3 hd
  have hdinner : machineOptimizerFeasibilityDInnerMagnitudeBits word =
      (d * (K + T * (6 + 3 * d) + 3 + d)).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ hd hinner
  have h8d : machineOptimizerFeasibilityEightDBits word = (8 * d).bits :=
    machineBinaryMulOf_natBits _ _ _ _ _ rfl hd
  have hden1 : machineOptimizerFeasibilityDenomFirstBits word =
      (12 + 8 * d).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ rfl h8d
  have hd2 : machineOptimizerFeasibilityDSquareBits word = (d ^ 2).bits := by
    rw [machineOptimizerFeasibilityDSquareBits, hd,
      machineBinaryMulBits_pair_natBits]
    simp only [pow_two]
  have hden2 : machineOptimizerFeasibilityDenomSecondBits word =
      (12 + 8 * d + d ^ 2).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hden1 hd2
  have hden : machineOptimizerFeasibilityDenominatorExponentBits word =
      (12 + 8 * d + d ^ 2 +
        d * (K + T * (6 + 3 * d) + 3 + d)).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hden2 hdinner
  have hbase : machineOptimizerFeasibilityPrecisionBaseBits word =
      ((LR * d + 2 * T + 1) +
        (12 + 8 * d + d ^ 2 +
          d * (K + T * (6 + 3 * d) + 3 + d))).bits :=
    machineBinaryAddOf_natBits _ _ _ _ _ hfirst hden
  have hp : machineOptimizerFeasibilityRoundingPrecisionBits word =
      (optimizerFeasibilityRoundingPrecision d LR K T).bits := by
    rw [machineOptimizerFeasibilityRoundingPrecisionBits]
    exact machineBinaryAddOf_natBits _ _ _ _ _ hbase rfl
  have hRthreshold :
      R = betheEpigraphOuterRadius (n - 1) upper.value
        (rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)).value := by
    dsimp [R]
    rw [rawOptimizerFeasibilityOuterRadius_value,
      betheEpigraphOuterRadius]
    push_cast
    rw [pow_two]
  have hTthreshold :
      T = betheThresholdFeasibilityBudget (n - 1) upper.value
        (rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)).value := by
    dsimp [T, d]
    rw [betheThresholdFeasibilityBudget, hRthreshold, pow_two]
  rw [hp, optimizerFeasibilityRoundingPrecision_eq_explicit, hTthreshold]

theorem optimizerFeasibilityRoundingPrecision_le_guardPolynomial
    (d LR K T : ℕ) :
    optimizerFeasibilityRoundingPrecision d LR K T ≤
      certificateExpGuardWidth 2 (T + d + K + LR) := by
  let Q := T + d + K + LR
  have hd : d ≤ Q := by omega
  have hLR : LR ≤ Q := by omega
  have hK : K ≤ Q := by omega
  have hT : T ≤ Q := by omega
  have hLRd : LR * d ≤ Q ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hLR hd
  have hd2 : d ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hd 2
  have hdK : d * K ≤ Q ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hd hK
  have hdT : d * T ≤ Q ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hd hT
  have hd2T : d ^ 2 * T ≤ Q ^ 3 := by
    simpa only [pow_two, pow_succ, pow_zero, one_mul] using
      Nat.mul_le_mul (Nat.mul_le_mul hd hd) hT
  have hcoarse : optimizerFeasibilityRoundingPrecision d LR K T ≤
      3 * Q ^ 3 + 10 * Q ^ 2 + 13 * Q + 15 := by
    rw [optimizerFeasibilityRoundingPrecision]
    nlinarith
  have hcubic :
      3 * Q ^ 3 + 10 * Q ^ 2 + 13 * Q + 15 ≤
        8 * (Q + 4) ^ 3 := by nlinarith
  have h8 : 8 ≤ Q + 16 := by omega
  have hshift : (Q + 4) ^ 3 ≤ (Q + 16) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  calc
    optimizerFeasibilityRoundingPrecision d LR K T ≤
        3 * Q ^ 3 + 10 * Q ^ 2 + 13 * Q + 15 := hcoarse
    _ ≤ 8 * (Q + 4) ^ 3 := hcubic
    _ ≤ (Q + 16) * (Q + 16) ^ 3 := Nat.mul_le_mul h8 hshift
    _ = (Q + 16) ^ 4 := by ring
    _ ≤ certificateExpGuardWidth 2 Q := by
      simpa using certificateExpGuardWidth_pow_lower 1 Q

@[simp] theorem machineOptimizerFeasibilityRoundingGuardSource_length_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    (machineOptimizerFeasibilityRoundingGuardSource
      (optimizerFeasibilityCallCode A upper)).length =
      betheThresholdFeasibilityBudget (n - 1) upper.value
          (rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value +
        ((n - 1) ^ 2 + 1) +
        explicitBallInitialMagnitudeExponent ((n - 1) ^ 2 + 1)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value +
        encodedBitLength ℚ
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value := by
  have hn1 : 1 ≤ n := by omega
  have hRthreshold :
      (rawOptimizerFeasibilityOuterRadius n
        (rationalMatrixEntryBitBound A) upper).value =
      betheEpigraphOuterRadius (n - 1) upper.value
        (rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)).value := by
    rw [rawOptimizerFeasibilityOuterRadius_value,
      betheEpigraphOuterRadius]
    push_cast
    rw [pow_two]
  rw [machineOptimizerFeasibilityRoundingGuardSource,
    machineOptimizerFeasibilityBudgetUnary_encode hn,
    machineOptimizerFeasibilityEllipsoidDimensionUnary_encode hn,
    machineOptimizerFeasibilityInitialMagnitudeLengthRuler_encode hn1,
    machineOptimizerFeasibilityOuterRadiusLengthRuler_encode hn1]
  simp only [List.length_append, List.length_replicate]
  rw [betheThresholdFeasibilityBudget, hRthreshold, pow_two]
  omega

@[simp] theorem machineOptimizerFeasibilityRoundingPrecisionUnary_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityRoundingPrecisionUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (explicitBallFeasibilityPrecision ((n - 1) ^ 2 + 1)
          (betheThresholdFeasibilityBudget (n - 1) upper.value
            (rawExplicitOptimizerInnerRadius n
              (rationalMatrixEntryBitBound A)).value)
          (rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value) true := by
  let d := (n - 1) ^ 2 + 1
  let R := (rawOptimizerFeasibilityOuterRadius n
    (rationalMatrixEntryBitBound A) upper).value
  let LR := encodedBitLength ℚ R
  let K := explicitBallInitialMagnitudeExponent d R
  let T := betheThresholdFeasibilityBudget (n - 1) upper.value
    (rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value
  rw [machineOptimizerFeasibilityRoundingPrecisionUnary,
    machineOptimizerFeasibilityRoundingPrecisionBits_encode (by omega)]
  apply machineBoundedUnary_encode_of_le
  rw [machineOptimizerFeasibilityRoundingGuard,
    machineIteratedBinaryWidth_length,
    machineOptimizerFeasibilityRoundingGuardSource_length_encode hn]
  rw [← optimizerFeasibilityRoundingPrecision_eq_explicit d T R]
  simpa only [d, R, LR, K, T] using
    optimizerFeasibilityRoundingPrecision_le_guardPolynomial d LR K T

end BeyondBethe
