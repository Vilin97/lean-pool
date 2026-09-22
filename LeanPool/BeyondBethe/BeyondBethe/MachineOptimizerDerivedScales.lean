/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerInteriorScale
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMin

/-!
# Remaining rational scales and precision ruler for the optimizer

Starting from the guarded dyadic interior floor, all remaining scales are
formed by exact unreduced rational arithmetic.  The precision is emitted
directly as a unary ruler assembled from the exact canonical encoding length
of the objective gap and fixed dimension-dependent summands.
-/

namespace BeyondBethe

open Complexity

def rawOptimizerOne : RawRat := RawRat.ofNat 1

def rawOptimizerThree : RawRat := RawRat.ofNat 3

def rawOptimizerTen : RawRat := RawRat.ofNat 10

def rawOptimizerFortyEight : RawRat := RawRat.ofNat 48

def rawOptimizerKKTError : RawRat := rawRatOfRat explicitKKTError

def rawExplicitOptimizerFloor (n B : ℕ) : RawRat :=
  (rawOptimizerHalf.pow
    (numericalInteriorExponent n B (explicitRegularizationScale n))).div
      rawOptimizerTwo

def rawExplicitOptimizerRho (n B : ℕ) : RawRat :=
  ((rawExplicitOptimizerFloor n B).mul rawOptimizerKKTError).div
    rawOptimizerFortyEight

def rawExplicitOptimizerGap (n B : ℕ) : RawRat :=
  ((rawOptimizerTau n).mul
    ((rawExplicitOptimizerRho n B).mul (rawExplicitOptimizerRho n B))).div
      rawOptimizerFour

def rawOptimizerObjectiveRange (n B : ℕ) : RawRat :=
  ((rawOptimizerDimension n).mul (rawOptimizerBitBound B)).add
    (rawOptimizerThree.mul (rawOptimizerNSquare n))

def rawOptimizerMixDenominator (n B : ℕ) : RawRat :=
  rawOptimizerFour.mul ((rawOptimizerObjectiveRange n B).add rawOptimizerOne)

def rawOptimizerMixCandidate (n B : ℕ) : RawRat :=
  (rawExplicitOptimizerGap n B).div (rawOptimizerMixDenominator n B)

def rawExplicitOptimizerMix (n B : ℕ) : RawRat :=
  if rawOptimizerHalf.value ≤ (rawOptimizerMixCandidate n B).value then
    rawOptimizerHalf
  else rawOptimizerMixCandidate n B

def rawOptimizerTwiceDimension (n : ℕ) : RawRat :=
  rawOptimizerTwo.mul (rawOptimizerDimension n)

def rawExplicitOptimizerInnerRadius (n B : ℕ) : RawRat :=
  (rawExplicitOptimizerMix n B).div (rawOptimizerTwiceDimension n)

/-! ## Finite-word scale machines -/

def machineExplicitOptimizerRhoRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair
      (machineRawRatMulCode
        (pair (machineExplicitOptimizerFloorRawCode word)
          (rawRatBinaryCode rawOptimizerKKTError)))
      (rawRatBinaryCode rawOptimizerFortyEight))

def machineExplicitOptimizerRhoSquareRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineExplicitOptimizerRhoRawCode word)
      (machineExplicitOptimizerRhoRawCode word))

def machineExplicitOptimizerGapNumeratorRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerTauRawCode word)
      (machineExplicitOptimizerRhoSquareRawCode word))

def machineExplicitOptimizerGapRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineExplicitOptimizerGapNumeratorRawCode word)
      (rawRatBinaryCode rawOptimizerFour))

def machineOptimizerThreeNSquareRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerThree)
      (machineOptimizerNSquareRawCode word))

def machineOptimizerObjectiveRangeRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerNBProductRawCode word)
      (machineOptimizerThreeNSquareRawCode word))

def machineOptimizerRangePlusOneRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerObjectiveRangeRawCode word)
      (rawRatBinaryCode rawOptimizerOne))

def machineOptimizerMixDenominatorRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerFour)
      (machineOptimizerRangePlusOneRawCode word))

def machineOptimizerMixCandidateRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineExplicitOptimizerGapRawCode word)
      (machineOptimizerMixDenominatorRawCode word))

def machineExplicitOptimizerMixRawCode (word : List Bool) : List Bool :=
  machineRawRatMinCode
    (pair (rawRatBinaryCode rawOptimizerHalf)
      (machineOptimizerMixCandidateRawCode word))

def machineOptimizerTwiceDimensionRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineOptimizerDimensionRawCode word))

def machineExplicitOptimizerInnerRadiusRawCode
    (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineExplicitOptimizerMixRawCode word)
      (machineOptimizerTwiceDimensionRawCode word))

/-! ## Polynomial-time closure -/

theorem machineExplicitOptimizerRhoRawCode_mem_FP :
    machineExplicitOptimizerRhoRawCode ∈ FP := by
  have hproduct := machineCompose_mem_FP
    (machinePair_mem_FP machineExplicitOptimizerFloorRawCode_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerKKTError)))
    machineRawRatMulCode_mem_FP
  simpa only [machineExplicitOptimizerRhoRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP hproduct
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerFortyEight)))
    machineRawRatDivCode_mem_FP

theorem machineExplicitOptimizerRhoSquareRawCode_mem_FP :
    machineExplicitOptimizerRhoSquareRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerRhoSquareRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineExplicitOptimizerRhoRawCode_mem_FP
        machineExplicitOptimizerRhoRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineExplicitOptimizerGapNumeratorRawCode_mem_FP :
    machineExplicitOptimizerGapNumeratorRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerGapNumeratorRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerTauRawCode_mem_FP
        machineExplicitOptimizerRhoSquareRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineExplicitOptimizerGapRawCode_mem_FP :
    machineExplicitOptimizerGapRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerGapRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineExplicitOptimizerGapNumeratorRawCode_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerFour)))
    machineRawRatDivCode_mem_FP

theorem machineOptimizerThreeNSquareRawCode_mem_FP :
    machineOptimizerThreeNSquareRawCode ∈ FP := by
  simpa only [machineOptimizerThreeNSquareRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerThree))
      machineOptimizerNSquareRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerObjectiveRangeRawCode_mem_FP :
    machineOptimizerObjectiveRangeRawCode ∈ FP := by
  simpa only [machineOptimizerObjectiveRangeRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerNBProductRawCode_mem_FP
      machineOptimizerThreeNSquareRawCode_mem_FP)
    machineRawRatAddCode_mem_FP

theorem machineOptimizerRangePlusOneRawCode_mem_FP :
    machineOptimizerRangePlusOneRawCode ∈ FP := by
  simpa only [machineOptimizerRangePlusOneRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerObjectiveRangeRawCode_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerOne)))
    machineRawRatAddCode_mem_FP

theorem machineOptimizerMixDenominatorRawCode_mem_FP :
    machineOptimizerMixDenominatorRawCode ∈ FP := by
  simpa only [machineOptimizerMixDenominatorRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerFour))
      machineOptimizerRangePlusOneRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerMixCandidateRawCode_mem_FP :
    machineOptimizerMixCandidateRawCode ∈ FP := by
  simpa only [machineOptimizerMixCandidateRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineExplicitOptimizerGapRawCode_mem_FP
      machineOptimizerMixDenominatorRawCode_mem_FP)
    machineRawRatDivCode_mem_FP

theorem machineExplicitOptimizerMixRawCode_mem_FP :
    machineExplicitOptimizerMixRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerMixRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerHalf))
      machineOptimizerMixCandidateRawCode_mem_FP)
    machineRawRatMinCode_mem_FP

theorem machineOptimizerTwiceDimensionRawCode_mem_FP :
    machineOptimizerTwiceDimensionRawCode ∈ FP := by
  simpa only [machineOptimizerTwiceDimensionRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP
      (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
      machineOptimizerDimensionRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineExplicitOptimizerInnerRadiusRawCode_mem_FP :
    machineExplicitOptimizerInnerRadiusRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerInnerRadiusRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineExplicitOptimizerMixRawCode_mem_FP
        machineOptimizerTwiceDimensionRawCode_mem_FP)
      machineRawRatDivCode_mem_FP

/-! ## Exact semantics -/

@[simp] theorem machineExplicitOptimizerRhoRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerRhoRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawExplicitOptimizerRho n (rationalMatrixEntryBitBound A)) := by
  rw [machineExplicitOptimizerRhoRawCode,
    machineExplicitOptimizerFloorRawCode_encode hn,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineExplicitOptimizerRhoSquareRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerRhoSquareRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        ((rawExplicitOptimizerRho n
          (rationalMatrixEntryBitBound A)).mul
          (rawExplicitOptimizerRho n
            (rationalMatrixEntryBitBound A))) := by
  rw [machineExplicitOptimizerRhoSquareRawCode,
    machineExplicitOptimizerRhoRawCode_encode hn,
    machineRawRatMulCode_encode]

@[simp] theorem machineExplicitOptimizerGapRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerGapRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawExplicitOptimizerGap n (rationalMatrixEntryBitBound A)) := by
  rw [machineExplicitOptimizerGapRawCode,
    machineExplicitOptimizerGapNumeratorRawCode,
    machineOptimizerTauRawCode_encode,
    machineExplicitOptimizerRhoSquareRawCode_encode hn,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineOptimizerThreeNSquareRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerThreeNSquareRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerThree.mul (rawOptimizerNSquare n)) := by
  rw [machineOptimizerThreeNSquareRawCode,
    machineOptimizerNSquareRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerObjectiveRangeRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerObjectiveRangeRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerObjectiveRange n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerObjectiveRangeRawCode,
    machineOptimizerNBProductRawCode_encode,
    machineOptimizerThreeNSquareRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerRangePlusOneRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerRangePlusOneRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        ((rawOptimizerObjectiveRange n
          (rationalMatrixEntryBitBound A)).add rawOptimizerOne) := by
  rw [machineOptimizerRangePlusOneRawCode,
    machineOptimizerObjectiveRangeRawCode_encode,
    machineRawRatAddCode_encode]

@[simp] theorem machineOptimizerMixDenominatorRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerMixDenominatorRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerMixDenominator n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerMixDenominatorRawCode,
    machineOptimizerRangePlusOneRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineOptimizerMixCandidateRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerMixCandidateRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerMixCandidate n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerMixCandidateRawCode,
    machineExplicitOptimizerGapRawCode_encode hn,
    machineOptimizerMixDenominatorRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem machineExplicitOptimizerMixRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerMixRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawExplicitOptimizerMix n (rationalMatrixEntryBitBound A)) := by
  rw [machineExplicitOptimizerMixRawCode,
    machineOptimizerMixCandidateRawCode_encode hn,
    machineRawRatMinCode_encode]
  rfl

@[simp] theorem machineOptimizerTwiceDimensionRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTwiceDimensionRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerTwiceDimension n) := by
  rw [machineOptimizerTwiceDimensionRawCode,
    machineOptimizerDimensionRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineExplicitOptimizerInnerRadiusRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerInnerRadiusRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)) := by
  rw [machineExplicitOptimizerInnerRadiusRawCode,
    machineExplicitOptimizerMixRawCode_encode hn,
    machineOptimizerTwiceDimensionRawCode_encode,
    machineRawRatDivCode_encode]
  rfl

@[simp] theorem rawExplicitOptimizerFloor_value (n B : ℕ) :
    (rawExplicitOptimizerFloor n B).value =
      numericalInteriorFloor n B (explicitRegularizationScale n) / 2 := by
  simp [rawExplicitOptimizerFloor, numericalInteriorFloor,
    rawOptimizerHalf, rawOptimizerTwo]

@[simp] theorem rawExplicitOptimizerRho_value (n B : ℕ) :
    (rawExplicitOptimizerRho n B).value =
      numericalInteriorFloor n B (explicitRegularizationScale n) / 2 *
        explicitKKTError / 48 := by
  simp [rawExplicitOptimizerRho, rawOptimizerKKTError,
    rawOptimizerFortyEight]

@[simp] theorem rawExplicitOptimizerGap_value (n B : ℕ) :
    (rawExplicitOptimizerGap n B).value =
      explicitRegularizationScale n *
        (numericalInteriorFloor n B (explicitRegularizationScale n) / 2 *
          explicitKKTError / 48) ^ 2 / 4 := by
  simp [rawExplicitOptimizerGap, rawOptimizerFour, pow_two]

@[simp] theorem rawOptimizerObjectiveRange_value (n B : ℕ) :
    (rawOptimizerObjectiveRange n B).value = n * B + 3 * n ^ 2 := by
  simp [rawOptimizerObjectiveRange, rawOptimizerThree,
    rawOptimizerNSquare]
  ring

@[simp] theorem rawOptimizerMixDenominator_value (n B : ℕ) :
    (rawOptimizerMixDenominator n B).value =
      4 * ((rawOptimizerObjectiveRange n B).value + 1) := by
  simp [rawOptimizerMixDenominator, rawOptimizerFour, rawOptimizerOne]

@[simp] theorem rawOptimizerMixCandidate_value (n B : ℕ) :
    (rawOptimizerMixCandidate n B).value =
      (rawExplicitOptimizerGap n B).value /
        (4 * ((rawOptimizerObjectiveRange n B).value + 1)) := by
  simp [rawOptimizerMixCandidate]

@[simp] theorem rawExplicitOptimizerMix_value (n B : ℕ) :
    (rawExplicitOptimizerMix n B).value =
      min (1 / 2)
        ((rawExplicitOptimizerGap n B).value /
          (4 * ((rawOptimizerObjectiveRange n B).value + 1))) := by
  rw [← rawOptimizerHalf_value,
    ← rawOptimizerMixCandidate_value]
  rw [rawExplicitOptimizerMix]
  by_cases h : rawOptimizerHalf.value ≤
      (rawOptimizerMixCandidate n B).value
  · rw [ite_eq_left h, min_eq_left h]
  · rw [ite_eq_right h, min_eq_right (le_of_not_ge h)]

@[simp] theorem rawExplicitOptimizerInnerRadius_value (n B : ℕ) :
    (rawExplicitOptimizerInnerRadius n B).value =
      (rawExplicitOptimizerMix n B).value / (2 * n) := by
  simp [rawExplicitOptimizerInnerRadius, rawOptimizerTwiceDimension,
    rawOptimizerTwo]

theorem rawExplicitOptimizerScales_value {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    (rawExplicitOptimizerFloor (m + 1)
        (rationalMatrixEntryBitBound A)).value = explicitOptimizerFloor A ∧
    (rawExplicitOptimizerRho (m + 1)
        (rationalMatrixEntryBitBound A)).value = explicitOptimizerRho A ∧
    (rawExplicitOptimizerGap (m + 1)
        (rationalMatrixEntryBitBound A)).value = explicitOptimizerGap A ∧
    (rawExplicitOptimizerMix (m + 1)
        (rationalMatrixEntryBitBound A)).value = explicitOptimizerMix A ∧
    (rawExplicitOptimizerInnerRadius (m + 1)
        (rationalMatrixEntryBitBound A)).value =
      explicitOptimizerInnerRadius A := by
  simp [explicitOptimizerFloor, explicitOptimizerRho, explicitOptimizerGap,
    explicitOptimizerMix, explicitOptimizerInnerRadius,
    rationalRegularizedObjectiveRange]

/-! ## Exact unary precision ruler -/

def machineExplicitOptimizerGapEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineExplicitOptimizerGapRawCode word)

def machineExplicitOptimizerGapLengthRuler
    (word : List Bool) : List Bool :=
  machineOptimizerEntryLengthRuler
    (machineExplicitOptimizerGapEntryCode word)

def machineExplicitOptimizerPrecisionRuler
    (word : List Bool) : List Bool :=
  machineExplicitOptimizerGapLengthRuler word ++
    (List.replicate (encodedBitLength ℚ explicitKKTError) true ++
      (machineOptimizerDimensionUnary word ++
        (machineOptimizerDimensionUnary word ++ List.replicate 10 true)))

theorem machineExplicitOptimizerGapEntryCode_mem_FP :
    machineExplicitOptimizerGapEntryCode ∈ FP := by
  simpa only [machineExplicitOptimizerGapEntryCode] using!
    machineCompose_mem_FP machineExplicitOptimizerGapRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineExplicitOptimizerGapLengthRuler_mem_FP :
    machineExplicitOptimizerGapLengthRuler ∈ FP := by
  simpa only [machineExplicitOptimizerGapLengthRuler] using!
    machineCompose_mem_FP machineExplicitOptimizerGapEntryCode_mem_FP
      machineOptimizerEntryLengthRuler_mem_FP

theorem machineExplicitOptimizerPrecisionRuler_mem_FP :
    machineExplicitOptimizerPrecisionRuler ∈ FP := by
  have hdim2 := machineAppend_mem_FP machineOptimizerDimensionUnary_mem_FP
    (machineAppend_mem_FP machineOptimizerDimensionUnary_mem_FP
      (machineConst_mem_FP (List.replicate 10 true)))
  have htail := machineAppend_mem_FP
    (machineConst_mem_FP
      (List.replicate (encodedBitLength ℚ explicitKKTError) true)) hdim2
  simpa only [machineExplicitOptimizerPrecisionRuler] using!
    machineAppend_mem_FP machineExplicitOptimizerGapLengthRuler_mem_FP htail

@[simp] theorem machineExplicitOptimizerGapEntryCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerGapEntryCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalEntryBinaryCode
        ((rawExplicitOptimizerGap n
          (rationalMatrixEntryBitBound A)).value) := by
  rw [machineExplicitOptimizerGapEntryCode,
    machineExplicitOptimizerGapRawCode_encode hn,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value]

@[simp] theorem machineExplicitOptimizerGapLengthRuler_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerGapLengthRuler
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate
        (encodedBitLength ℚ
          ((rawExplicitOptimizerGap n
            (rationalMatrixEntryBitBound A)).value)) true := by
  rw [machineExplicitOptimizerGapLengthRuler,
    machineExplicitOptimizerGapEntryCode_encode hn,
    machineOptimizerEntryLengthRuler_encode]

@[simp] theorem machineExplicitOptimizerPrecisionRuler_encode
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineExplicitOptimizerPrecisionRuler
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      List.replicate (explicitOptimizerPrecision A) true := by
  rw [machineExplicitOptimizerPrecisionRuler,
    machineExplicitOptimizerGapLengthRuler_encode (by omega),
    machineOptimizerDimensionUnary_encode]
  have hgap := (rawExplicitOptimizerScales_value A).2.2.1
  rw [hgap]
  simp only [← List.replicate_add, explicitOptimizerPrecision]
  congr 1
  omega

end BeyondBethe
