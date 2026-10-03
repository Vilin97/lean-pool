/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerDerivedScales

/-!
# Initial interval and bisection schedule as finite-word functions

The initial objective width is assembled by exact rational arithmetic.  The
number of bisection calls is then the sum of the canonical encoding lengths
of that width and of the optimizer gap, plus three.  Both schedules are
returned in unary, so later bounded iterations can consume them directly.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- The raw-rational objective upper bound `n*B + n`. -/
def rawOptimizerObjectiveUpper (n B : ℕ) : RawRat :=
  ((rawOptimizerDimension n).mul (rawOptimizerBitBound B)).add
    (rawOptimizerDimension n)

/-- Twice the explicit optimizer inner radius as a raw rational. -/
def rawOptimizerTwiceInnerRadius (n B : ℕ) : RawRat :=
  rawOptimizerTwo.mul (rawExplicitOptimizerInnerRadius n B)

/-- The smoothing slack given by mixing times the objective range plus twice the inner radius. -/
def rawOptimizerSmoothingSlack (n B : ℕ) : RawRat :=
  ((rawExplicitOptimizerMix n B).mul
    (rawOptimizerObjectiveRange n B)).add
      (rawOptimizerTwiceInnerRadius n B)

/-- The initial upper threshold obtained by adding smoothing slack to the objective upper bound. -/
def rawOptimizerInitialHigh (n B : ℕ) : RawRat :=
  (rawOptimizerObjectiveUpper n B).add
    (rawOptimizerSmoothingSlack n B)

/-- The raw-rational quantity `2*n^2` used to form the initial interval width. -/
def rawOptimizerTwiceNSquare (n : ℕ) : RawRat :=
  rawOptimizerTwo.mul (rawOptimizerNSquare n)

/-- The initial upper threshold minus the lower threshold `-2*n^2`. -/
def rawExplicitOptimizerInitialWidth (n B : ℕ) : RawRat :=
  (rawOptimizerInitialHigh n B).add (rawOptimizerTwiceNSquare n)

/-- Computes the encoded objective upper bound `n*B + n`. -/
def machineOptimizerObjectiveUpperRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerNBProductRawCode word)
      (machineOptimizerDimensionRawCode word))

/-- Computes twice the encoded optimizer inner radius. -/
def machineOptimizerTwiceInnerRadiusRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineExplicitOptimizerInnerRadiusRawCode word))

/-- Multiplies the encoded mixing parameter by the objective range. -/
def machineOptimizerMixRangeRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineExplicitOptimizerMixRawCode word)
      (machineOptimizerObjectiveRangeRawCode word))

/-- Adds the mixing-range product and twice the inner radius to encode smoothing slack. -/
def machineOptimizerSmoothingSlackRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerMixRangeRawCode word)
      (machineOptimizerTwiceInnerRadiusRawCode word))

/-- Adds smoothing slack to the encoded objective upper bound. -/
def machineOptimizerInitialHighRawCode (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerObjectiveUpperRawCode word)
      (machineOptimizerSmoothingSlackRawCode word))

/-- Computes the encoded quantity `2*n^2` used in the initial width. -/
def machineOptimizerTwiceNSquareForWidthRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineOptimizerNSquareRawCode word))

/-- Adds `2*n^2` to the initial upper threshold to encode the initial bisection width. -/
def machineExplicitOptimizerInitialWidthRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerInitialHighRawCode word)
      (machineOptimizerTwiceNSquareForWidthRawCode word))

theorem machineOptimizerObjectiveUpperRawCode_mem_FP :
    machineOptimizerObjectiveUpperRawCode ∈ FP := by
  simpa only [machineOptimizerObjectiveUpperRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerNBProductRawCode_mem_FP
        machineOptimizerDimensionRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerTwiceInnerRadiusRawCode_mem_FP :
    machineOptimizerTwiceInnerRadiusRawCode ∈ FP := by
  simpa only [machineOptimizerTwiceInnerRadiusRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
        machineExplicitOptimizerInnerRadiusRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineOptimizerMixRangeRawCode_mem_FP :
    machineOptimizerMixRangeRawCode ∈ FP := by
  simpa only [machineOptimizerMixRangeRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineExplicitOptimizerMixRawCode_mem_FP
      machineOptimizerObjectiveRangeRawCode_mem_FP)
    machineRawRatMulCode_mem_FP

theorem machineOptimizerSmoothingSlackRawCode_mem_FP :
    machineOptimizerSmoothingSlackRawCode ∈ FP := by
  simpa only [machineOptimizerSmoothingSlackRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerMixRangeRawCode_mem_FP
        machineOptimizerTwiceInnerRadiusRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerInitialHighRawCode_mem_FP :
    machineOptimizerInitialHighRawCode ∈ FP := by
  simpa only [machineOptimizerInitialHighRawCode] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerObjectiveUpperRawCode_mem_FP
      machineOptimizerSmoothingSlackRawCode_mem_FP)
    machineRawRatAddCode_mem_FP

theorem machineOptimizerTwiceNSquareForWidthRawCode_mem_FP :
    machineOptimizerTwiceNSquareForWidthRawCode ∈ FP := by
  simpa only [machineOptimizerTwiceNSquareForWidthRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
        machineOptimizerNSquareRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineExplicitOptimizerInitialWidthRawCode_mem_FP :
    machineExplicitOptimizerInitialWidthRawCode ∈ FP := by
  simpa only [machineExplicitOptimizerInitialWidthRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerInitialHighRawCode_mem_FP
        machineOptimizerTwiceNSquareForWidthRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

@[simp] theorem machineOptimizerObjectiveUpperRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerObjectiveUpperRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerObjectiveUpper n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerObjectiveUpperRawCode,
    machineOptimizerNBProductRawCode_encode,
    machineOptimizerDimensionRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerTwiceInnerRadiusRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTwiceInnerRadiusRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerTwiceInnerRadius n
          (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerTwiceInnerRadiusRawCode,
    machineExplicitOptimizerInnerRadiusRawCode_encode hn,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineOptimizerMixRangeRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerMixRangeRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        ((rawExplicitOptimizerMix n (rationalMatrixEntryBitBound A)).mul
          (rawOptimizerObjectiveRange n
            (rationalMatrixEntryBitBound A))) := by
  rw [machineOptimizerMixRangeRawCode,
    machineExplicitOptimizerMixRawCode_encode hn,
    machineOptimizerObjectiveRangeRawCode_encode,
    machineRawRatMulCode_encode]

@[simp] theorem machineOptimizerSmoothingSlackRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerSmoothingSlackRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerSmoothingSlack n
          (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerSmoothingSlackRawCode,
    machineOptimizerMixRangeRawCode_encode hn,
    machineOptimizerTwiceInnerRadiusRawCode_encode hn,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerInitialHighRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerInitialHighRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawOptimizerInitialHigh n (rationalMatrixEntryBitBound A)) := by
  rw [machineOptimizerInitialHighRawCode,
    machineOptimizerObjectiveUpperRawCode_encode,
    machineOptimizerSmoothingSlackRawCode_encode hn,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem machineOptimizerTwiceNSquareForWidthRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    machineOptimizerTwiceNSquareForWidthRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode (rawOptimizerTwiceNSquare n) := by
  rw [machineOptimizerTwiceNSquareForWidthRawCode,
    machineOptimizerNSquareRawCode_encode,
    machineRawRatMulCode_encode]
  rfl

@[simp] theorem machineExplicitOptimizerInitialWidthRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerInitialWidthRawCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rawRatBinaryCode
        (rawExplicitOptimizerInitialWidth n
          (rationalMatrixEntryBitBound A)) := by
  rw [machineExplicitOptimizerInitialWidthRawCode,
    machineOptimizerInitialHighRawCode_encode hn,
    machineOptimizerTwiceNSquareForWidthRawCode_encode,
    machineRawRatAddCode_encode]
  rfl

@[simp] theorem rawOptimizerObjectiveUpper_value (n B : ℕ) :
    (rawOptimizerObjectiveUpper n B).value = n * B + n := by
  simp [rawOptimizerObjectiveUpper]

@[simp] theorem rawOptimizerSmoothingSlack_value (n B : ℕ) :
    (rawOptimizerSmoothingSlack n B).value =
      (rawExplicitOptimizerMix n B).value *
        (rawOptimizerObjectiveRange n B).value +
      2 * (rawExplicitOptimizerInnerRadius n B).value := by
  simp [rawOptimizerSmoothingSlack, rawOptimizerTwiceInnerRadius,
    rawOptimizerTwo]

@[simp] theorem rawExplicitOptimizerInitialWidth_value (n B : ℕ) :
    (rawExplicitOptimizerInitialWidth n B).value =
      n * B + n +
        ((rawExplicitOptimizerMix n B).value *
          (rawOptimizerObjectiveRange n B).value +
        2 * (rawExplicitOptimizerInnerRadius n B).value) +
        2 * n ^ 2 := by
  simp [rawExplicitOptimizerInitialWidth, rawOptimizerInitialHigh,
    rawOptimizerTwiceNSquare, rawOptimizerNSquare,
    rawOptimizerDimension, rawOptimizerTwo]
  ring

theorem rawExplicitOptimizerInitialWidth_eq {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    (rawExplicitOptimizerInitialWidth (m + 1)
      (rationalMatrixEntryBitBound A)).value =
        explicitOptimizerInitialWidth A := by
  rcases rawExplicitOptimizerScales_value A with
    ⟨_, _, _, hmix, hradius⟩
  rw [rawExplicitOptimizerInitialWidth_value, hmix, hradius,
    rawOptimizerObjectiveRange_value]
  simp [explicitOptimizerInitialWidth, betheBisectionInitialHigh,
    betheNegativeObjectiveUpper, betheSmoothingSlack,
    betheNegativeObjectiveLower, rationalRegularizedObjectiveRange]

/-! ## Exact unary bisection count -/

/-- Normalizes the raw initial bisection width into a rational entry code. -/
def machineExplicitOptimizerInitialWidthEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineExplicitOptimizerInitialWidthRawCode word)

/-- Measures the encoded initial interval width with an optimizer entry-length ruler. -/
def machineExplicitOptimizerInitialWidthLengthRuler
    (word : List Bool) : List Bool :=
  machineOptimizerEntryLengthRuler
    (machineExplicitOptimizerInitialWidthEntryCode word)

/-- Concatenates the initial-width and gap length rulers with three extra bisection steps. -/
def machineExplicitOptimizerBisectionStepsRuler
    (word : List Bool) : List Bool :=
  machineExplicitOptimizerInitialWidthLengthRuler word ++
    (machineExplicitOptimizerGapLengthRuler word ++
      List.replicate 3 true)

theorem machineExplicitOptimizerInitialWidthEntryCode_mem_FP :
    machineExplicitOptimizerInitialWidthEntryCode ∈ FP := by
  simpa only [machineExplicitOptimizerInitialWidthEntryCode] using!
    machineCompose_mem_FP machineExplicitOptimizerInitialWidthRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineExplicitOptimizerInitialWidthLengthRuler_mem_FP :
    machineExplicitOptimizerInitialWidthLengthRuler ∈ FP := by
  simpa only [machineExplicitOptimizerInitialWidthLengthRuler] using!
    machineCompose_mem_FP
      machineExplicitOptimizerInitialWidthEntryCode_mem_FP
      machineOptimizerEntryLengthRuler_mem_FP

theorem machineExplicitOptimizerBisectionStepsRuler_mem_FP :
    machineExplicitOptimizerBisectionStepsRuler ∈ FP := by
  simpa only [machineExplicitOptimizerBisectionStepsRuler] using!
    machineAppend_mem_FP
      machineExplicitOptimizerInitialWidthLengthRuler_mem_FP
      (machineAppend_mem_FP machineExplicitOptimizerGapLengthRuler_mem_FP
        (machineConst_mem_FP (List.replicate 3 true)))

@[simp] theorem machineExplicitOptimizerInitialWidthEntryCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerInitialWidthEntryCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalEntryBinaryCode
        ((rawExplicitOptimizerInitialWidth n
          (rationalMatrixEntryBitBound A)).value) := by
  rw [machineExplicitOptimizerInitialWidthEntryCode,
    machineExplicitOptimizerInitialWidthRawCode_encode hn,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value]

@[simp] theorem machineExplicitOptimizerInitialWidthLengthRuler_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineExplicitOptimizerInitialWidthLengthRuler
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate
        (encodedBitLength ℚ
          ((rawExplicitOptimizerInitialWidth n
            (rationalMatrixEntryBitBound A)).value)) true := by
  rw [machineExplicitOptimizerInitialWidthLengthRuler,
    machineExplicitOptimizerInitialWidthEntryCode_encode hn,
    machineOptimizerEntryLengthRuler_encode]

@[simp] theorem machineExplicitOptimizerBisectionStepsRuler_encode
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    machineExplicitOptimizerBisectionStepsRuler
        (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩) =
      List.replicate (explicitOptimizerBisectionSteps A) true := by
  rw [machineExplicitOptimizerBisectionStepsRuler,
    machineExplicitOptimizerInitialWidthLengthRuler_encode (by omega),
    machineExplicitOptimizerGapLengthRuler_encode (by omega),
    rawExplicitOptimizerInitialWidth_eq]
  have hgap := (rawExplicitOptimizerScales_value A).2.2.1
  rw [hgap]
  simp only [← List.replicate_add, explicitOptimizerBisectionSteps]
  congr 1

end BeyondBethe
