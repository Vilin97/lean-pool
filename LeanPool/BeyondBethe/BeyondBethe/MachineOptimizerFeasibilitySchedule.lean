/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerBisectionSchedule

/-!
# Finite-word budget for one Bethe feasibility call

A feasibility-call word pairs the original matrix word with a raw rational
objective threshold.  This file computes the ellipsoid dimension, the exact
outer radius, and the exact call budget.  The final binary budget is expanded
to unary only behind a degree-eight guard built from the exact unary
dimension and the exact canonical bit lengths of both radii.
-/

namespace BeyondBethe

open Complexity

def optimizerFeasibilityCallCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) : List Bool :=
  pair (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)
    (rawRatBinaryCode upper)

def machineOptimizerFeasibilitySource (word : List Bool) : List Bool :=
  machinePairFirst word

def machineOptimizerFeasibilityUpperRawCode
    (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRawRatAbsCode (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode
    (machineIntegerNatAbsBits (machinePairFirst word)))
    (machinePairSecond word)

def rawRatAbs (q : RawRat) : RawRat :=
  ⟨q.num.natAbs, q.den, q.den_pos⟩

def machineOptimizerFeasibilityDimensionBits
    (word : List Bool) : List Bool :=
  machineOptimizerDimensionBits (machineOptimizerFeasibilitySource word)

def machineOptimizerFeasibilityReducedDimensionBits
    (word : List Bool) : List Bool :=
  machineBinarySubBits
    (pair (machineOptimizerFeasibilityDimensionBits word) [true])

def machineOptimizerFeasibilityReducedDimensionSquareBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityReducedDimensionBits word)
      (machineOptimizerFeasibilityReducedDimensionBits word))

def machineOptimizerFeasibilityEllipsoidDimensionBits
    (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerFeasibilityReducedDimensionSquareBits word) [true])

def machineOptimizerFeasibilityEllipsoidDimensionUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerFeasibilitySource word)
      (machineOptimizerFeasibilityEllipsoidDimensionBits word))

def machineOptimizerFeasibilityEllipsoidDimensionRawCode
    (word : List Bool) : List Bool :=
  pair (machineNaturalIntegerCode
    (machineOptimizerFeasibilityEllipsoidDimensionBits word)) [true]

def machineOptimizerFeasibilityInnerRadiusRawCode
    (word : List Bool) : List Bool :=
  machineExplicitOptimizerInnerRadiusRawCode
    (machineOptimizerFeasibilitySource word)

def machineOptimizerFeasibilityTwiceInnerRadiusRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode rawOptimizerTwo)
      (machineOptimizerFeasibilityInnerRadiusRawCode word))

def machineOptimizerFeasibilityOnePlusAbsUpperRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (rawRatBinaryCode rawOptimizerOne)
      (machineRawRatAbsCode
        (machineOptimizerFeasibilityUpperRawCode word)))

def machineOptimizerFeasibilityRadiusFactorRawCode
    (word : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineOptimizerFeasibilityOnePlusAbsUpperRawCode word)
      (machineOptimizerFeasibilityTwiceInnerRadiusRawCode word))

def machineOptimizerFeasibilityOuterRadiusRawCode
    (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineOptimizerFeasibilityEllipsoidDimensionRawCode word)
      (machineOptimizerFeasibilityRadiusFactorRawCode word))

/-! ## Polynomial-time closure of the radius computation -/

theorem machineOptimizerFeasibilitySource_mem_FP :
    machineOptimizerFeasibilitySource ∈ FP := machinePairFirst_mem_FP

theorem machineOptimizerFeasibilityUpperRawCode_mem_FP :
    machineOptimizerFeasibilityUpperRawCode ∈ FP := machinePairSecond_mem_FP

theorem machineRawRatAbsCode_mem_FP : machineRawRatAbsCode ∈ FP := by
  have habs := machineCompose_mem_FP machinePairFirst_mem_FP
    machineIntegerNatAbsBits_mem_FP
  have hnum := machineCompose_mem_FP habs machineNaturalIntegerCode_mem_FP
  simpa only [machineRawRatAbsCode] using!
    machinePair_mem_FP hnum machinePairSecond_mem_FP

theorem machineOptimizerFeasibilityDimensionBits_mem_FP :
    machineOptimizerFeasibilityDimensionBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityDimensionBits] using!
    machineCompose_mem_FP machineOptimizerFeasibilitySource_mem_FP
      machineOptimizerDimensionBits_mem_FP

theorem machineOptimizerFeasibilityReducedDimensionBits_mem_FP :
    machineOptimizerFeasibilityReducedDimensionBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityReducedDimensionBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityDimensionBits_mem_FP
        (machineConst_mem_FP [true]))
      machineBinarySubBits_mem_FP

theorem machineOptimizerFeasibilityReducedDimensionSquareBits_mem_FP :
    machineOptimizerFeasibilityReducedDimensionSquareBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityReducedDimensionSquareBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityReducedDimensionBits_mem_FP
        machineOptimizerFeasibilityReducedDimensionBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityEllipsoidDimensionBits_mem_FP :
    machineOptimizerFeasibilityEllipsoidDimensionBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityEllipsoidDimensionBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityReducedDimensionSquareBits_mem_FP
        (machineConst_mem_FP [true]))
      machineBinaryAddBits_mem_FP

theorem machineOptimizerFeasibilityEllipsoidDimensionUnary_mem_FP :
    machineOptimizerFeasibilityEllipsoidDimensionUnary ∈ FP := by
  simpa only [machineOptimizerFeasibilityEllipsoidDimensionUnary] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilitySource_mem_FP
        machineOptimizerFeasibilityEllipsoidDimensionBits_mem_FP)
      machineBoundedUnary_mem_FP

theorem machineOptimizerFeasibilityEllipsoidDimensionRawCode_mem_FP :
    machineOptimizerFeasibilityEllipsoidDimensionRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityEllipsoidDimensionRawCode] using!
    machinePair_mem_FP
      (machineCompose_mem_FP
        machineOptimizerFeasibilityEllipsoidDimensionBits_mem_FP
        machineNaturalIntegerCode_mem_FP)
      (machineConst_mem_FP [true])

theorem machineOptimizerFeasibilityInnerRadiusRawCode_mem_FP :
    machineOptimizerFeasibilityInnerRadiusRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityInnerRadiusRawCode] using!
    machineCompose_mem_FP machineOptimizerFeasibilitySource_mem_FP
      machineExplicitOptimizerInnerRadiusRawCode_mem_FP

theorem machineOptimizerFeasibilityTwiceInnerRadiusRawCode_mem_FP :
    machineOptimizerFeasibilityTwiceInnerRadiusRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityTwiceInnerRadiusRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawOptimizerTwo))
        machineOptimizerFeasibilityInnerRadiusRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

theorem machineOptimizerFeasibilityOnePlusAbsUpperRawCode_mem_FP :
    machineOptimizerFeasibilityOnePlusAbsUpperRawCode ∈ FP := by
  have habs := machineCompose_mem_FP
    machineOptimizerFeasibilityUpperRawCode_mem_FP machineRawRatAbsCode_mem_FP
  simpa only [machineOptimizerFeasibilityOnePlusAbsUpperRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode rawOptimizerOne)) habs)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerFeasibilityRadiusFactorRawCode_mem_FP :
    machineOptimizerFeasibilityRadiusFactorRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityRadiusFactorRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityOnePlusAbsUpperRawCode_mem_FP
        machineOptimizerFeasibilityTwiceInnerRadiusRawCode_mem_FP)
      machineRawRatAddCode_mem_FP

theorem machineOptimizerFeasibilityOuterRadiusRawCode_mem_FP :
    machineOptimizerFeasibilityOuterRadiusRawCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityOuterRadiusRawCode] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityEllipsoidDimensionRawCode_mem_FP
        machineOptimizerFeasibilityRadiusFactorRawCode_mem_FP)
      machineRawRatMulCode_mem_FP

/-! ## Exact radius semantics -/

@[simp] theorem machineOptimizerFeasibilitySource_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilitySource
        (optimizerFeasibilityCallCode A upper) =
      rationalMatrixBinaryEncoding.encode ⟨n, A⟩ := by
  simp [machineOptimizerFeasibilitySource, optimizerFeasibilityCallCode]

@[simp] theorem machineOptimizerFeasibilityUpperRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityUpperRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode upper := by
  simp [machineOptimizerFeasibilityUpperRawCode,
    optimizerFeasibilityCallCode]

@[simp] theorem machineRawRatAbsCode_encode (q : RawRat) :
    machineRawRatAbsCode (rawRatBinaryCode q) =
      rawRatBinaryCode (rawRatAbs q) := by
  rw [machineRawRatAbsCode, rawRatBinaryCode,
    machinePairFirst_pair, machineIntegerNatAbsBits_encode,
    machineNaturalIntegerCode_natBits, machinePairSecond_pair]
  rfl

@[simp] theorem rawRatAbs_value (q : RawRat) :
    (rawRatAbs q).value = abs q.value := by
  rw [rawRatAbs, RawRat.value, RawRat.value]
  rw [abs_div, abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  norm_cast

@[simp] theorem machineOptimizerFeasibilityDimensionBits_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityDimensionBits
        (optimizerFeasibilityCallCode A upper) = n.bits := by
  simp [machineOptimizerFeasibilityDimensionBits]

@[simp] theorem machineOptimizerFeasibilityReducedDimensionBits_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityReducedDimensionBits
        (optimizerFeasibilityCallCode A upper) = (n - 1).bits := by
  rw [machineOptimizerFeasibilityReducedDimensionBits,
    machineOptimizerFeasibilityDimensionBits_encode]
  exact machineBinarySubBits_pair_natBits n 1

@[simp] theorem
    machineOptimizerFeasibilityReducedDimensionSquareBits_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityReducedDimensionSquareBits
        (optimizerFeasibilityCallCode A upper) = ((n - 1) ^ 2).bits := by
  rw [machineOptimizerFeasibilityReducedDimensionSquareBits,
    machineOptimizerFeasibilityReducedDimensionBits_encode,
    machineBinaryMulBits_pair_natBits]
  congr 1
  ring

@[simp] theorem machineOptimizerFeasibilityEllipsoidDimensionBits_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityEllipsoidDimensionBits
        (optimizerFeasibilityCallCode A upper) =
      ((n - 1) ^ 2 + 1).bits := by
  have hone : ([true] : List Bool) = (1 : ℕ).bits := rfl
  rw [machineOptimizerFeasibilityEllipsoidDimensionBits,
    machineOptimizerFeasibilityReducedDimensionSquareBits_encode,
    hone,
    machineBinaryAddBits_pair_natBits]

theorem optimizerEllipsoidDimension_le_sourceLength {n : ℕ}
    (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) :
    (n - 1) ^ 2 + 1 ≤
      (rationalMatrixBinaryEncoding.encode ⟨n, A⟩).length := by
  have hsq : n ^ 2 ≤
      (rationalMatrixBinaryEncoding.encode ⟨n, A⟩).length := by
    let rows := rationalMatrixRows A
    let rowsCode := binaryListCode
      (binaryListCode rationalEntryBinaryCode) rows
    let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
    have hrowsCode :
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
          word.length := by
      change rowsCode.length ≤ (pair n.bits rowsCode).length
      simpa using! machinePairSecond_length_le (pair n.bits rowsCode)
    have hcount : n ^ 2 = (rows.map List.length).sum := by
      simp only [rows, rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
        Function.comp_apply, List.length_ofFn]
      simp
      ring
    rw [hcount]
    exact (rationalRowsEntryCount_le_codeLength rows).trans hrowsCode
  have hsmall : (n - 1) ^ 2 + 1 ≤ n ^ 2 := by
    have hnform : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    calc
      (n - 1) ^ 2 + 1 ≤ (n - 1 + 1) ^ 2 := by nlinarith
      _ = n ^ 2 := by rw [hnform]
  exact hsmall.trans hsq

@[simp] theorem machineOptimizerFeasibilityEllipsoidDimensionUnary_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityEllipsoidDimensionUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate ((n - 1) ^ 2 + 1) true := by
  rw [machineOptimizerFeasibilityEllipsoidDimensionUnary,
    machineOptimizerFeasibilitySource_encode,
    machineOptimizerFeasibilityEllipsoidDimensionBits_encode]
  exact machineBoundedUnary_encode_of_le _ _
    (optimizerEllipsoidDimension_le_sourceLength hn A)

@[simp] theorem
    machineOptimizerFeasibilityEllipsoidDimensionRawCode_encode
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (upper : RawRat) :
    machineOptimizerFeasibilityEllipsoidDimensionRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode (RawRat.ofNat ((n - 1) ^ 2 + 1)) := by
  rw [machineOptimizerFeasibilityEllipsoidDimensionRawCode,
    machineOptimizerFeasibilityEllipsoidDimensionBits_encode,
    machineNaturalIntegerCode_natBits]
  simp [RawRat.ofNat, rawRatBinaryCode]

@[simp] theorem machineOptimizerFeasibilityInnerRadiusRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInnerRadiusRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode
        (rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)) := by
  simp [machineOptimizerFeasibilityInnerRadiusRawCode,
    machineExplicitOptimizerInnerRadiusRawCode_encode hn]

@[simp] theorem machineOptimizerFeasibilityOuterRadiusRawCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityOuterRadiusRawCode
        (optimizerFeasibilityCallCode A upper) =
      rawRatBinaryCode
        ((RawRat.ofNat ((n - 1) ^ 2 + 1)).mul
          ((rawOptimizerOne.add (rawRatAbs upper)).add
            (rawOptimizerTwo.mul
              (rawExplicitOptimizerInnerRadius n
                (rationalMatrixEntryBitBound A))))) := by
  rw [machineOptimizerFeasibilityOuterRadiusRawCode,
    machineOptimizerFeasibilityEllipsoidDimensionRawCode_encode,
    machineOptimizerFeasibilityRadiusFactorRawCode,
    machineOptimizerFeasibilityOnePlusAbsUpperRawCode,
    machineOptimizerFeasibilityUpperRawCode_encode,
    machineRawRatAbsCode_encode, machineRawRatAddCode_encode,
    machineOptimizerFeasibilityTwiceInnerRadiusRawCode,
    machineOptimizerFeasibilityInnerRadiusRawCode_encode hn,
    machineRawRatMulCode_encode, machineRawRatAddCode_encode,
    machineRawRatMulCode_encode]

def rawOptimizerFeasibilityOuterRadius
    (n B : ℕ) (upper : RawRat) : RawRat :=
  (RawRat.ofNat ((n - 1) ^ 2 + 1)).mul
    ((rawOptimizerOne.add (rawRatAbs upper)).add
      (rawOptimizerTwo.mul (rawExplicitOptimizerInnerRadius n B)))

@[simp] theorem rawOptimizerFeasibilityOuterRadius_value
    (n B : ℕ) (upper : RawRat) :
    (rawOptimizerFeasibilityOuterRadius n B upper).value =
      (((n - 1) ^ 2 + 1 : ℕ) : ℚ) *
        (1 + abs upper.value +
          2 * (rawExplicitOptimizerInnerRadius n B).value) := by
  simp only [rawOptimizerFeasibilityOuterRadius, RawRat.value_mul,
    RawRat.value_add, RawRat.value_ofNat, rawRatAbs_value]
  norm_num [rawOptimizerOne, rawOptimizerTwo]

theorem rawOptimizerFeasibilityOuterRadius_eq {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (upper : RawRat) :
    (rawOptimizerFeasibilityOuterRadius (m + 1)
      (rationalMatrixEntryBitBound A) upper).value =
      betheEpigraphOuterRadius m upper.value
        (explicitOptimizerInnerRadius A) := by
  rw [rawOptimizerFeasibilityOuterRadius_value]
  have hradius := (rawExplicitOptimizerScales_value A).2.2.2.2
  rw [hradius]
  have hm : (m + 1 - 1) ^ 2 + 1 = m * m + 1 := by
    have : m + 1 - 1 = m := by omega
    rw [this, pow_two]
  rw [hm]
  simp only [betheEpigraphOuterRadius]
  push_cast
  rfl

/-! ## Exact encoded lengths and guarded budget -/

def machineOptimizerFeasibilityOuterRadiusEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerFeasibilityOuterRadiusRawCode word)

def machineOptimizerFeasibilityOuterRadiusLengthRuler
    (word : List Bool) : List Bool :=
  machineOptimizerEntryLengthRuler
    (machineOptimizerFeasibilityOuterRadiusEntryCode word)

def machineOptimizerFeasibilityInnerRadiusEntryCode
    (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineOptimizerFeasibilityInnerRadiusRawCode word)

def machineOptimizerFeasibilityInnerRadiusLengthRuler
    (word : List Bool) : List Bool :=
  machineOptimizerEntryLengthRuler
    (machineOptimizerFeasibilityInnerRadiusEntryCode word)

def machineOptimizerFeasibilityBudgetGuardSource
    (word : List Bool) : List Bool :=
  machineOptimizerFeasibilityEllipsoidDimensionUnary word ++
    (machineOptimizerFeasibilityOuterRadiusLengthRuler word ++
      machineOptimizerFeasibilityInnerRadiusLengthRuler word)

def machineOptimizerFeasibilityDBits (word : List Bool) : List Bool :=
  machineOptimizerFeasibilityEllipsoidDimensionBits word

def machineOptimizerFeasibilityDSquareBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityDBits word)
      (machineOptimizerFeasibilityDBits word))

def machineOptimizerFeasibilityDCubeBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityDSquareBits word)
      (machineOptimizerFeasibilityDBits word))

def machineOptimizerFeasibilityOuterLengthBits
    (word : List Bool) : List Bool :=
  machineLengthBits
    (machineOptimizerFeasibilityOuterRadiusLengthRuler word)

def machineOptimizerFeasibilityInnerLengthBits
    (word : List Bool) : List Bool :=
  machineLengthBits
    (machineOptimizerFeasibilityInnerRadiusLengthRuler word)

def machineOptimizerFeasibilityOuterLengthTimesDBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityOuterLengthBits word)
      (machineOptimizerFeasibilityDBits word))

def machineOptimizerFeasibilityInnerLengthTimesDBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityInnerLengthBits word)
      (machineOptimizerFeasibilityDBits word))

def machineOptimizerFeasibilityMFirstBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerFeasibilityDSquareBits word)
      (machineOptimizerFeasibilityOuterLengthTimesDBits word))

def machineOptimizerFeasibilityMSecondBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerFeasibilityMFirstBits word)
      (machineOptimizerFeasibilityInnerLengthTimesDBits word))

def machineOptimizerFeasibilityMBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineOptimizerFeasibilityMSecondBits word) [true])

def machineOptimizerFeasibilityThirtyTwoDCubeBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (32 : ℕ).bits (machineOptimizerFeasibilityDCubeBits word))

def machineOptimizerFeasibilityBudgetBits
    (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineOptimizerFeasibilityThirtyTwoDCubeBits word)
      (machineOptimizerFeasibilityMBits word))

def machineOptimizerFeasibilityBudgetGuard
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 3
    (machineOptimizerFeasibilityBudgetGuardSource word)

def machineOptimizerFeasibilityBudgetUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineOptimizerFeasibilityBudgetGuard word)
      (machineOptimizerFeasibilityBudgetBits word))

/-! All components above are fixed compositions of verified `FP` machines. -/

theorem machineOptimizerFeasibilityOuterRadiusEntryCode_mem_FP :
    machineOptimizerFeasibilityOuterRadiusEntryCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityOuterRadiusEntryCode] using!
    machineCompose_mem_FP machineOptimizerFeasibilityOuterRadiusRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerFeasibilityOuterRadiusLengthRuler_mem_FP :
    machineOptimizerFeasibilityOuterRadiusLengthRuler ∈ FP := by
  simpa only [machineOptimizerFeasibilityOuterRadiusLengthRuler] using!
    machineCompose_mem_FP
      machineOptimizerFeasibilityOuterRadiusEntryCode_mem_FP
      machineOptimizerEntryLengthRuler_mem_FP

theorem machineOptimizerFeasibilityInnerRadiusEntryCode_mem_FP :
    machineOptimizerFeasibilityInnerRadiusEntryCode ∈ FP := by
  simpa only [machineOptimizerFeasibilityInnerRadiusEntryCode] using!
    machineCompose_mem_FP machineOptimizerFeasibilityInnerRadiusRawCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

theorem machineOptimizerFeasibilityInnerRadiusLengthRuler_mem_FP :
    machineOptimizerFeasibilityInnerRadiusLengthRuler ∈ FP := by
  simpa only [machineOptimizerFeasibilityInnerRadiusLengthRuler] using!
    machineCompose_mem_FP
      machineOptimizerFeasibilityInnerRadiusEntryCode_mem_FP
      machineOptimizerEntryLengthRuler_mem_FP

theorem machineOptimizerFeasibilityBudgetGuardSource_mem_FP :
    machineOptimizerFeasibilityBudgetGuardSource ∈ FP := by
  simpa only [machineOptimizerFeasibilityBudgetGuardSource] using!
    machineAppend_mem_FP
      machineOptimizerFeasibilityEllipsoidDimensionUnary_mem_FP
      (machineAppend_mem_FP
        machineOptimizerFeasibilityOuterRadiusLengthRuler_mem_FP
        machineOptimizerFeasibilityInnerRadiusLengthRuler_mem_FP)

theorem machineOptimizerFeasibilityDBits_mem_FP :
    machineOptimizerFeasibilityDBits ∈ FP :=
  machineOptimizerFeasibilityEllipsoidDimensionBits_mem_FP

theorem machineOptimizerFeasibilityDSquareBits_mem_FP :
    machineOptimizerFeasibilityDSquareBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityDSquareBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityDBits_mem_FP
        machineOptimizerFeasibilityDBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityDCubeBits_mem_FP :
    machineOptimizerFeasibilityDCubeBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityDCubeBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityDSquareBits_mem_FP
        machineOptimizerFeasibilityDBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityOuterLengthBits_mem_FP :
    machineOptimizerFeasibilityOuterLengthBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityOuterLengthBits] using!
    machineCompose_mem_FP
      machineOptimizerFeasibilityOuterRadiusLengthRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineOptimizerFeasibilityInnerLengthBits_mem_FP :
    machineOptimizerFeasibilityInnerLengthBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityInnerLengthBits] using!
    machineCompose_mem_FP
      machineOptimizerFeasibilityInnerRadiusLengthRuler_mem_FP
      machineLengthBits_mem_FP

theorem machineOptimizerFeasibilityOuterLengthTimesDBits_mem_FP :
    machineOptimizerFeasibilityOuterLengthTimesDBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityOuterLengthTimesDBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityOuterLengthBits_mem_FP
        machineOptimizerFeasibilityDBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityInnerLengthTimesDBits_mem_FP :
    machineOptimizerFeasibilityInnerLengthTimesDBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityInnerLengthTimesDBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityInnerLengthBits_mem_FP
        machineOptimizerFeasibilityDBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityMFirstBits_mem_FP :
    machineOptimizerFeasibilityMFirstBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityMFirstBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityDSquareBits_mem_FP
        machineOptimizerFeasibilityOuterLengthTimesDBits_mem_FP)
      machineBinaryAddBits_mem_FP

theorem machineOptimizerFeasibilityMSecondBits_mem_FP :
    machineOptimizerFeasibilityMSecondBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityMSecondBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityMFirstBits_mem_FP
        machineOptimizerFeasibilityInnerLengthTimesDBits_mem_FP)
      machineBinaryAddBits_mem_FP

theorem machineOptimizerFeasibilityMBits_mem_FP :
    machineOptimizerFeasibilityMBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityMBits] using! machineCompose_mem_FP
    (machinePair_mem_FP machineOptimizerFeasibilityMSecondBits_mem_FP
      (machineConst_mem_FP [true]))
    machineBinaryAddBits_mem_FP

theorem machineOptimizerFeasibilityThirtyTwoDCubeBits_mem_FP :
    machineOptimizerFeasibilityThirtyTwoDCubeBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityThirtyTwoDCubeBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP (machineConst_mem_FP (32 : ℕ).bits)
        machineOptimizerFeasibilityDCubeBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityBudgetBits_mem_FP :
    machineOptimizerFeasibilityBudgetBits ∈ FP := by
  simpa only [machineOptimizerFeasibilityBudgetBits] using!
    machineCompose_mem_FP
      (machinePair_mem_FP
        machineOptimizerFeasibilityThirtyTwoDCubeBits_mem_FP
        machineOptimizerFeasibilityMBits_mem_FP)
      machineBinaryMulBits_mem_FP

theorem machineOptimizerFeasibilityBudgetGuard_mem_FP :
    machineOptimizerFeasibilityBudgetGuard ∈ FP := by
  simpa only [machineOptimizerFeasibilityBudgetGuard] using!
    machineCompose_mem_FP machineOptimizerFeasibilityBudgetGuardSource_mem_FP
      (machineIteratedBinaryWidth_mem_FP 3)

theorem machineOptimizerFeasibilityBudgetUnary_mem_FP :
    machineOptimizerFeasibilityBudgetUnary ∈ FP := by
  simpa only [machineOptimizerFeasibilityBudgetUnary] using!
    machineCompose_mem_FP
      (machinePair_mem_FP machineOptimizerFeasibilityBudgetGuard_mem_FP
        machineOptimizerFeasibilityBudgetBits_mem_FP)
      machineBoundedUnary_mem_FP

/-! ## Exact budget semantics and proof that the guard is inactive -/

@[simp] theorem machineOptimizerFeasibilityOuterRadiusEntryCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityOuterRadiusEntryCode
        (optimizerFeasibilityCallCode A upper) =
      rationalEntryBinaryCode
        ((rawOptimizerFeasibilityOuterRadius n
          (rationalMatrixEntryBitBound A) upper).value) := by
  rw [machineOptimizerFeasibilityOuterRadiusEntryCode,
    machineOptimizerFeasibilityOuterRadiusRawCode_encode hn,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value]
  rfl

@[simp] theorem machineOptimizerFeasibilityOuterRadiusLengthRuler_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityOuterRadiusLengthRuler
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (encodedBitLength ℚ
          ((rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value)) true := by
  rw [machineOptimizerFeasibilityOuterRadiusLengthRuler,
    machineOptimizerFeasibilityOuterRadiusEntryCode_encode hn,
    machineOptimizerEntryLengthRuler_encode]

@[simp] theorem machineOptimizerFeasibilityInnerRadiusEntryCode_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInnerRadiusEntryCode
        (optimizerFeasibilityCallCode A upper) =
      rationalEntryBinaryCode
        ((rawExplicitOptimizerInnerRadius n
          (rationalMatrixEntryBitBound A)).value) := by
  rw [machineOptimizerFeasibilityInnerRadiusEntryCode,
    machineOptimizerFeasibilityInnerRadiusRawCode_encode hn,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value]

@[simp] theorem machineOptimizerFeasibilityInnerRadiusLengthRuler_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityInnerRadiusLengthRuler
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (encodedBitLength ℚ
          ((rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value)) true := by
  rw [machineOptimizerFeasibilityInnerRadiusLengthRuler,
    machineOptimizerFeasibilityInnerRadiusEntryCode_encode hn,
    machineOptimizerEntryLengthRuler_encode]

@[simp] theorem machineOptimizerFeasibilityBudgetGuardSource_length_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    (machineOptimizerFeasibilityBudgetGuardSource
      (optimizerFeasibilityCallCode A upper)).length =
      ((n - 1) ^ 2 + 1) +
        encodedBitLength ℚ
          ((rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value) +
      encodedBitLength ℚ
          ((rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value) := by
  have hn1 : 1 ≤ n := by omega
  rw [machineOptimizerFeasibilityBudgetGuardSource,
    machineOptimizerFeasibilityEllipsoidDimensionUnary_encode hn,
    machineOptimizerFeasibilityOuterRadiusLengthRuler_encode hn1,
    machineOptimizerFeasibilityInnerRadiusLengthRuler_encode hn1]
  simp only [List.length_append, List.length_replicate]
  omega

@[simp] theorem machineOptimizerFeasibilityBudgetBits_encode
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityBudgetBits
        (optimizerFeasibilityCallCode A upper) =
      (32 * (((n - 1) ^ 2 + 1) ^ 3) *
        rationalBallDyadicExponent ((n - 1) ^ 2 + 1)
          ((rawOptimizerFeasibilityOuterRadius n
            (rationalMatrixEntryBitBound A) upper).value)
          ((rawExplicitOptimizerInnerRadius n
            (rationalMatrixEntryBitBound A)).value)).bits := by
  let word := optimizerFeasibilityCallCode A upper
  let d := (n - 1) ^ 2 + 1
  let LR := encodedBitLength ℚ
    ((rawOptimizerFeasibilityOuterRadius n
      (rationalMatrixEntryBitBound A) upper).value)
  let Lr := encodedBitLength ℚ
    ((rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value)
  have hd : machineOptimizerFeasibilityDBits word = d.bits := by
    simpa only [machineOptimizerFeasibilityDBits, word, d] using!
      machineOptimizerFeasibilityEllipsoidDimensionBits_encode A upper
  have hd2 : machineOptimizerFeasibilityDSquareBits word = (d ^ 2).bits := by
    rw [machineOptimizerFeasibilityDSquareBits, hd,
      machineBinaryMulBits_pair_natBits]
    simp only [pow_two]
  have hd3 : machineOptimizerFeasibilityDCubeBits word = (d ^ 3).bits := by
    rw [machineOptimizerFeasibilityDCubeBits, hd2, hd,
      machineBinaryMulBits_pair_natBits]
    simp only [pow_succ]
  have hLR : machineOptimizerFeasibilityOuterLengthBits word = LR.bits := by
    have hRuler : machineOptimizerFeasibilityOuterRadiusLengthRuler word =
        List.replicate LR true := by
      simpa only [word, LR] using!
        machineOptimizerFeasibilityOuterRadiusLengthRuler_encode hn A upper
    rw [machineOptimizerFeasibilityOuterLengthBits, hRuler,
      machineLengthBits_encode, List.length_replicate]
  have hLr : machineOptimizerFeasibilityInnerLengthBits word = Lr.bits := by
    have hRuler : machineOptimizerFeasibilityInnerRadiusLengthRuler word =
        List.replicate Lr true := by
      simpa only [word, Lr] using!
        machineOptimizerFeasibilityInnerRadiusLengthRuler_encode hn A upper
    rw [machineOptimizerFeasibilityInnerLengthBits, hRuler,
      machineLengthBits_encode, List.length_replicate]
  have hLRd : machineOptimizerFeasibilityOuterLengthTimesDBits word =
      (LR * d).bits := by
    rw [machineOptimizerFeasibilityOuterLengthTimesDBits, hLR, hd,
      machineBinaryMulBits_pair_natBits]
  have hLrd : machineOptimizerFeasibilityInnerLengthTimesDBits word =
      (Lr * d).bits := by
    rw [machineOptimizerFeasibilityInnerLengthTimesDBits, hLr, hd,
      machineBinaryMulBits_pair_natBits]
  have hM1 : machineOptimizerFeasibilityMFirstBits word =
      (d ^ 2 + LR * d).bits := by
    rw [machineOptimizerFeasibilityMFirstBits, hd2, hLRd,
      machineBinaryAddBits_pair_natBits]
  have hM2 : machineOptimizerFeasibilityMSecondBits word =
      (d ^ 2 + LR * d + Lr * d).bits := by
    rw [machineOptimizerFeasibilityMSecondBits, hM1, hLrd,
      machineBinaryAddBits_pair_natBits]
  have hone : ([true] : List Bool) = (1 : ℕ).bits := rfl
  have hM : machineOptimizerFeasibilityMBits word =
      (d ^ 2 + LR * d + Lr * d + 1).bits := by
    rw [machineOptimizerFeasibilityMBits, hM2, hone,
      machineBinaryAddBits_pair_natBits]
  have h32d3 : machineOptimizerFeasibilityThirtyTwoDCubeBits word =
      (32 * d ^ 3).bits := by
    rw [machineOptimizerFeasibilityThirtyTwoDCubeBits, hd3,
      machineBinaryMulBits_pair_natBits]
  rw [machineOptimizerFeasibilityBudgetBits, h32d3, hM,
    machineBinaryMulBits_pair_natBits]
  rfl

theorem optimizerFeasibilityBudget_le_guardPolynomial
    (d LR Lr : ℕ) :
    32 * d ^ 3 * (d ^ 2 + LR * d + Lr * d + 1) ≤
      certificateExpGuardWidth 3 (d + LR + Lr) := by
  let Q := d + LR + Lr
  have hd : d ≤ Q := by omega
  have hLR : LR ≤ Q := by omega
  have hLr : Lr ≤ Q := by omega
  have hM : d ^ 2 + LR * d + Lr * d + 1 ≤ 3 * Q ^ 2 + 1 := by
    nlinarith [Nat.mul_le_mul hd hd, Nat.mul_le_mul hLR hd,
      Nat.mul_le_mul hLr hd]
  have hbudget :
      32 * d ^ 3 * (d ^ 2 + LR * d + Lr * d + 1) ≤
        128 * (Q + 1) ^ 5 := by
    have hd3 : d ^ 3 ≤ (Q + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hM' : 3 * Q ^ 2 + 1 ≤ 4 * (Q + 1) ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul hd3 (hM.trans hM')]
  have hconst : 128 ≤ (Q + 16) ^ 3 := by
    have : 8 ≤ Q + 16 := by omega
    nlinarith [Nat.pow_le_pow_left this 3]
  have hq5 : (Q + 1) ^ 5 ≤ (Q + 16) ^ 5 :=
    Nat.pow_le_pow_left (by omega) 5
  have hpow : 128 * (Q + 1) ^ 5 ≤ (Q + 16) ^ 8 := by
    calc
      128 * (Q + 1) ^ 5 ≤ (Q + 16) ^ 3 * (Q + 16) ^ 5 :=
        Nat.mul_le_mul hconst hq5
      _ = (Q + 16) ^ 8 := by rw [← pow_add]
  exact hbudget.trans <| hpow.trans <| by
    simpa only [Q] using! certificateExpGuardWidth_pow_lower 2 Q

@[simp] theorem machineOptimizerFeasibilityBudgetUnary_encode
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityBudgetUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (32 * (((n - 1) ^ 2 + 1) ^ 3) *
          rationalBallDyadicExponent ((n - 1) ^ 2 + 1)
            ((rawOptimizerFeasibilityOuterRadius n
              (rationalMatrixEntryBitBound A) upper).value)
            ((rawExplicitOptimizerInnerRadius n
              (rationalMatrixEntryBitBound A)).value)) true := by
  let d := (n - 1) ^ 2 + 1
  let LR := encodedBitLength ℚ
    ((rawOptimizerFeasibilityOuterRadius n
      (rationalMatrixEntryBitBound A) upper).value)
  let Lr := encodedBitLength ℚ
    ((rawExplicitOptimizerInnerRadius n
      (rationalMatrixEntryBitBound A)).value)
  rw [machineOptimizerFeasibilityBudgetUnary,
    machineOptimizerFeasibilityBudgetBits_encode (by omega)]
  apply machineBoundedUnary_encode_of_le
  rw [machineOptimizerFeasibilityBudgetGuard,
    machineIteratedBinaryWidth_length,
    machineOptimizerFeasibilityBudgetGuardSource_length_encode hn]
  simpa only [d, LR, Lr, rationalBallDyadicExponent] using!
    optimizerFeasibilityBudget_le_guardPolynomial d LR Lr

theorem machineOptimizerFeasibilityBudgetUnary_eq_thresholdBudget
    {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (upper : RawRat) :
    machineOptimizerFeasibilityBudgetUnary
        (optimizerFeasibilityCallCode A upper) =
      List.replicate
        (betheThresholdFeasibilityBudget m upper.value
          (explicitOptimizerInnerRadius A)) true := by
  rw [machineOptimizerFeasibilityBudgetUnary_encode (by omega)]
  have hR := rawOptimizerFeasibilityOuterRadius_eq A upper
  have hr := (rawExplicitOptimizerScales_value A).2.2.2.2
  have hd : (m + 1 - 1) ^ 2 + 1 = m * m + 1 := by
    have : m + 1 - 1 = m := by omega
    rw [this, pow_two]
  simp only [betheThresholdFeasibilityBudget]
  rw [hd, hR, hr]

end BeyondBethe
