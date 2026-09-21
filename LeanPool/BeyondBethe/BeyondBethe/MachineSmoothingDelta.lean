/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineFactorial
import LeanPool.BeyondBethe.BeyondBethe.MachineLengthBits
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension
import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSupportProduct
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMin
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalPower

/-!
# The rational smoothing level as a finite-word function

The input is a pair consisting of an unreduced rational word for `chi` and a
canonical rational-matrix word.  We assemble

`min (1 / (2 * n)) (chi * supportFloor ^ n / (4 * n!))`

from the verified finite-word primitives.  The matrix dimension is first
converted to a guarded unary ruler; this same ruler drives both exponentiation
and factorial.  All intermediate rational words remain unreduced until the
final minimum has selected a branch, at which point the selected fraction is
canonically normalized.
-/

namespace BeyondBethe

open Complexity

def machineSmoothingChiRawCode (word : List Bool) : List Bool :=
  machinePairFirst word

def machineSmoothingMatrixCode (word : List Bool) : List Bool :=
  machinePairSecond word

def machineSmoothingDimensionRuler (word : List Bool) : List Bool :=
  machineMatrixDimensionUnary (machineSmoothingMatrixCode word)

def machineSmoothingDimensionRawCode (word : List Bool) : List Bool :=
  pair (false :: machineLengthBits (machineSmoothingDimensionRuler word))
    (1 : ℕ).bits

def machineSmoothingSupportRawCode (word : List Bool) : List Bool :=
  machineMatrixSupportRawCode (machineSmoothingMatrixCode word)

def machineSmoothingSupportPowerRawCode (word : List Bool) : List Bool :=
  machineRawRatPowerCode
    (pair (machineSmoothingDimensionRuler word)
      (machineSmoothingSupportRawCode word))

def machineSmoothingFactorialRawCode (word : List Bool) : List Bool :=
  machineFactorialRawRatCode (machineSmoothingDimensionRuler word)

def machineSmoothingFirstDenominatorRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode (RawRat.ofNat 2))
      (machineSmoothingDimensionRawCode word))

def machineSmoothingFirstRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (rawRatBinaryCode RawRat.one)
      (machineSmoothingFirstDenominatorRawCode word))

def machineSmoothingWeightedSupportRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (machineSmoothingChiRawCode word)
      (machineSmoothingSupportPowerRawCode word))

def machineSmoothingSecondDenominatorRawCode (word : List Bool) : List Bool :=
  machineRawRatMulCode
    (pair (rawRatBinaryCode (RawRat.ofNat 4))
      (machineSmoothingFactorialRawCode word))

def machineSmoothingSecondRawCode (word : List Bool) : List Bool :=
  machineRawRatDivCode
    (pair (machineSmoothingWeightedSupportRawCode word)
      (machineSmoothingSecondDenominatorRawCode word))

def machineSmoothingDeltaRawCode (word : List Bool) : List Bool :=
  machineRawRatMinCode
    (pair (machineSmoothingFirstRawCode word)
      (machineSmoothingSecondRawCode word))

def machineSmoothingDeltaCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineSmoothingDeltaRawCode word)

theorem machineSmoothingChiRawCode_mem_FP :
    machineSmoothingChiRawCode ∈ Complexity.FP := machinePairFirst_mem_FP

theorem machineSmoothingMatrixCode_mem_FP :
    machineSmoothingMatrixCode ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineSmoothingDimensionRuler_mem_FP :
    machineSmoothingDimensionRuler ∈ Complexity.FP := by
  simpa only [machineSmoothingDimensionRuler] using
    machineCompose_mem_FP machineSmoothingMatrixCode_mem_FP
      machineMatrixDimensionUnary_mem_FP

theorem machineSmoothingDimensionRawCode_mem_FP :
    machineSmoothingDimensionRawCode ∈ Complexity.FP := by
  have hbits := machineCompose_mem_FP
    machineSmoothingDimensionRuler_mem_FP machineLengthBits_mem_FP
  have hnum := machineCompose_mem_FP hbits (machinePrepend_mem_FP false)
  exact machinePair_mem_FP hnum (machineConst_mem_FP (1 : ℕ).bits)

theorem machineSmoothingSupportRawCode_mem_FP :
    machineSmoothingSupportRawCode ∈ Complexity.FP := by
  simpa only [machineSmoothingSupportRawCode] using
    machineCompose_mem_FP machineSmoothingMatrixCode_mem_FP
      machineMatrixSupportRawCode_mem_FP

theorem machineSmoothingSupportPowerRawCode_mem_FP :
    machineSmoothingSupportPowerRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSmoothingDimensionRuler_mem_FP
    machineSmoothingSupportRawCode_mem_FP
  simpa only [machineSmoothingSupportPowerRawCode] using
    machineCompose_mem_FP hpair machineRawRatPowerCode_mem_FP

theorem machineSmoothingFactorialRawCode_mem_FP :
    machineSmoothingFactorialRawCode ∈ Complexity.FP := by
  simpa only [machineSmoothingFactorialRawCode] using
    machineCompose_mem_FP machineSmoothingDimensionRuler_mem_FP
      machineFactorialRawRatCode_mem_FP

theorem machineSmoothingFirstDenominatorRawCode_mem_FP :
    machineSmoothingFirstDenominatorRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (RawRat.ofNat 2)))
    machineSmoothingDimensionRawCode_mem_FP
  simpa only [machineSmoothingFirstDenominatorRawCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineSmoothingFirstRawCode_mem_FP :
    machineSmoothingFirstRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.one))
    machineSmoothingFirstDenominatorRawCode_mem_FP
  simpa only [machineSmoothingFirstRawCode] using
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineSmoothingWeightedSupportRawCode_mem_FP :
    machineSmoothingWeightedSupportRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSmoothingChiRawCode_mem_FP
    machineSmoothingSupportPowerRawCode_mem_FP
  simpa only [machineSmoothingWeightedSupportRawCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineSmoothingSecondDenominatorRawCode_mem_FP :
    machineSmoothingSecondDenominatorRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode (RawRat.ofNat 4)))
    machineSmoothingFactorialRawCode_mem_FP
  simpa only [machineSmoothingSecondDenominatorRawCode] using
    machineCompose_mem_FP hpair machineRawRatMulCode_mem_FP

theorem machineSmoothingSecondRawCode_mem_FP :
    machineSmoothingSecondRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineSmoothingWeightedSupportRawCode_mem_FP
    machineSmoothingSecondDenominatorRawCode_mem_FP
  simpa only [machineSmoothingSecondRawCode] using
    machineCompose_mem_FP hpair machineRawRatDivCode_mem_FP

theorem machineSmoothingDeltaRawCode_mem_FP :
    machineSmoothingDeltaRawCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineSmoothingFirstRawCode_mem_FP
    machineSmoothingSecondRawCode_mem_FP
  simpa only [machineSmoothingDeltaRawCode] using
    machineCompose_mem_FP hpair machineRawRatMinCode_mem_FP

theorem machineSmoothingDeltaCode_mem_FP :
    machineSmoothingDeltaCode ∈ Complexity.FP := by
  simpa only [machineSmoothingDeltaCode] using
    machineCompose_mem_FP machineSmoothingDeltaRawCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

/-! ## Exact semantics on canonical inputs -/

@[simp] theorem machineSmoothingDimensionRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingDimensionRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode (RawRat.ofNat n) := by
  simp [machineSmoothingDimensionRawCode, machineSmoothingDimensionRuler,
    machineSmoothingMatrixCode, rawRatBinaryCode, RawRat.ofNat,
    integerBinaryCode]

@[simp] theorem machineSmoothingSupportRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingSupportRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode
        (rawRatRowsSupportProduct RawRat.one (rationalMatrixRows A)) := by
  simp [machineSmoothingSupportRawCode, machineSmoothingMatrixCode]

@[simp] theorem machineSmoothingSupportPowerRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingSupportPowerRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode
        ((rawRatRowsSupportProduct RawRat.one
          (rationalMatrixRows A)).pow n) := by
  rw [machineSmoothingSupportPowerRawCode,
    machineSmoothingDimensionRuler, machineSmoothingMatrixCode,
    machinePairSecond_pair, machineMatrixDimensionUnary_encode,
    machineSmoothingSupportRawCode_encode,
    machineRawRatPowerCode_encode]

@[simp] theorem machineSmoothingFactorialRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingFactorialRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode (RawRat.ofNat n.factorial) := by
  simp [machineSmoothingFactorialRawCode, machineSmoothingDimensionRuler,
    machineSmoothingMatrixCode]

def rawRationalSmoothingFirst (n : ℕ) : RawRat :=
  RawRat.one.div ((RawRat.ofNat 2).mul (RawRat.ofNat n))

def rawRationalSmoothingSecond {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) : RawRat :=
  (χ.mul ((rawRatRowsSupportProduct RawRat.one
    (rationalMatrixRows A)).pow n)).div
      ((RawRat.ofNat 4).mul (RawRat.ofNat n.factorial))

def rawRationalSmoothingDelta {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) : RawRat :=
  if (rawRationalSmoothingFirst n).value ≤
      (rawRationalSmoothingSecond A χ).value then
    rawRationalSmoothingFirst n
  else
    rawRationalSmoothingSecond A χ

@[simp] theorem machineSmoothingDeltaRawCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingDeltaRawCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rawRatBinaryCode (rawRationalSmoothingDelta A χ) := by
  simp only [machineSmoothingDeltaRawCode,
    machineSmoothingFirstRawCode,
    machineSmoothingFirstDenominatorRawCode,
    machineSmoothingSecondRawCode,
    machineSmoothingWeightedSupportRawCode,
    machineSmoothingSecondDenominatorRawCode,
    machineSmoothingChiRawCode, machinePairFirst_pair,
    machineSmoothingDimensionRawCode_encode,
    machineSmoothingSupportPowerRawCode_encode,
    machineSmoothingFactorialRawCode_encode,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode,
    machineRawRatMinCode_encode, rawRationalSmoothingDelta,
    rawRationalSmoothingFirst, rawRationalSmoothingSecond]

theorem rawRationalSmoothingDelta_value {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    (rawRationalSmoothingDelta A χ).value =
      rationalSmoothingDelta A χ.value := by
  simp only [rawRationalSmoothingDelta, rawRationalSmoothingFirst,
    rawRationalSmoothingSecond, RawRat.value_div, RawRat.value_mul,
    RawRat.value_pow, RawRat.value_ofNat, RawRat.value_one,
    rawRatRowsSupportProduct_eq_rationalSupportFloor,
    rationalSmoothingDelta]
  norm_num only [Nat.cast_ofNat]
  by_cases h :
      1 / ((2 : ℚ) * n) ≤
        χ.value * rationalSupportFloor A ^ n /
          ((4 : ℚ) * n.factorial)
  · rw [if_pos h, min_eq_left h]
    simp
  · have hright :
        χ.value * rationalSupportFloor A ^ n /
            ((4 : ℚ) * n.factorial) ≤
          1 / ((2 : ℚ) * n) := le_of_not_ge h
    rw [if_neg h, min_eq_right hright]
    simp [rawRatRowsSupportProduct_eq_rationalSupportFloor]

theorem machineSmoothingDeltaCode_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : RawRat) :
    machineSmoothingDeltaCode
        (pair (rawRatBinaryCode χ)
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalBinaryCode (rationalSmoothingDelta A χ.value) := by
  simp only [machineSmoothingDeltaCode, machineSmoothingDeltaRawCode,
    machineSmoothingFirstRawCode,
    machineSmoothingFirstDenominatorRawCode,
    machineSmoothingSecondRawCode,
    machineSmoothingWeightedSupportRawCode,
    machineSmoothingSecondDenominatorRawCode,
    machineSmoothingChiRawCode, machinePairFirst_pair,
    machineSmoothingDimensionRawCode_encode,
    machineSmoothingSupportPowerRawCode_encode,
    machineSmoothingFactorialRawCode_encode,
    machineRawRatMulCode_encode, machineRawRatDivCode_encode,
    machineRawRatMinCode_encode,
    machineNormalizeRawRatBinaryCode_encode,
    binaryNormalizeRawRat_eq_value, rationalSmoothingDelta,
    RawRat.value_div, RawRat.value_mul, RawRat.value_pow,
    RawRat.value_ofNat, RawRat.value_one,
    rawRatRowsSupportProduct_eq_rationalSupportFloor]
  norm_num only [Nat.cast_ofNat]
  by_cases h :
      1 / ((2 : ℚ) * n) ≤
        χ.value * rationalSupportFloor A ^ n /
          ((4 : ℚ) * n.factorial)
  · rw [if_pos h, min_eq_left h]
    simp
  · have hright :
        χ.value * rationalSupportFloor A ^ n /
            ((4 : ℚ) * n.factorial) ≤
          1 / ((2 : ℚ) * n) := le_of_not_ge h
    rw [if_neg h, min_eq_right hright]
    simp [rawRatRowsSupportProduct_eq_rationalSupportFloor]

@[simp] theorem machineSmoothingDeltaCode_rational {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (χ : ℚ) :
    machineSmoothingDeltaCode
        (pair (rawRatBinaryCode (rawRatOfRat χ))
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)) =
      rationalBinaryCode (rationalSmoothingDelta A χ) := by
  rw [machineSmoothingDeltaCode_encode, rawRatOfRat_value]

end BeyondBethe
