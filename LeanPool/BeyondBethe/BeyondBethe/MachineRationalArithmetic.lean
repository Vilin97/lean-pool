/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineIntegerArithmetic

/-!
# Polynomial-time rational addition and multiplication

The input is a pair of unreduced rational encodings.  Addition forms the two
cross-products and multiplication forms the two direct products.  Both public
operations then invoke the separately verified gcd normalizer, so no use of
Lean's built-in rational arithmetic is hidden in the machine implementation.
-/

namespace BeyondBethe

open Complexity

def machineRawLeftNumeratorCode (word : List Bool) : List Bool :=
  machinePairFirst (machinePairFirst word)

def machineRawLeftDenominatorBits (word : List Bool) : List Bool :=
  machinePairSecond (machinePairFirst word)

def machineRawRightNumeratorCode (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond word)

def machineRawRightDenominatorBits (word : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond word)

/-- Regard canonical natural-number bits as a nonnegative integer code. -/
def machineNaturalIntegerCode (word : List Bool) : List Bool :=
  false :: word

def machineRawAddLeftScaledNumerator (word : List Bool) : List Bool :=
  machineIntegerMulCode
    (pair (machineRawLeftNumeratorCode word)
      (machineNaturalIntegerCode (machineRawRightDenominatorBits word)))

def machineRawAddRightScaledNumerator (word : List Bool) : List Bool :=
  machineIntegerMulCode
    (pair (machineRawRightNumeratorCode word)
      (machineNaturalIntegerCode (machineRawLeftDenominatorBits word)))

def machineRawAddNumeratorCode (word : List Bool) : List Bool :=
  machineIntegerAddCode
    (pair (machineRawAddLeftScaledNumerator word)
      (machineRawAddRightScaledNumerator word))

def machineRawProductNumeratorCode (word : List Bool) : List Bool :=
  machineIntegerMulCode
    (pair (machineRawLeftNumeratorCode word)
      (machineRawRightNumeratorCode word))

def machineRawProductDenominatorBits (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineRawLeftDenominatorBits word)
      (machineRawRightDenominatorBits word))

/-- Unreduced output encoding for rational addition. -/
def machineRawRatAddCode (word : List Bool) : List Bool :=
  pair (machineRawAddNumeratorCode word)
    (machineRawProductDenominatorBits word)

/-- Unreduced output encoding for rational multiplication. -/
def machineRawRatMulCode (word : List Bool) : List Bool :=
  pair (machineRawProductNumeratorCode word)
    (machineRawProductDenominatorBits word)

/-- Canonical public rational encoding of the sum. -/
def machineRationalAddCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatAddCode word)

/-- Canonical public rational encoding of the product. -/
def machineRationalMulCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatBinaryCode (machineRawRatMulCode word)

theorem machineRawLeftNumeratorCode_mem_FP :
    machineRawLeftNumeratorCode ∈ Complexity.FP := by
  simpa only [machineRawLeftNumeratorCode] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machinePairFirst_mem_FP

theorem machineRawLeftDenominatorBits_mem_FP :
    machineRawLeftDenominatorBits ∈ Complexity.FP := by
  simpa only [machineRawLeftDenominatorBits] using!
    machineCompose_mem_FP machinePairFirst_mem_FP machinePairSecond_mem_FP

theorem machineRawRightNumeratorCode_mem_FP :
    machineRawRightNumeratorCode ∈ Complexity.FP := by
  simpa only [machineRawRightNumeratorCode] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRawRightDenominatorBits_mem_FP :
    machineRawRightDenominatorBits ∈ Complexity.FP := by
  simpa only [machineRawRightDenominatorBits] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineNaturalIntegerCode_mem_FP :
    machineNaturalIntegerCode ∈ Complexity.FP := by
  exact machinePrepend_mem_FP false

theorem machineRawAddLeftScaledNumerator_mem_FP :
    machineRawAddLeftScaledNumerator ∈ Complexity.FP := by
  have hden := machineCompose_mem_FP
    machineRawRightDenominatorBits_mem_FP machineNaturalIntegerCode_mem_FP
  have hpair := machinePair_mem_FP machineRawLeftNumeratorCode_mem_FP hden
  simpa only [machineRawAddLeftScaledNumerator] using!
    machineCompose_mem_FP hpair machineIntegerMulCode_mem_FP

theorem machineRawAddRightScaledNumerator_mem_FP :
    machineRawAddRightScaledNumerator ∈ Complexity.FP := by
  have hden := machineCompose_mem_FP
    machineRawLeftDenominatorBits_mem_FP machineNaturalIntegerCode_mem_FP
  have hpair := machinePair_mem_FP machineRawRightNumeratorCode_mem_FP hden
  simpa only [machineRawAddRightScaledNumerator] using!
    machineCompose_mem_FP hpair machineIntegerMulCode_mem_FP

theorem machineRawAddNumeratorCode_mem_FP :
    machineRawAddNumeratorCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    machineRawAddLeftScaledNumerator_mem_FP
    machineRawAddRightScaledNumerator_mem_FP
  simpa only [machineRawAddNumeratorCode] using!
    machineCompose_mem_FP hpair machineIntegerAddCode_mem_FP

theorem machineRawProductNumeratorCode_mem_FP :
    machineRawProductNumeratorCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineRawLeftNumeratorCode_mem_FP
    machineRawRightNumeratorCode_mem_FP
  simpa only [machineRawProductNumeratorCode] using!
    machineCompose_mem_FP hpair machineIntegerMulCode_mem_FP

theorem machineRawProductDenominatorBits_mem_FP :
    machineRawProductDenominatorBits ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineRawLeftDenominatorBits_mem_FP
    machineRawRightDenominatorBits_mem_FP
  simpa only [machineRawProductDenominatorBits] using!
    machineCompose_mem_FP hpair machineBinaryMulBits_mem_FP

theorem machineRawRatAddCode_mem_FP : machineRawRatAddCode ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRawAddNumeratorCode_mem_FP
    machineRawProductDenominatorBits_mem_FP

theorem machineRawRatMulCode_mem_FP : machineRawRatMulCode ∈ Complexity.FP := by
  exact machinePair_mem_FP machineRawProductNumeratorCode_mem_FP
    machineRawProductDenominatorBits_mem_FP

theorem machineRationalAddCode_mem_FP : machineRationalAddCode ∈ Complexity.FP := by
  simpa only [machineRationalAddCode] using!
    machineCompose_mem_FP machineRawRatAddCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

theorem machineRationalMulCode_mem_FP : machineRationalMulCode ∈ Complexity.FP := by
  simpa only [machineRationalMulCode] using!
    machineCompose_mem_FP machineRawRatMulCode_mem_FP
      machineNormalizeRawRatBinaryCode_mem_FP

@[simp] theorem machineNaturalIntegerCode_natBits (n : ℕ) :
    machineNaturalIntegerCode n.bits = integerBinaryCode (Int.ofNat n) := by
  rfl

@[simp] theorem machineRawLeftNumeratorCode_encode (q r : RawRat) :
    machineRawLeftNumeratorCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode q.num := by
  simp [machineRawLeftNumeratorCode, rawRatBinaryCode]

@[simp] theorem machineRawLeftDenominatorBits_encode (q r : RawRat) :
    machineRawLeftDenominatorBits
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) = q.den.bits := by
  simp [machineRawLeftDenominatorBits, rawRatBinaryCode]

@[simp] theorem machineRawRightNumeratorCode_encode (q r : RawRat) :
    machineRawRightNumeratorCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode r.num := by
  simp [machineRawRightNumeratorCode, rawRatBinaryCode]

@[simp] theorem machineRawRightDenominatorBits_encode (q r : RawRat) :
    machineRawRightDenominatorBits
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) = r.den.bits := by
  simp [machineRawRightDenominatorBits, rawRatBinaryCode]

theorem machineRawAddLeftScaledNumerator_encode (q r : RawRat) :
    machineRawAddLeftScaledNumerator
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode (q.num * (r.den : ℤ)) := by
  simp [machineRawAddLeftScaledNumerator,
    machineIntegerMulCode_encode]

theorem machineRawAddRightScaledNumerator_encode (q r : RawRat) :
    machineRawAddRightScaledNumerator
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode (r.num * (q.den : ℤ)) := by
  simp [machineRawAddRightScaledNumerator,
    machineIntegerMulCode_encode]

theorem machineRawAddNumeratorCode_encode (q r : RawRat) :
    machineRawAddNumeratorCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode
        (q.num * (r.den : ℤ) + r.num * (q.den : ℤ)) := by
  rw [machineRawAddNumeratorCode,
    machineRawAddLeftScaledNumerator_encode,
    machineRawAddRightScaledNumerator_encode,
    machineIntegerAddCode_encode]

theorem machineRawProductNumeratorCode_encode (q r : RawRat) :
    machineRawProductNumeratorCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      integerBinaryCode (q.num * r.num) := by
  simp [machineRawProductNumeratorCode, machineIntegerMulCode_encode]

theorem machineRawProductDenominatorBits_encode (q r : RawRat) :
    machineRawProductDenominatorBits
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      (q.den * r.den).bits := by
  simp [machineRawProductDenominatorBits,
    machineBinaryMulBits_pair_natBits]

theorem machineRawRatAddCode_encode (q r : RawRat) :
    machineRawRatAddCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rawRatBinaryCode (q.add r) := by
  rw [machineRawRatAddCode, machineRawAddNumeratorCode_encode,
    machineRawProductDenominatorBits_encode]
  rfl

theorem machineRawRatMulCode_encode (q r : RawRat) :
    machineRawRatMulCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rawRatBinaryCode (q.mul r) := by
  rw [machineRawRatMulCode, machineRawProductNumeratorCode_encode,
    machineRawProductDenominatorBits_encode]
  rfl

theorem machineRationalAddCode_encode (q r : RawRat) :
    machineRationalAddCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rationalBinaryCode (binaryNormalizeRawRat (q.add r)) := by
  rw [machineRationalAddCode, machineRawRatAddCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

theorem machineRationalMulCode_encode (q r : RawRat) :
    machineRationalMulCode
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      rationalBinaryCode (binaryNormalizeRawRat (q.mul r)) := by
  rw [machineRationalMulCode, machineRawRatMulCode_encode,
    machineNormalizeRawRatBinaryCode_encode]

end BeyondBethe
