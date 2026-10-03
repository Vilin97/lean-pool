/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineListUpdate
public import LeanPool.BeyondBethe.BeyondBethe.MachineNestedMatrixMemory
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare

/-!
# Boolean vector and matrix memory

Matching states use canonical right-nested lists of one-bit Boolean values.
The access and update routines below are compositions of the verified unary
list primitives.  The final routine queries the support graph of a rational
matrix without decoding the matrix into a Lean object.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encode one Boolean as a singleton word. -/
def boolElementCode (b : Bool) : List Bool := [b]

/-- Encode a Boolean vector as a binary list of singleton Boolean codes. -/
def boolVectorCode (v : List Bool) : List Bool :=
  binaryListCode boolElementCode v

/-- Encode a Boolean matrix as a binary list of encoded Boolean rows. -/
def boolMatrixCode (M : List (List Bool)) : List Bool :=
  binaryListCode boolVectorCode M

/-- Input: `pair indexUnary boolVectorCode`. -/
def machineBoolVectorEntryAtUnary (word : List Bool) : List Bool :=
  machineListIndex word

/-- Input: `pair indexUnary (pair replacementBit boolVectorCode)`. -/
def machineBoolVectorUpdateAtUnary (word : List Bool) : List Bool :=
  machineListUpdate word

theorem machineBoolVectorEntryAtUnary_mem_FP :
    machineBoolVectorEntryAtUnary ∈ Complexity.FP :=
  machineListIndex_mem_FP

theorem machineBoolVectorUpdateAtUnary_mem_FP :
    machineBoolVectorUpdateAtUnary ∈ Complexity.FP :=
  machineListUpdate_mem_FP

@[simp] theorem machineBoolVectorEntryAtUnary_encode
    (v : List Bool) (i : ℕ) (hi : i < v.length) :
    machineBoolVectorEntryAtUnary
        (pair (List.replicate i true) (boolVectorCode v)) = [v[i]] := by
  exact machineListIndex_binaryListCode boolElementCode v i hi

@[simp] theorem machineBoolVectorUpdateAtUnary_encode
    (v : List Bool) (i : ℕ) (replacement : Bool)
    (hi : i < v.length) :
    machineBoolVectorUpdateAtUnary
        (pair (List.replicate i true)
          (pair [replacement] (boolVectorCode v))) =
      boolVectorCode (v.set i replacement) := by
  exact machineListUpdate_binaryListCode boolElementCode v replacement i hi

/-- Input: `pair rowUnary (pair columnUnary boolMatrixCode)`. -/
def machineBoolMatrixEntryAtUnary (word : List Bool) : List Bool :=
  machineNestedMatrixEntryAtUnary word

theorem machineBoolMatrixEntryAtUnary_mem_FP :
    machineBoolMatrixEntryAtUnary ∈ Complexity.FP :=
  machineNestedMatrixEntryAtUnary_mem_FP

@[simp] theorem machineBoolMatrixEntryAtUnary_encode
    (M : List (List Bool)) (i j : ℕ)
    (hi : i < M.length) (hj : j < M[i].length) :
    machineBoolMatrixEntryAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true) (boolMatrixCode M))) =
      [M[i][j]] := by
  exact machineNestedMatrixEntryAtUnary_encode boolElementCode M i j hi hj

/-- Input:
`pair rowUnary (pair columnUnary (pair replacementBit boolMatrixCode))`. -/
def machineBoolMatrixUpdateAtUnary (word : List Bool) : List Bool :=
  machineNestedMatrixUpdateAtUnary word

theorem machineBoolMatrixUpdateAtUnary_mem_FP :
    machineBoolMatrixUpdateAtUnary ∈ Complexity.FP :=
  machineNestedMatrixUpdateAtUnary_mem_FP

@[simp] theorem machineBoolMatrixUpdateAtUnary_encode
    (M : List (List Bool)) (i j : ℕ) (replacement : Bool)
    (hi : i < M.length) (hj : j < M[i].length) :
    machineBoolMatrixUpdateAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true)
            (pair [replacement] (boolMatrixCode M)))) =
      boolMatrixCode (M.set i (M[i].set j replacement)) := by
  exact machineNestedMatrixUpdateAtUnary_encode boolElementCode M i j replacement hi hj

/-! ## Rational support queries -/

/-- Test equality of two encoded raw rationals by checking both order comparisons. -/
def machineRawRatEqBit (word : List Bool) : List Bool :=
  machineAndBit (machineRawRatLeBit word)
    (machineRawRatLeBit (pair (machinePairSecond word)
      (machinePairFirst word)))

/-- Negate the raw-rational equality test. -/
def machineRawRatNeBit (word : List Bool) : List Bool :=
  machineNotBit (machineRawRatEqBit word)

theorem machineRawRatEqBit_mem_FP :
    machineRawRatEqBit ∈ Complexity.FP := by
  have hswap := machinePair_mem_FP machinePairSecond_mem_FP
    machinePairFirst_mem_FP
  have hright := machineCompose_mem_FP hswap machineRawRatLeBit_mem_FP
  exact machineAndBit_mem_FP machineRawRatLeBit_mem_FP hright

theorem machineRawRatNeBit_mem_FP :
    machineRawRatNeBit ∈ Complexity.FP := by
  simpa only [machineRawRatNeBit] using!
    machineNotBit_mem_FP machineRawRatEqBit_mem_FP

@[simp] theorem machineRawRatEqBit_encode (q r : RawRat) :
    machineRawRatEqBit
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      [decide (q.value = r.value)] := by
  rw [machineRawRatEqBit, machineRawRatLeBit_encode]
  simp only [machinePairSecond_pair, machinePairFirst_pair,
    machineRawRatLeBit_encode, machineAndBit_one]
  apply congrArg singleton
  apply Bool.eq_iff_iff.mpr
  simp [le_antisymm_iff]

@[simp] theorem machineRawRatNeBit_encode (q r : RawRat) :
    machineRawRatNeBit
        (pair (rawRatBinaryCode q) (rawRatBinaryCode r)) =
      [decide (q.value ≠ r.value)] := by
  rw [machineRawRatNeBit, machineRawRatEqBit_encode, machineNotBit_one]
  by_cases h : q.value = r.value <;> simp [h]

/-- Input: `pair rowUnary (pair columnUnary rationalMatrixWord)`. -/
def machineRationalSupportBitAtUnary (word : List Bool) : List Bool :=
  let entry := machineMatrixEntryAtUnary word
  machineRawRatNeBit
    (pair entry (rawRatBinaryCode RawRat.zero))

theorem machineRationalSupportBitAtUnary_mem_FP :
    machineRationalSupportBitAtUnary ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixEntryAtUnary_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
  simpa only [machineRationalSupportBitAtUnary] using!
    machineCompose_mem_FP hpair machineRawRatNeBit_mem_FP

@[simp] theorem machineRationalSupportBitAtUnary_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    machineRationalSupportBitAtUnary
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalMatrixBinaryEncoding.encode ⟨n, A⟩))) =
      [decide (A i j ≠ 0)] := by
  rw [machineRationalSupportBitAtUnary,
    machineMatrixEntryAtUnary_encode]
  rw [← rawRatBinaryCode_rawRatOfRat, machineRawRatNeBit_encode]
  simp only [rawRatOfRat_value, RawRat.value_zero]

end BeyondBethe
