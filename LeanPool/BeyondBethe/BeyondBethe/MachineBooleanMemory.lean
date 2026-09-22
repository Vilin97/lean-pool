/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineListUpdate
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare

/-!
# Boolean vector and matrix memory

Matching states use canonical right-nested lists of one-bit Boolean values.
The access and update routines below are compositions of the verified unary
list primitives.  The final routine queries the support graph of a rational
matrix without decoding the matrix into a Lean object.
-/

namespace BeyondBethe

open Complexity

def boolElementCode (b : Bool) : List Bool := [b]

def boolVectorCode (v : List Bool) : List Bool :=
  binaryListCode boolElementCode v

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
  let rowUnary := machinePairFirst word
  let rest := machinePairSecond word
  let columnUnary := machinePairFirst rest
  let matrixCode := machinePairSecond rest
  let rowCode := machineListIndex (pair rowUnary matrixCode)
  machineListIndex (pair columnUnary rowCode)

theorem machineBoolMatrixEntryAtUnary_mem_FP :
    machineBoolMatrixEntryAtUnary ∈ Complexity.FP := by
  have hrow : (fun word : List Bool => machinePairFirst word) ∈
      Complexity.FP := machinePairFirst_mem_FP
  have hrest : (fun word : List Bool => machinePairSecond word) ∈
      Complexity.FP := machinePairSecond_mem_FP
  have hcolumn :
      (fun word : List Bool => machinePairFirst (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrest machinePairFirst_mem_FP
  have hmatrix :
      (fun word : List Bool => machinePairSecond (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrest machinePairSecond_mem_FP
  have hrowPayload := machinePair_mem_FP hrow hmatrix
  have hrowCode := machineCompose_mem_FP hrowPayload machineListIndex_mem_FP
  have hentryPayload := machinePair_mem_FP hcolumn hrowCode
  simpa only [machineBoolMatrixEntryAtUnary] using!
    machineCompose_mem_FP hentryPayload machineListIndex_mem_FP

@[simp] theorem machineBoolMatrixEntryAtUnary_encode
    (M : List (List Bool)) (i j : ℕ)
    (hi : i < M.length) (hj : j < M[i].length) :
    machineBoolMatrixEntryAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true) (boolMatrixCode M))) =
      [M[i][j]] := by
  rw [machineBoolMatrixEntryAtUnary]
  simp only [machinePairFirst_pair, machinePairSecond_pair, boolMatrixCode]
  rw [machineListIndex_binaryListCode boolVectorCode M i hi]
  simp only [boolVectorCode]
  exact machineListIndex_binaryListCode boolElementCode M[i] j hj

/-- Input:
`pair rowUnary (pair columnUnary (pair replacementBit boolMatrixCode))`. -/
def machineBoolMatrixUpdateAtUnary (word : List Bool) : List Bool :=
  let rowUnary := machinePairFirst word
  let restOne := machinePairSecond word
  let columnUnary := machinePairFirst restOne
  let restTwo := machinePairSecond restOne
  let replacement := machinePairFirst restTwo
  let matrixCode := machinePairSecond restTwo
  let rowCode := machineListIndex (pair rowUnary matrixCode)
  let updatedRow := machineListUpdate
    (pair columnUnary (pair replacement rowCode))
  machineListUpdate (pair rowUnary (pair updatedRow matrixCode))

theorem machineBoolMatrixUpdateAtUnary_mem_FP :
    machineBoolMatrixUpdateAtUnary ∈ Complexity.FP := by
  have hrow : (fun word : List Bool => machinePairFirst word) ∈
      Complexity.FP := machinePairFirst_mem_FP
  have hrestOne : (fun word : List Bool => machinePairSecond word) ∈
      Complexity.FP := machinePairSecond_mem_FP
  have hcolumn :
      (fun word : List Bool => machinePairFirst (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrestOne machinePairFirst_mem_FP
  have hrestTwo :
      (fun word : List Bool => machinePairSecond (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrestOne machinePairSecond_mem_FP
  have hreplacement :
      (fun word : List Bool =>
        machinePairFirst (machinePairSecond (machinePairSecond word))) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrestTwo machinePairFirst_mem_FP
  have hmatrix :
      (fun word : List Bool =>
        machinePairSecond (machinePairSecond (machinePairSecond word))) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrestTwo machinePairSecond_mem_FP
  have hrowPayload := machinePair_mem_FP hrow hmatrix
  have hrowCode := machineCompose_mem_FP hrowPayload machineListIndex_mem_FP
  have hupdateRowPayload := machinePair_mem_FP hcolumn
    (machinePair_mem_FP hreplacement hrowCode)
  have hupdatedRow := machineCompose_mem_FP hupdateRowPayload
    machineListUpdate_mem_FP
  have hupdateMatrixPayload := machinePair_mem_FP hrow
    (machinePair_mem_FP hupdatedRow hmatrix)
  simpa only [machineBoolMatrixUpdateAtUnary] using!
    machineCompose_mem_FP hupdateMatrixPayload machineListUpdate_mem_FP

@[simp] theorem machineBoolMatrixUpdateAtUnary_encode
    (M : List (List Bool)) (i j : ℕ) (replacement : Bool)
    (hi : i < M.length) (hj : j < M[i].length) :
    machineBoolMatrixUpdateAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true)
            (pair [replacement] (boolMatrixCode M)))) =
      boolMatrixCode (M.set i (M[i].set j replacement)) := by
  rw [machineBoolMatrixUpdateAtUnary]
  simp only [machinePairFirst_pair, machinePairSecond_pair, boolMatrixCode]
  rw [machineListIndex_binaryListCode boolVectorCode M i hi]
  change machineListUpdate
    (pair (List.replicate i true)
      (pair
        (machineListUpdate
          (machineListUpdateCanonicalInput boolElementCode M[i]
            replacement j))
        (binaryListCode boolVectorCode M))) = _
  rw [machineListUpdate_binaryListCode boolElementCode M[i]
    replacement j hj]
  change machineListUpdate
    (machineListUpdateCanonicalInput boolVectorCode M
      (M[i].set j replacement) i) = _
  exact machineListUpdate_binaryListCode boolVectorCode M
    (M[i].set j replacement) i hi

/-! ## Rational support queries -/

def machineRawRatEqBit (word : List Bool) : List Bool :=
  machineAndBit (machineRawRatLeBit word)
    (machineRawRatLeBit (pair (machinePairSecond word)
      (machinePairFirst word)))

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
