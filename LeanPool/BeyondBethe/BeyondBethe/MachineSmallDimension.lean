/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOutputEncoding

/-!
# Exact order-zero and order-one matrix branches

The completed permanent algorithm handles dimensions zero and one exactly.
This file realizes those branches directly from the canonical matrix code.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineMatrixDimensionZeroBit (word : List Bool) : List Bool :=
  machineBinaryNatEqBit
    (pair (machineMatrixDimensionWord word) [])

def machineMatrixDimensionOneBit (word : List Bool) : List Bool :=
  machineBinaryNatEqBit
    (pair (machineMatrixDimensionWord word) [true])

def machineMatrixFirstRowCode (word : List Bool) : List Bool :=
  machineListHead (machineMatrixRowsWord word)

def machineMatrixFirstEntryCode (word : List Bool) : List Bool :=
  machineListHead (machineMatrixFirstRowCode word)

def machineMatrixFirstEntryOutput (word : List Bool) : List Bool :=
  machineRationalBinaryCode (machineMatrixFirstEntryCode word)

def machineSmallDimensionPermanentCode (word : List Bool) : List Bool :=
  machineIfHead (machineMatrixDimensionZeroBit word)
    (rationalBinaryCode 1)
    (machineIfHead (machineMatrixDimensionOneBit word)
      (machineMatrixFirstEntryOutput word) [])

theorem machineMatrixDimensionZeroBit_mem_FP :
    machineMatrixDimensionZeroBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixDimensionWord_mem_FP
    (machineConst_mem_FP [])
  simpa only [machineMatrixDimensionZeroBit] using!
    machineCompose_mem_FP hpair machineBinaryNatEqBit_mem_FP

theorem machineMatrixDimensionOneBit_mem_FP :
    machineMatrixDimensionOneBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP machineMatrixDimensionWord_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineMatrixDimensionOneBit] using!
    machineCompose_mem_FP hpair machineBinaryNatEqBit_mem_FP

theorem machineMatrixFirstRowCode_mem_FP :
    machineMatrixFirstRowCode ∈ Complexity.FP := by
  simpa only [machineMatrixFirstRowCode, machineListHead] using!
    machineCompose_mem_FP machineMatrixRowsWord_mem_FP machinePairFirst_mem_FP

theorem machineMatrixFirstEntryCode_mem_FP :
    machineMatrixFirstEntryCode ∈ Complexity.FP := by
  simpa only [machineMatrixFirstEntryCode, machineListHead] using!
    machineCompose_mem_FP machineMatrixFirstRowCode_mem_FP
      machinePairFirst_mem_FP

theorem machineMatrixFirstEntryOutput_mem_FP :
    machineMatrixFirstEntryOutput ∈ Complexity.FP := by
  simpa only [machineMatrixFirstEntryOutput] using!
    machineCompose_mem_FP machineMatrixFirstEntryCode_mem_FP
      machineRationalBinaryCode_mem_FP

theorem machineSmallDimensionPermanentCode_mem_FP :
    machineSmallDimensionPermanentCode ∈ Complexity.FP := by
  have hone := machineIfHead_mem_FP machineMatrixDimensionOneBit_mem_FP
    machineMatrixFirstEntryOutput_mem_FP (machineConst_mem_FP [])
  exact machineIfHead_mem_FP machineMatrixDimensionZeroBit_mem_FP
    (machineConst_mem_FP (rationalBinaryCode 1)) hone

@[simp] theorem machineMatrixDimensionZeroBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixDimensionZeroBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [decide (n = 0)] := by
  rw [machineMatrixDimensionZeroBit, machineMatrixDimensionWord_encode,
    show ([] : List Bool) = (0 : ℕ).bits by rfl,
    machineBinaryNatEqBit_pair_natBits]
  simp

@[simp] theorem machineMatrixDimensionOneBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixDimensionOneBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [decide (n = 1)] := by
  rw [machineMatrixDimensionOneBit, machineMatrixDimensionWord_encode,
    show ([true] : List Bool) = (1 : ℕ).bits by rfl,
    machineBinaryNatEqBit_pair_natBits]

@[simp] theorem machineMatrixFirstRowCode_encode
    (A : Matrix (Fin 1) (Fin 1) ℚ) :
    machineMatrixFirstRowCode
        (rationalMatrixBinaryEncoding.encode ⟨1, A⟩) =
      binaryListCode rationalEntryBinaryCode [A 0 0] := by
  simp [machineMatrixFirstRowCode, rationalMatrixRows]

@[simp] theorem machineMatrixFirstEntryCode_encode
    (A : Matrix (Fin 1) (Fin 1) ℚ) :
    machineMatrixFirstEntryCode
        (rationalMatrixBinaryEncoding.encode ⟨1, A⟩) =
      rationalEntryBinaryCode (A 0 0) := by
  simp [machineMatrixFirstEntryCode]

@[simp] theorem machineMatrixFirstEntryOutput_encode
    (A : Matrix (Fin 1) (Fin 1) ℚ) :
    machineMatrixFirstEntryOutput
        (rationalMatrixBinaryEncoding.encode ⟨1, A⟩) =
      rationalBinaryCode (A 0 0) := by
  simp [machineMatrixFirstEntryOutput, machineRationalBinaryCode_encode]

theorem machineSmallDimensionPermanentCode_zero
    (A : Matrix (Fin 0) (Fin 0) ℚ) :
    machineSmallDimensionPermanentCode
        (rationalMatrixBinaryEncoding.encode ⟨0, A⟩) =
      rationalBinaryCode (Matrix.permanent A) := by
  simp [machineSmallDimensionPermanentCode, Matrix.permanent]

theorem machineSmallDimensionPermanentCode_one
    (A : Matrix (Fin 1) (Fin 1) ℚ) :
    machineSmallDimensionPermanentCode
        (rationalMatrixBinaryEncoding.encode ⟨1, A⟩) =
      rationalBinaryCode (Matrix.permanent A) := by
  simp [machineSmallDimensionPermanentCode, Matrix.permanent_fin_one]

theorem machineSmallDimensionPermanentCode_encode {n : ℕ}
    (hn : n < 2) (A : Matrix (Fin n) (Fin n) ℚ) :
    machineSmallDimensionPermanentCode
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      rationalBinaryCode (Matrix.permanent A) := by
  interval_cases n
  · exact machineSmallDimensionPermanentCode_zero A
  · exact machineSmallDimensionPermanentCode_one A

end BeyondBethe
