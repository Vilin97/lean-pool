/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineOptimizerCertificateBoundary
public import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum

/-!
# Polynomial-time rational-vector summation

Optimizer potentials are encoded as right-nested lists of canonical rational
entries.  We reuse the verified clamped matrix fold by presenting such a list
as a one-row nested list.  The semantic proof below is stated first for an
arbitrary rectangular list of rows; square matrices are not needed by the
fold itself.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineMatrixRawSumFinalState_rows_encode
    (rows : List (List ℚ)) :
    let word := pair []
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
    machineMatrixRawSumFinalState word =
      machineMatrixRawSumPack [] []
        (rawRatBinaryCode (rawRatRowsSum RawRat.zero rows))
        (machineMatrixRawSumInputBound word) := by
  let word := pair []
    (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
  let s : MatrixRawSumSemState := ⟨rows, [], RawRat.zero⟩
  have hrowsLength :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    simpa only [word] using! machinePairSecond_length_le word
  have hinv : MatrixRawSumSemInvariant (1 + word.length) s := by
    simp only [MatrixRawSumSemInvariant, s, rawRatListCost,
      List.map_nil, List.sum_nil, rawRatWidth_zero, Nat.add_zero]
    exact Nat.add_le_add_left
      ((rawRatRowsCost_le_codeLength rows).trans hrowsLength) 1
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length :=
    (binaryListCode_length_ge_work rows).trans hrowsLength
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  have hinit : machineMatrixRawSumInit word =
      matrixRawSumSemCode (machineMatrixRawSumInputBound word) s := by
    simp [machineMatrixRawSumInit, matrixRawSumSemCode, s, word,
      binaryListCode, machineMatrixRowsWord]
  change machineMatrixRawSumFinalState word = _
  rw [machineMatrixRawSumFinalState, hsplit, Function.iterate_add_apply,
    hinit, machineMatrixRawSumIterate_semantics word s hinv,
    matrixRawSumSem_processRows]
  simp only [matrixRawSumSemCode, binaryListCode]
  rw [machineMatrixRawSum_done_iterate]

@[simp] theorem machineMatrixRawSumCode_rows_encode
    (rows : List (List ℚ)) :
    machineMatrixRawSumCode
        (pair []
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)) =
      rawRatBinaryCode (rawRatRowsSum RawRat.zero rows) := by
  rw [machineMatrixRawSumCode,
    machineMatrixRawSumFinalState_rows_encode]
  simp

/-- View a canonical rational-vector word as the only row of a nested row
list.  The unused matrix-dimension component is the empty word. -/
def machineRationalVectorAsRowsWord (word : List Bool) : List Bool :=
  pair [] (pair word [])

def machineRationalVectorRawSumCode (word : List Bool) : List Bool :=
  machineMatrixRawSumCode (machineRationalVectorAsRowsWord word)

theorem machineRationalVectorAsRowsWord_mem_FP :
    machineRationalVectorAsRowsWord ∈ Complexity.FP := by
  exact machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP id_mem_FP (machineConst_mem_FP []))

theorem machineRationalVectorRawSumCode_mem_FP :
    machineRationalVectorRawSumCode ∈ Complexity.FP := by
  simpa only [machineRationalVectorRawSumCode] using!
    machineCompose_mem_FP machineRationalVectorAsRowsWord_mem_FP
      machineMatrixRawSumCode_mem_FP

@[simp] theorem machineRationalVectorRawSumCode_encode {n : ℕ}
    (v : Fin n → ℚ) :
    machineRationalVectorRawSumCode (rationalVectorBinaryCode v) =
      rawRatBinaryCode
        (rawRatListSum RawRat.zero (List.ofFn v)) := by
  rw [machineRationalVectorRawSumCode,
    machineRationalVectorAsRowsWord, rationalVectorBinaryCode]
  change machineMatrixRawSumCode
      (pair []
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          [List.ofFn v])) = _
  rw [machineMatrixRawSumCode_rows_encode]
  rfl

theorem rawRatListSum_ofFn_value {n : ℕ} (v : Fin n → ℚ) :
    (rawRatListSum RawRat.zero (List.ofFn v)).value = ∑ i, v i := by
  rw [rawRatListSum_value, RawRat.value_zero, zero_add]
  exact List.sum_ofFn

theorem machineRationalVectorRawSumCode_value {n : ℕ}
    (v : Fin n → ℚ) :
    RawRat.value (rawRatListSum RawRat.zero (List.ofFn v)) = ∑ i, v i :=
  rawRatListSum_ofFn_value v

end BeyondBethe
