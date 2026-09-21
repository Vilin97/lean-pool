/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixSum
import LeanPool.BeyondBethe.BeyondBethe.MachineBoundedUnary

/-!
# A guarded unary dimension ruler

Several bounded loops execute once per row or column.  The binary dimension
cannot be expanded to unary on arbitrary strings, so the entire matrix word is
used as an explicit guard.  Canonical square-matrix encodings are long enough
to make this guard inactive.
-/

namespace BeyondBethe

open Complexity

def machineMatrixDimensionUnary (word : List Bool) : List Bool :=
  machineBoundedUnary (pair word (machineMatrixDimensionWord word))

theorem machineMatrixDimensionUnary_mem_FP :
    machineMatrixDimensionUnary ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP id_mem_FP
    machineMatrixDimensionWord_mem_FP
  simpa only [machineMatrixDimensionUnary] using
    machineCompose_mem_FP hpair machineBoundedUnary_mem_FP

theorem list_length_le_binaryListCode_length {α : Type*}
    (encode : α → List Bool) : ∀ xs : List α,
    xs.length ≤ (binaryListCode encode xs).length := by
  intro xs
  induction xs with
  | nil => simp [binaryListCode]
  | cons x xs ih =>
      simp only [List.length_cons, binaryListCode, pair_length]
      omega

theorem matrix_dimension_le_code_length {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    n ≤ (rationalMatrixBinaryEncoding.encode ⟨n, A⟩).length := by
  have hlist : n ≤ (rationalMatrixRows A).length := by
    simp [rationalMatrixRows]
  have hrows := list_length_le_binaryListCode_length
    (binaryListCode rationalEntryBinaryCode) (rationalMatrixRows A)
  have hcode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows A)).length ≤
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩).length := by
    calc
      _ = (machineMatrixRowsWord
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)).length := by
        simpa using congrArg List.length
          (machineMatrixRowsWord_encode A).symm
      _ ≤ _ := by
        simpa only [machineMatrixRowsWord] using machinePairSecond_length_le
          (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)
  exact hlist.trans (hrows.trans hcode)

@[simp] theorem machineMatrixDimensionUnary_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixDimensionUnary
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      List.replicate n true := by
  rw [machineMatrixDimensionUnary, machineMatrixDimensionWord_encode,
    machineBoundedUnary_encode_of_le]
  exact matrix_dimension_le_code_length A

end BeyondBethe
