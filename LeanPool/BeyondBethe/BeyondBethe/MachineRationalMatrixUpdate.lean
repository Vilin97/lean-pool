/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineListUpdate
import Mathlib.Tactic

/-!
# Mutable rational-matrix memory

The input is `pair rowUnary (pair columnUnary (pair replacement matrixWord))`.
The replacement is already a canonical rational-entry code.  The routine
updates the selected entry of the right-nested row-major matrix encoding and
preserves the original binary dimension word.
-/

namespace BeyondBethe

open Complexity

def machineRationalMatrixUpdateRow (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRationalMatrixUpdateRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRationalMatrixUpdateColumn (word : List Bool) : List Bool :=
  machinePairFirst (machineRationalMatrixUpdateRest word)

def machineRationalMatrixUpdatePayload (word : List Bool) : List Bool :=
  machinePairSecond (machineRationalMatrixUpdateRest word)

def machineRationalMatrixUpdateReplacement (word : List Bool) : List Bool :=
  machinePairFirst (machineRationalMatrixUpdatePayload word)

def machineRationalMatrixUpdateMatrix (word : List Bool) : List Bool :=
  machinePairSecond (machineRationalMatrixUpdatePayload word)

def machineRationalMatrixUpdateRows (word : List Bool) : List Bool :=
  machineMatrixRowsWord (machineRationalMatrixUpdateMatrix word)

def machineRationalMatrixUpdateCurrentRow (word : List Bool) : List Bool :=
  machineListIndex
    (pair (machineRationalMatrixUpdateRow word)
      (machineRationalMatrixUpdateRows word))

def machineRationalMatrixUpdateNewRow (word : List Bool) : List Bool :=
  machineListUpdate
    (pair (machineRationalMatrixUpdateColumn word)
      (pair (machineRationalMatrixUpdateReplacement word)
        (machineRationalMatrixUpdateCurrentRow word)))

def machineRationalMatrixUpdateNewRows (word : List Bool) : List Bool :=
  machineListUpdate
    (pair (machineRationalMatrixUpdateRow word)
      (pair (machineRationalMatrixUpdateNewRow word)
        (machineRationalMatrixUpdateRows word)))

def machineRationalMatrixUpdateAtUnary (word : List Bool) : List Bool :=
  pair (machineMatrixDimensionWord (machineRationalMatrixUpdateMatrix word))
    (machineRationalMatrixUpdateNewRows word)

theorem machineRationalMatrixUpdateRow_mem_FP :
    machineRationalMatrixUpdateRow ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineRationalMatrixUpdateRest_mem_FP :
    machineRationalMatrixUpdateRest ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineRationalMatrixUpdateColumn_mem_FP :
    machineRationalMatrixUpdateColumn ∈ Complexity.FP := by
  simpa only [machineRationalMatrixUpdateColumn] using
    machineCompose_mem_FP machineRationalMatrixUpdateRest_mem_FP
      machinePairFirst_mem_FP

theorem machineRationalMatrixUpdatePayload_mem_FP :
    machineRationalMatrixUpdatePayload ∈ Complexity.FP := by
  simpa only [machineRationalMatrixUpdatePayload] using
    machineCompose_mem_FP machineRationalMatrixUpdateRest_mem_FP
      machinePairSecond_mem_FP

theorem machineRationalMatrixUpdateReplacement_mem_FP :
    machineRationalMatrixUpdateReplacement ∈ Complexity.FP := by
  simpa only [machineRationalMatrixUpdateReplacement] using
    machineCompose_mem_FP machineRationalMatrixUpdatePayload_mem_FP
      machinePairFirst_mem_FP

theorem machineRationalMatrixUpdateMatrix_mem_FP :
    machineRationalMatrixUpdateMatrix ∈ Complexity.FP := by
  simpa only [machineRationalMatrixUpdateMatrix] using
    machineCompose_mem_FP machineRationalMatrixUpdatePayload_mem_FP
      machinePairSecond_mem_FP

theorem machineRationalMatrixUpdateRows_mem_FP :
    machineRationalMatrixUpdateRows ∈ Complexity.FP := by
  simpa only [machineRationalMatrixUpdateRows] using
    machineCompose_mem_FP machineRationalMatrixUpdateMatrix_mem_FP
      machineMatrixRowsWord_mem_FP

theorem machineRationalMatrixUpdateCurrentRow_mem_FP :
    machineRationalMatrixUpdateCurrentRow ∈ Complexity.FP := by
  have hinput := machinePair_mem_FP machineRationalMatrixUpdateRow_mem_FP
    machineRationalMatrixUpdateRows_mem_FP
  simpa only [machineRationalMatrixUpdateCurrentRow] using
    machineCompose_mem_FP hinput machineListIndex_mem_FP

theorem machineRationalMatrixUpdateNewRow_mem_FP :
    machineRationalMatrixUpdateNewRow ∈ Complexity.FP := by
  have hpayload := machinePair_mem_FP
    machineRationalMatrixUpdateReplacement_mem_FP
    machineRationalMatrixUpdateCurrentRow_mem_FP
  have hinput := machinePair_mem_FP machineRationalMatrixUpdateColumn_mem_FP
    hpayload
  simpa only [machineRationalMatrixUpdateNewRow] using
    machineCompose_mem_FP hinput machineListUpdate_mem_FP

theorem machineRationalMatrixUpdateNewRows_mem_FP :
    machineRationalMatrixUpdateNewRows ∈ Complexity.FP := by
  have hpayload := machinePair_mem_FP machineRationalMatrixUpdateNewRow_mem_FP
    machineRationalMatrixUpdateRows_mem_FP
  have hinput := machinePair_mem_FP machineRationalMatrixUpdateRow_mem_FP
    hpayload
  simpa only [machineRationalMatrixUpdateNewRows] using
    machineCompose_mem_FP hinput machineListUpdate_mem_FP

theorem machineRationalMatrixUpdateAtUnary_mem_FP :
    machineRationalMatrixUpdateAtUnary ∈ Complexity.FP := by
  have hdimension := machineCompose_mem_FP
    machineRationalMatrixUpdateMatrix_mem_FP machineMatrixDimensionWord_mem_FP
  exact machinePair_mem_FP hdimension
    machineRationalMatrixUpdateNewRows_mem_FP

/-! ## Exact semantics -/

def rationalRowsWord (dimension : List Bool)
    (rows : List (List ℚ)) : List Bool :=
  pair dimension
    (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)

@[simp] theorem machineMatrixDimensionWord_rationalRowsWord
    (dimension : List Bool) (rows : List (List ℚ)) :
    machineMatrixDimensionWord (rationalRowsWord dimension rows) =
      dimension := by
  simp [machineMatrixDimensionWord, rationalRowsWord]

@[simp] theorem machineMatrixRowsWord_rationalRowsWord
    (dimension : List Bool) (rows : List (List ℚ)) :
    machineMatrixRowsWord (rationalRowsWord dimension rows) =
      binaryListCode (binaryListCode rationalEntryBinaryCode) rows := by
  simp [machineMatrixRowsWord, rationalRowsWord]

@[simp] theorem machineRationalMatrixUpdateAtUnary_rows
    (dimension : List Bool) (rows : List (List ℚ))
    (replacement : ℚ) (i j : ℕ)
    (hi : i < rows.length) (hj : j < rows[i].length) :
    machineRationalMatrixUpdateAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true)
            (pair (rationalEntryBinaryCode replacement)
              (rationalRowsWord dimension rows)))) =
      rationalRowsWord dimension
        (rows.set i (rows[i].set j replacement)) := by
  rw [machineRationalMatrixUpdateAtUnary]
  simp only [machineRationalMatrixUpdateMatrix,
    machineRationalMatrixUpdatePayload, machineRationalMatrixUpdateRest,
    machineRationalMatrixUpdateRow, machineRationalMatrixUpdateColumn,
    machineRationalMatrixUpdateReplacement, machinePairFirst_pair,
    machinePairSecond_pair, machineMatrixDimensionWord_rationalRowsWord,
    machineRationalMatrixUpdateNewRows,
    machineRationalMatrixUpdateRows,
    machineMatrixRowsWord_rationalRowsWord,
    machineRationalMatrixUpdateNewRow,
    machineRationalMatrixUpdateCurrentRow]
  rw [machineListIndex_binaryListCode
    (binaryListCode rationalEntryBinaryCode) rows i hi]
  change pair dimension
      (machineListUpdate
        (pair (List.replicate i true)
          (pair
            (machineListUpdate
              (machineListUpdateCanonicalInput rationalEntryBinaryCode
                rows[i] replacement j))
            (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)))) = _
  rw [machineListUpdate_binaryListCode rationalEntryBinaryCode rows[i]
    replacement j hj]
  change pair dimension
      (machineListUpdate
        (machineListUpdateCanonicalInput
          (binaryListCode rationalEntryBinaryCode) rows
          (rows[i].set j replacement) i)) = _
  rw [machineListUpdate_binaryListCode
    (binaryListCode rationalEntryBinaryCode) rows
    (rows[i].set j replacement) i hi]
  rfl

@[simp] theorem machineRationalMatrixUpdateAtUnary_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (replacement : ℚ) :
    machineRationalMatrixUpdateAtUnary
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (pair (rationalEntryBinaryCode replacement)
              (rationalMatrixBinaryEncoding.encode ⟨n, A⟩)))) =
      rationalRowsWord n.bits
        ((rationalMatrixRows A).set i.1
          (((rationalMatrixRows A)[i.1]'(by simp [rationalMatrixRows])).set
            j.1 replacement)) := by
  change machineRationalMatrixUpdateAtUnary
      (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true)
          (pair (rationalEntryBinaryCode replacement)
            (rationalRowsWord n.bits (rationalMatrixRows A))))) = _
  exact machineRationalMatrixUpdateAtUnary_rows n.bits
    (rationalMatrixRows A) replacement i.1 j.1
      (by simp [rationalMatrixRows]) (by simp [rationalMatrixRows])

end BeyondBethe
