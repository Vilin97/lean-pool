/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineListIndex
import LeanPool.BeyondBethe.BeyondBethe.MachineListUpdate

/-! # Machine Nested Matrix Memory -/

namespace BeyondBethe

open Complexity

/-!
# Generic finite-word memory for nested matrices

These accessors operate on a bare `binaryListCode (binaryListCode encode) M`.
They are independent of the element type and will be used for rational
ellipsoid bases as well as intermediate matrices.
-/

/-- Input: `pair rowUnary (pair columnUnary nestedMatrixCode)`. -/
def machineNestedMatrixEntryAtUnary (word : List Bool) : List Bool :=
  let rowUnary := machinePairFirst word
  let rest := machinePairSecond word
  let columnUnary := machinePairFirst rest
  let matrixCode := machinePairSecond rest
  let rowCode := machineListIndex (pair rowUnary matrixCode)
  machineListIndex (pair columnUnary rowCode)

/-- Input:
`pair rowUnary (pair columnUnary (pair replacement nestedMatrixCode))`. -/
def machineNestedMatrixUpdateAtUnary (word : List Bool) : List Bool :=
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

theorem machineNestedMatrixEntryAtUnary_mem_FP :
    machineNestedMatrixEntryAtUnary ∈ FP := by
  have hrow := machinePairFirst_mem_FP
  have hrest := machinePairSecond_mem_FP
  have hcolumn := machineCompose_mem_FP hrest machinePairFirst_mem_FP
  have hmatrix := machineCompose_mem_FP hrest machinePairSecond_mem_FP
  have hrowPayload := machinePair_mem_FP hrow hmatrix
  have hrowCode := machineCompose_mem_FP hrowPayload machineListIndex_mem_FP
  have hentryPayload := machinePair_mem_FP hcolumn hrowCode
  simpa only [machineNestedMatrixEntryAtUnary] using!
    machineCompose_mem_FP hentryPayload machineListIndex_mem_FP

theorem machineNestedMatrixUpdateAtUnary_mem_FP :
    machineNestedMatrixUpdateAtUnary ∈ FP := by
  have hrow := machinePairFirst_mem_FP
  have hrestOne := machinePairSecond_mem_FP
  have hcolumn := machineCompose_mem_FP hrestOne machinePairFirst_mem_FP
  have hrestTwo := machineCompose_mem_FP hrestOne machinePairSecond_mem_FP
  have hreplacement := machineCompose_mem_FP hrestTwo machinePairFirst_mem_FP
  have hmatrix := machineCompose_mem_FP hrestTwo machinePairSecond_mem_FP
  have hrowPayload := machinePair_mem_FP hrow hmatrix
  have hrowCode := machineCompose_mem_FP hrowPayload machineListIndex_mem_FP
  have hupdateRowPayload := machinePair_mem_FP hcolumn
    (machinePair_mem_FP hreplacement hrowCode)
  have hupdatedRow := machineCompose_mem_FP hupdateRowPayload
    machineListUpdate_mem_FP
  have hupdateMatrixPayload := machinePair_mem_FP hrow
    (machinePair_mem_FP hupdatedRow hmatrix)
  simpa only [machineNestedMatrixUpdateAtUnary] using!
    machineCompose_mem_FP hupdateMatrixPayload machineListUpdate_mem_FP

@[simp] theorem machineNestedMatrixEntryAtUnary_encode
    {α : Type*} (encode : α → List Bool) (M : List (List α))
    (i j : ℕ) (hi : i < M.length) (hj : j < M[i].length) :
    machineNestedMatrixEntryAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true)
            (binaryListCode (binaryListCode encode) M))) =
      encode M[i][j] := by
  rw [machineNestedMatrixEntryAtUnary]
  simp only [machinePairFirst_pair, machinePairSecond_pair]
  rw [machineListIndex_binaryListCode (binaryListCode encode) M i hi]
  exact machineListIndex_binaryListCode encode M[i] j hj

@[simp] theorem machineNestedMatrixUpdateAtUnary_encode
    {α : Type*} (encode : α → List Bool) (M : List (List α))
    (i j : ℕ) (replacement : α)
    (hi : i < M.length) (hj : j < M[i].length) :
    machineNestedMatrixUpdateAtUnary
        (pair (List.replicate i true)
          (pair (List.replicate j true)
            (pair (encode replacement)
              (binaryListCode (binaryListCode encode) M)))) =
      binaryListCode (binaryListCode encode)
        (M.set i (M[i].set j replacement)) := by
  rw [machineNestedMatrixUpdateAtUnary]
  simp only [machinePairFirst_pair, machinePairSecond_pair]
  rw [machineListIndex_binaryListCode (binaryListCode encode) M i hi]
  change machineListUpdate
    (pair (List.replicate i true)
      (pair
        (machineListUpdate
          (machineListUpdateCanonicalInput encode M[i] replacement j))
        (binaryListCode (binaryListCode encode) M))) = _
  rw [machineListUpdate_binaryListCode encode M[i] replacement j hj]
  change machineListUpdate
    (machineListUpdateCanonicalInput (binaryListCode encode) M
      (M[i].set j replacement) i) = _
  exact machineListUpdate_binaryListCode (binaryListCode encode) M
    (M[i].set j replacement) i hi

end BeyondBethe
