/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineMatrixDimension

/-!
# Indexed access to right-nested machine lists

The index is supplied in unary.  This is the representation used by all
bounded row, column, and coordinate loops below: its length is the number of
list tails to take.  The routine is total on arbitrary strings and its state
only shrinks, so its global polynomial-time bound does not depend on the input
being a well-formed list code.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the unary index ruler from a list-index request. -/
def machineListIndexRuler (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the encoded list from a list-index request. -/
def machineListIndexData (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Drops as many encoded list entries as the length of the unary index ruler. -/
def machineListIndexFinalState (word : List Bool) : List Bool :=
  (machineListTail)^[(machineListIndexRuler word).length]
    (machineListIndexData word)

/-- Return the code of the element at the unary index, or the empty word if
the index is outside the encoded list. -/
def machineListIndex (word : List Bool) : List Bool :=
  machineListHead (machineListIndexFinalState word)

theorem machineListIndexRuler_mem_FP :
    machineListIndexRuler ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineListIndexData_mem_FP :
    machineListIndexData ∈ Complexity.FP :=
  machinePairSecond_mem_FP

theorem machineListTail_length_le (word : List Bool) :
    (machineListTail word).length ≤ word.length := by
  simpa only [machineListTail] using! machinePairSecond_length_le word

theorem machineListTail_iterate_length_le (word : List Bool) : ∀ k,
    ((machineListTail)^[k] word).length ≤ word.length := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (machineListTail_length_le _).trans ih

theorem machineListIndexIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineListIndexRuler word).length) :
    ((machineListTail)^[iterations]
      (machineListIndexData word)).length ≤ word.length := by
  exact (machineListTail_iterate_length_le
    (machineListIndexData word) iterations).trans
      (machinePairSecond_length_le word)

theorem machineListIndexFinalState_mem_FP :
    machineListIndexFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineListTail_mem_FP
    machineListIndexData_mem_FP machineListIndexRuler_mem_FP id_mem_FP
    machineListIndexIterate_length_le_width

theorem machineListIndex_mem_FP :
    machineListIndex ∈ Complexity.FP := by
  simpa only [machineListIndex] using!
    machineCompose_mem_FP machineListIndexFinalState_mem_FP
      machineListHead_mem_FP

theorem machineListIndex_length_le_data (word : List Bool) :
    (machineListIndex word).length ≤ (machineListIndexData word).length := by
  rw [machineListIndex]
  exact (machinePairFirst_length_le (machineListIndexFinalState word)).trans
    (machineListTail_iterate_length_le (machineListIndexData word)
      (machineListIndexRuler word).length)

/-! ## Exact semantics -/

theorem machineListTail_iterate_binaryListCode
    {α : Type*} (encode : α → List Bool) : ∀ (xs : List α) (k : ℕ),
    (machineListTail)^[k] (binaryListCode encode xs) =
      binaryListCode encode (xs.drop k) := by
  intro xs k
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      cases xs with
      | nil =>
          have htail : machineListTail [] = [] := by
            rfl
          simpa [binaryListCode] using! ih ([] : List α)
      | cons x xs =>
          rw [machineListTail_cons, ih]
          rfl

theorem machineListIndex_binaryListCode
    {α : Type*} (encode : α → List Bool)
    (xs : List α) (k : ℕ) (hk : k < xs.length) :
    machineListIndex
        (pair (List.replicate k true) (binaryListCode encode xs)) =
      encode xs[k] := by
  rw [machineListIndex, machineListIndexFinalState,
    machineListIndexRuler, machinePairFirst_pair, List.length_replicate,
    machineListIndexData, machinePairSecond_pair,
    machineListTail_iterate_binaryListCode]
  rw [List.drop_eq_getElem_cons hk]
  exact machineListHead_cons encode xs[k] (xs.drop (k + 1))

/-- Read a matrix entry using unary row and column indices.  The input is
`pair rowUnary (pair columnUnary matrixCode)`. -/
def machineMatrixEntryAtUnary (word : List Bool) : List Bool :=
  let rowUnary := machinePairFirst word
  let rest := machinePairSecond word
  let columnUnary := machinePairFirst rest
  let matrixWord := machinePairSecond rest
  let rowCode := machineListIndex
    (pair rowUnary (machineMatrixRowsWord matrixWord))
  machineListIndex (pair columnUnary rowCode)

theorem machineMatrixEntryAtUnary_mem_FP :
    machineMatrixEntryAtUnary ∈ Complexity.FP := by
  have hrowUnary : (fun word : List Bool => machinePairFirst word) ∈
      Complexity.FP := machinePairFirst_mem_FP
  have hrest : (fun word : List Bool => machinePairSecond word) ∈
      Complexity.FP := machinePairSecond_mem_FP
  have hcolumnUnary :
      (fun word : List Bool => machinePairFirst (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrest machinePairFirst_mem_FP
  have hmatrixWord :
      (fun word : List Bool => machinePairSecond (machinePairSecond word)) ∈
        Complexity.FP :=
    machineCompose_mem_FP hrest machinePairSecond_mem_FP
  have hrows :
      (fun word : List Bool =>
        machineMatrixRowsWord (machinePairSecond (machinePairSecond word))) ∈
        Complexity.FP :=
    machineCompose_mem_FP hmatrixWord machineMatrixRowsWord_mem_FP
  have hrowPayload := machinePair_mem_FP hrowUnary hrows
  have hrowCode := machineCompose_mem_FP hrowPayload machineListIndex_mem_FP
  have hentryPayload := machinePair_mem_FP hcolumnUnary hrowCode
  simpa only [machineMatrixEntryAtUnary] using!
    machineCompose_mem_FP hentryPayload machineListIndex_mem_FP

@[simp] theorem machineMatrixEntryAtUnary_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    machineMatrixEntryAtUnary
        (pair (List.replicate i.1 true)
          (pair (List.replicate j.1 true)
            (rationalMatrixBinaryEncoding.encode ⟨n, A⟩))) =
      rationalEntryBinaryCode (A i j) := by
  rw [machineMatrixEntryAtUnary]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineMatrixRowsWord_encode]
  rw [machineListIndex_binaryListCode]
  · rw [machineListIndex_binaryListCode]
    · simp [rationalMatrixRows, List.getElem_ofFn]
    · simp [rationalMatrixRows]
  · simp [rationalMatrixRows]

end BeyondBethe
