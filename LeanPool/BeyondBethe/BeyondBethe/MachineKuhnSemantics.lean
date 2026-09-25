/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineKuhnStep
public import Mathlib.Tactic

/-!
# Correctness of one encoded Kuhn transition

The main theorem in this file shows that the un-clamped control computation is
exactly `kuhnEvalStep`.  Clamp inactivity and the bounded full run are proved
after the semantic size invariant.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

@[simp] theorem machineIfEmpty_binaryListCode_cons {α : Type*}
    (encode : α → List Bool) (x : α) (xs : List α)
    (whenEmpty whenNonempty : List Bool) :
    machineIfEmpty (binaryListCode encode (x :: xs))
        whenEmpty whenNonempty = whenNonempty := by
  exact machineIfEmpty_of_ne_nil _ _ _
    (binaryListCode_cons_ne_nil encode x xs)

@[simp] theorem machineIfEmpty_replicate_succ
    (n : ℕ) (bit : Bool) (whenEmpty whenNonempty : List Bool) :
    machineIfEmpty (List.replicate (n + 1) bit)
        whenEmpty whenNonempty = whenNonempty := by
  rw [show n + 1 = Nat.succ n by omega, List.replicate_succ]
  simp

@[simp] theorem machineIfEmpty_pair
    (left right whenEmpty whenNonempty : List Bool) :
    machineIfEmpty (pair left right) whenEmpty whenNonempty =
      whenNonempty := by
  apply machineIfEmpty_of_ne_nil
  intro h
  have hlen := congrArg List.length h
  simp at hlen

@[simp] theorem machineMateVectorUpdateSomeAtUnary_encode
    (mate : List (Option ℕ)) (column row : ℕ)
    (hcolumn : column < mate.length) :
    machineMateVectorUpdateAtUnary
        (pair (List.replicate column true)
          (pair (true :: List.replicate row true) (mateVectorCode mate))) =
      mateVectorCode (mate.set column (some row)) := by
  simpa [mateValueCode] using!
    machineMateVectorUpdateAtUnary_encode mate column (some row) hcolumn

@[simp] theorem seenBoolList_empty {n : ℕ} :
    seenBoolList (∅ : Finset (Fin n)) = List.replicate n false := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    simp [seenBoolList]

/-! ## Exact projections from semantic state codes -/

@[simp] theorem machineKuhnControl_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnControl (kuhnMachineStateCode A state) =
      kuhnControlCode state := by
  simp [machineKuhnControl, kuhnMachineStateCode]

@[simp] theorem machineKuhnMatrix_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnStateMatrix (kuhnMachineStateCode A state) =
      rationalMatrixBinaryEncoding.encode ⟨n, A⟩ := by
  simp [kuhnMachineStateCode]

@[simp] theorem machineKuhnDimension_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnStateDimension (kuhnMachineStateCode A state) =
      List.replicate n true := by
  simp [kuhnMachineStateCode]

@[simp] theorem machineKuhnColumns_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnStateColumns (kuhnMachineStateCode A state) =
      finRangeUnaryCode n := by
  simp [kuhnMachineStateCode]

@[simp] theorem machineKuhnFalseSeen_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnStateFalseSeen (kuhnMachineStateCode A state) =
      boolVectorCode (List.replicate n false) := by
  simp [kuhnMachineStateCode]

@[simp] theorem machineKuhnBound_stateCode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnStateBound (kuhnMachineStateCode A state) =
      machineKuhnInputBound (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) := by
  simp [kuhnMachineStateCode]

@[simp] theorem machineKuhnFuel_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnFuel (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) =
        List.replicate fuel true := by
  simp [machineKuhnFuel, kuhnControlCode]

@[simp] theorem machineKuhnRemaining_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnRemaining (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) =
        finListUnaryCode remaining := by
  simp [machineKuhnRemaining, kuhnControlCode]

@[simp] theorem machineKuhnRow_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnRow (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) = finUnaryCode row := by
  simp [machineKuhnRow, kuhnControlCode]

@[simp] theorem machineKuhnSeen_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnSeen (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) =
        boolVectorCode (seenBoolList seen) := by
  simp [machineKuhnSeen, kuhnControlCode]

@[simp] theorem machineKuhnMate_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnMate (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) =
        mateVectorCode (columnMateList mate) := by
  simp [machineKuhnMate, kuhnControlCode]

@[simp] theorem machineKuhnStack_encode_call {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnStack (kuhnMachineStateCode A
      (.call fuel remaining row seen mate stack)) = kuhnStackCode stack := by
  simp [machineKuhnStack, kuhnControlCode]

@[simp] theorem machineKuhnReturnFields_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (result : KuhnSearchResult n)
    (stack : List (KuhnFrame n)) :
    machineKuhnRetSuccess (kuhnMachineStateCode A (.ret result stack)) =
        [result.mate?.isSome] ∧
      machineKuhnRetSeen (kuhnMachineStateCode A (.ret result stack)) =
        boolVectorCode (seenBoolList result.seen) ∧
      machineKuhnRetMate (kuhnMachineStateCode A (.ret result stack)) =
        kuhnSearchResultMateCode result ∧
      machineKuhnRetStack (kuhnMachineStateCode A (.ret result stack)) =
        kuhnStackCode stack := by
  simp [machineKuhnRetSuccess, machineKuhnRetSeen, machineKuhnRetMate,
    machineKuhnRetStack, kuhnControlCode]

@[simp] theorem machineKuhnTopFrame_encode_ret_cons {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (result : KuhnSearchResult n)
    (frame : KuhnFrame n) (stack : List (KuhnFrame n)) :
    machineKuhnTopFrame
        (kuhnMachineStateCode A (.ret result (frame :: stack))) =
      kuhnFrameCode frame := by
  simp [machineKuhnTopFrame]

@[simp] theorem machineKuhnRestStack_encode_ret_cons {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (result : KuhnSearchResult n)
    (frame : KuhnFrame n) (stack : List (KuhnFrame n)) :
    machineKuhnRestStack
        (kuhnMachineStateCode A (.ret result (frame :: stack))) =
      kuhnStackCode stack := by
  simp [machineKuhnRestStack]

@[simp] theorem machineKuhnCurrentColumn_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnCurrentColumn (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        finUnaryCode col := by
  simp [machineKuhnCurrentColumn, finListUnaryCode]

@[simp] theorem machineKuhnRemainingTail_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnRemainingTail (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        finListUnaryCode remaining := by
  simp [machineKuhnRemainingTail, finListUnaryCode]

/-! ## Exact memory operations -/

@[simp] theorem machineKuhnSeenBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnSeenBit (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        [decide (col ∈ seen)] := by
  rw [machineKuhnSeenBit, machineKuhnCurrentColumn_encode,
    machineKuhnSeen_encode_call, finUnaryCode,
    machineBoolVectorEntryAtUnary_encode (seenBoolList seen) col.1
      (by simp)]
  congr 2
  exact seenBoolList_getElem seen col.1 (by simp)

@[simp] theorem machineKuhnSupportBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnSupportBit (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        [decide (A row col ≠ 0)] := by
  rw [machineKuhnSupportBit, machineKuhnRow_encode_call,
    machineKuhnCurrentColumn_encode, machineKuhnMatrix_stateCode]
  simp only [finUnaryCode]
  rw [machineRationalSupportBitAtUnary_encode]

@[simp] theorem machineKuhnSeenUpdated_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnSeenUpdated (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        boolVectorCode (seenBoolList (insert col seen)) := by
  rw [machineKuhnSeenUpdated, machineKuhnCurrentColumn_encode,
    machineKuhnSeen_encode_call, finUnaryCode,
    machineBoolVectorUpdateAtUnary_encode (seenBoolList seen) col.1 true
      (by simp), ← seenBoolList_insert]

@[simp] theorem machineKuhnMateValue_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnMateValue (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        mateValueCode ((mate col).map Fin.val) := by
  rw [machineKuhnMateValue, machineKuhnCurrentColumn_encode,
    machineKuhnMate_encode_call, finUnaryCode,
    machineMateVectorGetAtUnary_encode (columnMateList mate) col.1 (by simp)]
  congr 1
  exact columnMateList_getElem mate col.1 (by simp)

@[simp] theorem machineKuhnMateSetCurrent_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnMateSetCurrent (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        mateVectorCode
          (columnMateList (Function.update mate col (some row))) := by
  rw [machineKuhnMateSetCurrent, machineKuhnCurrentColumn_encode,
    machineKuhnSomeCurrentRow, machineKuhnRow_encode_call,
    machineKuhnMate_encode_call]
  simp only [finUnaryCode]
  change machineMateVectorUpdateAtUnary
      (pair (List.replicate col.1 true)
        (pair (mateValueCode (some row.1))
          (mateVectorCode (columnMateList mate)))) = _
  rw [machineMateVectorUpdateAtUnary_encode (columnMateList mate) col.1
    (some row.1) (by simp), columnMateList_update]
  simp

@[simp] theorem machineKuhnMateClearCurrent_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ) (col : Fin n)
    (remaining : List (Fin n)) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) (stack : List (KuhnFrame n)) :
    machineKuhnMateClearCurrent (kuhnMachineStateCode A
      (.call fuel (col :: remaining) row seen mate stack)) =
        mateVectorCode (columnMateList (Function.update mate col none)) := by
  rw [machineKuhnMateClearCurrent, machineKuhnCurrentColumn_encode,
    machineKuhnMate_encode_call]
  simp only [finUnaryCode]
  change machineMateVectorUpdateAtUnary
      (pair (List.replicate col.1 true)
        (pair (mateValueCode none) (mateVectorCode (columnMateList mate)))) = _
  rw [machineMateVectorUpdateAtUnary_encode (columnMateList mate) col.1 none
    (by simp), columnMateList_update]
  simp

/-! ## Un-clamped transition correctness -/

theorem machineKuhnNextControl_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (state : KuhnEvalState n) :
    machineKuhnNextControl (kuhnMachineStateCode A state) =
      kuhnControlCode (kuhnEvalStep A state) := by
  cases state with
  | done mate =>
      simp [machineKuhnNextControl, machineKuhnDoneControl,
        kuhnControlCode, kuhnEvalStep]
  | call fuel remaining row seen mate stack =>
      cases fuel with
      | zero =>
          simp [machineKuhnNextControl, machineKuhnCallControl,
            machineKuhnFailureControl, kuhnControlCode, kuhnEvalStep,
            kuhnSearchResultMateCode]
      | succ fuel =>
          cases remaining with
          | nil =>
              simp [machineKuhnNextControl, machineKuhnCallControl,
                machineKuhnFailureControl, kuhnControlCode,
                kuhnEvalStep, kuhnSearchResultMateCode,
                finListUnaryCode, binaryListCode]
          | cons col remaining =>
              by_cases hskip : col ∈ seen ∨ A row col = 0
              · rcases hskip with hseen | hzero
                · simp [machineKuhnNextControl, machineKuhnCallControl,
                    machineKuhnNonterminalCallControl, machineKuhnSkipBit,
                    machineKuhnSkipControl, kuhnControlCode,
                    kuhnEvalStep, hseen, finListUnaryCode, binaryListCode]
                · have hsupport : decide (A row col ≠ 0) = false := by
                    simp [hzero]
                  simp [machineKuhnNextControl, machineKuhnCallControl,
                    machineKuhnNonterminalCallControl, machineKuhnSkipBit,
                    machineKuhnSkipControl, kuhnControlCode,
                    kuhnEvalStep, hzero,
                    finListUnaryCode, binaryListCode]
              · have hnotSeen : col ∉ seen := by aesop
                have hsupport : A row col ≠ 0 := by aesop
                cases hmate : mate col with
                | none =>
                    simp [machineKuhnNextControl, machineKuhnCallControl,
                      machineKuhnNonterminalCallControl, machineKuhnSkipBit,
                      machineKuhnProceedControl, machineKuhnMateIsNoneBit,
                      machineKuhnFreeColumnControl, kuhnControlCode,
                      kuhnEvalStep, kuhnSearchResultMateCode,
                      hnotSeen, hsupport, hmate,
                      finListUnaryCode, binaryListCode]
                | some oldRow =>
                    simp [machineKuhnNextControl, machineKuhnCallControl,
                      machineKuhnNonterminalCallControl, machineKuhnSkipBit,
                      machineKuhnProceedControl, machineKuhnMateIsNoneBit,
                      machineKuhnOccupiedColumnControl,
                      machineKuhnPushedSearchStack,
                      machineKuhnSearchFrameCurrent, kuhnControlCode,
                      kuhnEvalStep,
                      kuhnStackCode, hnotSeen, hsupport, hmate,
                      finRangeUnaryCode, finListUnaryCode, finUnaryCode,
                      machineKuhnStackPush, binaryListCode]
                    rfl
  | ret result stack =>
      cases stack with
      | nil =>
          simp [machineKuhnNextControl, machineKuhnReturnControl,
            kuhnControlCode, kuhnEvalStep, kuhnStackCode, binaryListCode]
      | cons frame stack =>
          cases frame with
          | search frame =>
              cases hmate : result.mate? with
              | none =>
                  simp [machineKuhnNextControl, machineKuhnReturnControl,
                    machineKuhnNonemptyReturnControl,
                    machineKuhnSearchReturnControl,
                    machineKuhnSearchReturnFailureControl,
                    kuhnControlCode, kuhnSearchResultMateCode,
                    kuhnFrameCode, kuhnStackCode, kuhnSearchFrameCode,
                    kuhnEvalStep, hmate, finListUnaryCode,
                    binaryListCode]
              | some mate' =>
                  simp [machineKuhnNextControl, machineKuhnReturnControl,
                    machineKuhnNonemptyReturnControl,
                    machineKuhnSearchReturnControl,
                    machineKuhnSearchReturnSuccessControl,
                    kuhnControlCode, kuhnSearchResultMateCode,
                    kuhnFrameCode, kuhnStackCode, kuhnSearchFrameCode,
                    kuhnEvalStep, hmate, columnMateList_update,
                    finUnaryCode, binaryListCode]
          | build frame =>
              rcases frame with ⟨rows, fallback⟩
              cases hmate : result.mate? with
              | none =>
                  cases rows with
                  | nil =>
                      simp [machineKuhnNextControl, machineKuhnReturnControl,
                        machineKuhnNonemptyReturnControl,
                        machineKuhnBuildReturnControl,
                        machineKuhnBuildRows, machineKuhnBuildChosenMate,
                        kuhnControlCode, kuhnSearchResultMateCode,
                        kuhnFrameCode, kuhnStackCode, kuhnBuildFrameCode,
                        kuhnEvalStep, hmate, finListUnaryCode,
                        binaryListCode]
                  | cons row rows =>
                      simp [machineKuhnNextControl, machineKuhnReturnControl,
                        machineKuhnNonemptyReturnControl,
                        machineKuhnBuildReturnControl,
                        machineKuhnBuildContinueControl,
                        machineKuhnBuildNextStack,
                        machineKuhnBuildNextFrame, machineKuhnBuildRows,
                        machineKuhnBuildChosenMate, kuhnControlCode,
                        kuhnSearchResultMateCode, kuhnFrameCode,
                        kuhnStackCode, kuhnBuildFrameCode,
                        kuhnEvalStep, hmate, finRangeUnaryCode,
                        finListUnaryCode, machineListHead, machineListTail,
                        machineKuhnStackPush, List.replicate_succ,
                        binaryListCode]
              | some mate' =>
                  cases rows with
                  | nil =>
                      simp [machineKuhnNextControl, machineKuhnReturnControl,
                        machineKuhnNonemptyReturnControl,
                        machineKuhnBuildReturnControl,
                        machineKuhnBuildRows, machineKuhnBuildChosenMate,
                        kuhnControlCode, kuhnSearchResultMateCode,
                        kuhnFrameCode, kuhnStackCode, kuhnBuildFrameCode,
                        kuhnEvalStep, hmate, finListUnaryCode,
                        binaryListCode]
                  | cons row rows =>
                      simp [machineKuhnNextControl, machineKuhnReturnControl,
                        machineKuhnNonemptyReturnControl,
                        machineKuhnBuildReturnControl,
                        machineKuhnBuildContinueControl,
                        machineKuhnBuildNextStack,
                        machineKuhnBuildNextFrame, machineKuhnBuildRows,
                        machineKuhnBuildChosenMate, kuhnControlCode,
                        kuhnSearchResultMateCode, kuhnFrameCode,
                        kuhnStackCode, kuhnBuildFrameCode,
                        kuhnEvalStep, hmate, finRangeUnaryCode,
                        finListUnaryCode, machineListHead, machineListTail,
                        machineKuhnStackPush, List.replicate_succ,
                        binaryListCode]
end BeyondBethe
