/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryRange

/-!
# Finite-word encoding of the explicit Kuhn evaluator

Every natural index is unary.  Boolean visited sets and column-mate tables are
right-nested lists, and the recursive continuation is an explicit
right-nested stack.  The rational matrix and the dimension-derived constant
words are carried unchanged beside the control word.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Semantic tables -/

/-- Lists the membership bits of the seen-column set in finite-index order. -/
def seenBoolList {n : ℕ} (seen : Finset (Fin n)) : List Bool :=
  List.ofFn fun i ↦ decide (i ∈ seen)

/-- Lists each column's optional matched row, replacing finite row indices by natural numbers. -/
def columnMateList {n : ℕ} (mate : ColumnMate n) : List (Option ℕ) :=
  List.ofFn fun j ↦ (mate j).map Fin.val

/-- Encodes a list of finite indices using unary codes for its entries. -/
def finListUnaryCode {n : ℕ} (xs : List (Fin n)) : List Bool :=
  binaryListCode finUnaryCode xs

@[simp] theorem seenBoolList_length {n : ℕ} (seen : Finset (Fin n)) :
    (seenBoolList seen).length = n := by
  simp [seenBoolList]

@[simp] theorem columnMateList_length {n : ℕ} (mate : ColumnMate n) :
    (columnMateList mate).length = n := by
  simp [columnMateList]

@[simp] theorem seenBoolList_getElem {n : ℕ} (seen : Finset (Fin n))
    (i : ℕ) (hi : i < (seenBoolList seen).length) :
    (seenBoolList seen)[i] = decide (⟨i, by simpa using! hi⟩ ∈ seen) := by
  simp [seenBoolList]

@[simp] theorem columnMateList_getElem {n : ℕ} (mate : ColumnMate n)
    (i : ℕ) (hi : i < (columnMateList mate).length) :
    (columnMateList mate)[i] =
      (mate ⟨i, by simpa using! hi⟩).map Fin.val := by
  simp [columnMateList]

theorem seenBoolList_insert {n : ℕ} (seen : Finset (Fin n)) (col : Fin n) :
    seenBoolList (insert col seen) =
      (seenBoolList seen).set col.1 true := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    simp only [seenBoolList_length] at hi hi'
    by_cases h : i = col.1
    · subst i
      simp [seenBoolList]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ col := by
        intro heq
        exact h (congrArg Fin.val heq)
      have hrev : col.1 ≠ i := by exact fun heq ↦ h heq.symm
      simp [seenBoolList, List.getElem_set, h, hrev, hfin]

theorem columnMateList_update {n : ℕ} (mate : ColumnMate n)
    (col : Fin n) (value : Option (Fin n)) :
    columnMateList (Function.update mate col value) =
      (columnMateList mate).set col.1 (value.map Fin.val) := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    simp only [columnMateList_length] at hi hi'
    by_cases h : i = col.1
    · subst i
      simp [columnMateList, Function.update]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ col := by
        intro heq
        exact h (congrArg Fin.val heq)
      have hrev : col.1 ≠ i := by exact fun heq ↦ h heq.symm
      simp [columnMateList, Function.update, List.getElem_set, h, hrev, hfin]

/-! ## Frame codes -/

/-- Packs the search continuation's fuel, remaining columns, row, saved matching, and selected
column. -/
def machineKuhnSearchFramePack
    (fuel remaining row mate column : List Bool) : List Bool :=
  pair fuel (pair remaining (pair row (pair mate column)))

/-- Packs the build continuation's remaining rows and fallback matching. -/
def machineKuhnBuildFramePack (rows fallback : List Bool) : List Bool :=
  pair rows fallback

/-- Encodes a semantic search frame with unary fuel and indices and the encoded column-mate
vector. -/
def kuhnSearchFrameCode {n : ℕ} (frame : KuhnSearchFrame n) : List Bool :=
  machineKuhnSearchFramePack (List.replicate frame.fuel true)
    (finListUnaryCode frame.remaining) (finUnaryCode frame.row)
    (mateVectorCode (columnMateList frame.mate))
    (finUnaryCode frame.column)

/-- Encodes a semantic build frame using its remaining row list and fallback column-mate vector. -/
def kuhnBuildFrameCode {n : ℕ} (frame : KuhnBuildFrame n) : List Bool :=
  machineKuhnBuildFramePack (finListUnaryCode frame.rows)
    (mateVectorCode (columnMateList frame.fallback))

/-- Encodes a Kuhn continuation frame with a false tag for search frames and a true tag for
build frames. -/
def kuhnFrameCode {n : ℕ} : KuhnFrame n → List Bool
  | .search frame => pair [false] (kuhnSearchFrameCode frame)
  | .build frame => pair [true] (kuhnBuildFrameCode frame)

/-- Encodes a stack of tagged Kuhn continuation frames as a binary list. -/
def kuhnStackCode {n : ℕ} (stack : List (KuhnFrame n)) : List Bool :=
  binaryListCode kuhnFrameCode stack

/-- Extracts the search-or-build tag from an encoded Kuhn continuation frame. -/
def machineKuhnFrameTag (frame : List Bool) : List Bool :=
  machinePairFirst frame

/-- Extracts the fields following an encoded Kuhn frame's tag. -/
def machineKuhnFramePayload (frame : List Bool) : List Bool :=
  machinePairSecond frame

/-- Extracts the unary fuel field from a tagged search continuation. -/
def machineKuhnSearchFrameFuel (frame : List Bool) : List Bool :=
  machinePairFirst (machineKuhnFramePayload frame)

/-- Extracts the encoded remaining-column list from a tagged search continuation. -/
def machineKuhnSearchFrameRemaining (frame : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineKuhnFramePayload frame))

/-- Extracts the unary row field from a tagged search continuation. -/
def machineKuhnSearchFrameRow (frame : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machineKuhnFramePayload frame)))

/-- Extracts the saved column-mate vector from a tagged search continuation. -/
def machineKuhnSearchFrameMate (frame : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machinePairSecond (machinePairSecond (machineKuhnFramePayload frame))))

/-- Extracts the selected column ruler from a tagged search continuation. -/
def machineKuhnSearchFrameColumn (frame : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond
    (machinePairSecond (machinePairSecond (machineKuhnFramePayload frame))))

/-- Extracts the remaining-row list from a tagged build continuation. -/
def machineKuhnBuildFrameRows (frame : List Bool) : List Bool :=
  machinePairFirst (machineKuhnFramePayload frame)

/-- Extracts the fallback matching from a tagged build continuation. -/
def machineKuhnBuildFrameFallback (frame : List Bool) : List Bool :=
  machinePairSecond (machineKuhnFramePayload frame)

/-- Reads the first encoded continuation frame from a Kuhn stack. -/
def machineKuhnStackHead (stack : List Bool) : List Bool :=
  machineListHead stack

/-- Removes the first encoded continuation frame from a Kuhn stack. -/
def machineKuhnStackTail (stack : List Bool) : List Bool :=
  machineListTail stack

/-- Prepends an encoded continuation frame to a Kuhn stack. -/
def machineKuhnStackPush (frame stack : List Bool) : List Bool :=
  pair frame stack

/-! ## Control codes -/

/-- Packs the fuel, remaining columns, row, seen bits, matching, and continuation stack of a
Kuhn search call. -/
def machineKuhnCallPack (fuel remaining row seen mate stack : List Bool) :
    List Bool :=
  pair fuel (pair remaining (pair row (pair seen (pair mate stack))))

/-- Packs the success flag, seen bits, matching, and continuation stack of a Kuhn return state. -/
def machineKuhnReturnPack (success seen mate stack : List Bool) : List Bool :=
  pair success (pair seen (pair mate stack))

/-- Builds a Kuhn call control word with the false tag and the complete search-call payload. -/
def machineKuhnControlCall
    (fuel remaining row seen mate stack : List Bool) : List Bool :=
  pair [false] (machineKuhnCallPack fuel remaining row seen mate stack)

/-- Builds a Kuhn return control word with tag `[true, false]` and its result payload. -/
def machineKuhnControlReturn
    (success seen mate stack : List Bool) : List Bool :=
  pair [true, false] (machineKuhnReturnPack success seen mate stack)

/-- Builds a completed Kuhn control word with tag `[true, true]` and the resulting matching. -/
def machineKuhnControlDone (mate : List Bool) : List Bool :=
  pair [true, true] mate

/-- Extracts the call, return, or completion tag from a Kuhn control word. -/
def machineKuhnControlTag (control : List Bool) : List Bool :=
  machinePairFirst control

/-- Extracts the payload following a Kuhn control word's tag. -/
def machineKuhnControlPayload (control : List Bool) : List Bool :=
  machinePairSecond control

/-- Reads the second control-tag bit, which distinguishes completed states among the
return-or-done tags. -/
def machineKuhnControlIsDoneBit (control : List Bool) : List Bool :=
  machineHeadBit (machineKuhnControlTag control).tail

/-- Extracts the unary fuel field from a Kuhn call control word. -/
def machineKuhnCallFuel (control : List Bool) : List Bool :=
  machinePairFirst (machineKuhnControlPayload control)

/-- Extracts the remaining-column list from a Kuhn call control word. -/
def machineKuhnCallRemaining (control : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineKuhnControlPayload control))

/-- Extracts the current row ruler from a Kuhn call control word. -/
def machineKuhnCallRow (control : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machineKuhnControlPayload control)))

/-- Extracts the seen-column bits from a Kuhn call control word. -/
def machineKuhnCallSeen (control : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machinePairSecond (machinePairSecond (machineKuhnControlPayload control))))

/-- Extracts the column-mate vector from a Kuhn call control word. -/
def machineKuhnCallMate (control : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond
      (machinePairSecond
        (machinePairSecond
          (machinePairSecond (machineKuhnControlPayload control)))))

/-- Extracts the continuation stack from a Kuhn call control word. -/
def machineKuhnCallStack (control : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond
      (machinePairSecond
        (machinePairSecond
          (machinePairSecond (machineKuhnControlPayload control)))))

/-- Extracts the success flag from a Kuhn return control word. -/
def machineKuhnReturnSuccess (control : List Bool) : List Bool :=
  machinePairFirst (machineKuhnControlPayload control)

/-- Extracts the updated seen-column bits from a Kuhn return control word. -/
def machineKuhnReturnSeen (control : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineKuhnControlPayload control))

/-- Extracts the returned matching from a Kuhn return control word. -/
def machineKuhnReturnMate (control : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machineKuhnControlPayload control)))

/-- Extracts the continuation stack from a Kuhn return control word. -/
def machineKuhnReturnStack (control : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machineKuhnControlPayload control)))

/-- Extracts the final matching from a completed Kuhn control word. -/
def machineKuhnDoneMate (control : List Bool) : List Bool :=
  machineKuhnControlPayload control

/-- Encodes a search result's matching when present, using the empty word when the search
failed. -/
def kuhnSearchResultMateCode {n : ℕ} (result : KuhnSearchResult n) : List Bool :=
  match result.mate? with
  | none => []
  | some mate => mateVectorCode (columnMateList mate)

/-- Encodes semantic Kuhn call, return, and completed states, including unary indices, seen
bits, matching vectors, and continuation stacks. -/
def kuhnControlCode {n : ℕ} : KuhnEvalState n → List Bool
  | .call fuel remaining row seen mate stack =>
      machineKuhnControlCall (List.replicate fuel true)
        (finListUnaryCode remaining) (finUnaryCode row)
        (boolVectorCode (seenBoolList seen))
        (mateVectorCode (columnMateList mate)) (kuhnStackCode stack)
  | .ret result stack =>
      machineKuhnControlReturn [result.mate?.isSome]
        (boolVectorCode (seenBoolList result.seen))
        (kuhnSearchResultMateCode result) (kuhnStackCode stack)
  | .done mate =>
      machineKuhnControlDone (mateVectorCode (columnMateList mate))

/-! ## Whole-state code and projections -/

/-- Packs a Kuhn control word with its fixed matrix, dimension, column list, all-false seen
vector, and length bound. -/
def machineKuhnStatePack
    (control matrix dimension columns falseSeen bound : List Bool) : List Bool :=
  pair control
    (pair matrix (pair dimension (pair columns (pair falseSeen bound))))

/-- Extracts the control word from an encoded Kuhn machine state. -/
def machineKuhnStateControl (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the fixed matrix word from an encoded Kuhn machine state. -/
def machineKuhnStateMatrix (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the unary dimension from an encoded Kuhn machine state. -/
def machineKuhnStateDimension (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the fixed complete column list from an encoded Kuhn machine state. -/
def machineKuhnStateColumns (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Extracts the fixed all-false seen vector from an encoded Kuhn machine state. -/
def machineKuhnStateFalseSeen (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state))))

/-- Extracts the word that bounds the field lengths of a Kuhn machine state. -/
def machineKuhnStateBound (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state))))

/-- Applies the binary-multiplication width construction to the list-update input bound to
obtain the Kuhn field bound. -/
def machineKuhnInputBound (matrix : List Bool) : List Bool :=
  machineBinaryMulWidth (machineListUpdateInputBound matrix)

/-- Encodes a semantic Kuhn state with its rational matrix, unary dimension, complete index
list, all-false seen vector, and computed bound. -/
def kuhnMachineStateCode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (state : KuhnEvalState n) : List Bool :=
  let matrix := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  let dimension := List.replicate n true
  machineKuhnStatePack (kuhnControlCode state) matrix dimension
    (finRangeUnaryCode n)
    (boolVectorCode (List.replicate n false))
    (machineKuhnInputBound matrix)

@[simp] theorem machineKuhnStateControl_pack (a b c d e f) :
    machineKuhnStateControl (machineKuhnStatePack a b c d e f) = a := by
  simp [machineKuhnStateControl, machineKuhnStatePack]

@[simp] theorem machineKuhnStateMatrix_pack (a b c d e f) :
    machineKuhnStateMatrix (machineKuhnStatePack a b c d e f) = b := by
  simp [machineKuhnStateMatrix, machineKuhnStatePack]

@[simp] theorem machineKuhnStateDimension_pack (a b c d e f) :
    machineKuhnStateDimension (machineKuhnStatePack a b c d e f) = c := by
  simp [machineKuhnStateDimension, machineKuhnStatePack]

@[simp] theorem machineKuhnStateColumns_pack (a b c d e f) :
    machineKuhnStateColumns (machineKuhnStatePack a b c d e f) = d := by
  simp [machineKuhnStateColumns, machineKuhnStatePack]

@[simp] theorem machineKuhnStateFalseSeen_pack (a b c d e f) :
    machineKuhnStateFalseSeen (machineKuhnStatePack a b c d e f) = e := by
  simp [machineKuhnStateFalseSeen, machineKuhnStatePack]

@[simp] theorem machineKuhnStateBound_pack (a b c d e f) :
    machineKuhnStateBound (machineKuhnStatePack a b c d e f) = f := by
  simp [machineKuhnStateBound, machineKuhnStatePack]

@[simp] theorem machineKuhnControlTag_call (a b c d e f) :
    machineKuhnControlTag (machineKuhnControlCall a b c d e f) = [false] := by
  simp [machineKuhnControlTag, machineKuhnControlCall]

@[simp] theorem machineKuhnControlTag_return (a b c d) :
    machineKuhnControlTag (machineKuhnControlReturn a b c d) =
      [true, false] := by
  simp [machineKuhnControlTag, machineKuhnControlReturn]

@[simp] theorem machineKuhnControlTag_done (a) :
    machineKuhnControlTag (machineKuhnControlDone a) = [true, true] := by
  simp [machineKuhnControlTag, machineKuhnControlDone]

@[simp] theorem machineKuhnControlIsDoneBit_call (a b c d e f) :
    machineKuhnControlIsDoneBit (machineKuhnControlCall a b c d e f) =
      [false] := by
  simp [machineKuhnControlIsDoneBit]

@[simp] theorem machineKuhnControlIsDoneBit_return (a b c d) :
    machineKuhnControlIsDoneBit (machineKuhnControlReturn a b c d) =
      [false] := by
  simp [machineKuhnControlIsDoneBit]

@[simp] theorem machineKuhnControlIsDoneBit_done (a) :
    machineKuhnControlIsDoneBit (machineKuhnControlDone a) = [true] := by
  simp [machineKuhnControlIsDoneBit]

@[simp] theorem machineKuhnCallFuel_pack (a b c d e f) :
    machineKuhnCallFuel (machineKuhnControlCall a b c d e f) = a := by
  simp [machineKuhnCallFuel, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnCallRemaining_pack (a b c d e f) :
    machineKuhnCallRemaining (machineKuhnControlCall a b c d e f) = b := by
  simp [machineKuhnCallRemaining, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnCallRow_pack (a b c d e f) :
    machineKuhnCallRow (machineKuhnControlCall a b c d e f) = c := by
  simp [machineKuhnCallRow, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnCallSeen_pack (a b c d e f) :
    machineKuhnCallSeen (machineKuhnControlCall a b c d e f) = d := by
  simp [machineKuhnCallSeen, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnCallMate_pack (a b c d e f) :
    machineKuhnCallMate (machineKuhnControlCall a b c d e f) = e := by
  simp [machineKuhnCallMate, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnCallStack_pack (a b c d e f) :
    machineKuhnCallStack (machineKuhnControlCall a b c d e f) = f := by
  simp [machineKuhnCallStack, machineKuhnControlCall,
    machineKuhnControlPayload, machineKuhnCallPack]

@[simp] theorem machineKuhnReturnSuccess_pack (a b c d) :
    machineKuhnReturnSuccess (machineKuhnControlReturn a b c d) = a := by
  simp [machineKuhnReturnSuccess, machineKuhnControlReturn,
    machineKuhnControlPayload, machineKuhnReturnPack]

@[simp] theorem machineKuhnReturnSeen_pack (a b c d) :
    machineKuhnReturnSeen (machineKuhnControlReturn a b c d) = b := by
  simp [machineKuhnReturnSeen, machineKuhnControlReturn,
    machineKuhnControlPayload, machineKuhnReturnPack]

@[simp] theorem machineKuhnReturnMate_pack (a b c d) :
    machineKuhnReturnMate (machineKuhnControlReturn a b c d) = c := by
  simp [machineKuhnReturnMate, machineKuhnControlReturn,
    machineKuhnControlPayload, machineKuhnReturnPack]

@[simp] theorem machineKuhnReturnStack_pack (a b c d) :
    machineKuhnReturnStack (machineKuhnControlReturn a b c d) = d := by
  simp [machineKuhnReturnStack, machineKuhnControlReturn,
    machineKuhnControlPayload, machineKuhnReturnPack]

@[simp] theorem machineKuhnDoneMate_pack (a) :
    machineKuhnDoneMate (machineKuhnControlDone a) = a := by
  simp [machineKuhnDoneMate, machineKuhnControlDone,
    machineKuhnControlPayload]

@[simp] theorem machineKuhnFrameTag_search (a b c d e) :
    machineKuhnFrameTag
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = [false] := by
  simp [machineKuhnFrameTag]

@[simp] theorem machineKuhnFrameTag_build (a b) :
    machineKuhnFrameTag
        (pair [true] (machineKuhnBuildFramePack a b)) = [true] := by
  simp [machineKuhnFrameTag]

@[simp] theorem machineKuhnSearchFrameFuel_pack (a b c d e) :
    machineKuhnSearchFrameFuel
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = a := by
  simp [machineKuhnSearchFrameFuel, machineKuhnFramePayload,
    machineKuhnSearchFramePack]

@[simp] theorem machineKuhnSearchFrameRemaining_pack (a b c d e) :
    machineKuhnSearchFrameRemaining
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = b := by
  simp [machineKuhnSearchFrameRemaining, machineKuhnFramePayload,
    machineKuhnSearchFramePack]

@[simp] theorem machineKuhnSearchFrameRow_pack (a b c d e) :
    machineKuhnSearchFrameRow
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = c := by
  simp [machineKuhnSearchFrameRow, machineKuhnFramePayload,
    machineKuhnSearchFramePack]

@[simp] theorem machineKuhnSearchFrameMate_pack (a b c d e) :
    machineKuhnSearchFrameMate
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = d := by
  simp [machineKuhnSearchFrameMate, machineKuhnFramePayload,
    machineKuhnSearchFramePack]

@[simp] theorem machineKuhnSearchFrameColumn_pack (a b c d e) :
    machineKuhnSearchFrameColumn
        (pair [false] (machineKuhnSearchFramePack a b c d e)) = e := by
  simp [machineKuhnSearchFrameColumn, machineKuhnFramePayload,
    machineKuhnSearchFramePack]

@[simp] theorem machineKuhnBuildFrameRows_pack (a b) :
    machineKuhnBuildFrameRows
        (pair [true] (machineKuhnBuildFramePack a b)) = a := by
  simp [machineKuhnBuildFrameRows, machineKuhnFramePayload,
    machineKuhnBuildFramePack]

@[simp] theorem machineKuhnBuildFrameFallback_pack (a b) :
    machineKuhnBuildFrameFallback
        (pair [true] (machineKuhnBuildFramePack a b)) = b := by
  simp [machineKuhnBuildFrameFallback, machineKuhnFramePayload,
    machineKuhnBuildFramePack]

@[simp] theorem machineKuhnStackHead_cons {n : ℕ}
    (frame : KuhnFrame n) (stack : List (KuhnFrame n)) :
    machineKuhnStackHead (kuhnStackCode (frame :: stack)) =
      kuhnFrameCode frame := by
  exact machineListHead_cons kuhnFrameCode frame stack

@[simp] theorem machineKuhnStackTail_cons {n : ℕ}
    (frame : KuhnFrame n) (stack : List (KuhnFrame n)) :
    machineKuhnStackTail (kuhnStackCode (frame :: stack)) =
      kuhnStackCode stack := by
  exact machineListTail_cons kuhnFrameCode frame stack

/-! The projections below are all constant-depth pairing operations. -/

theorem machineKuhnStateControl_mem_FP :
    machineKuhnStateControl ∈ Complexity.FP := machinePairFirst_mem_FP
theorem machineKuhnStateMatrix_mem_FP :
    machineKuhnStateMatrix ∈ Complexity.FP := by
  simpa only [machineKuhnStateMatrix] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP
theorem machineKuhnStateDimension_mem_FP :
    machineKuhnStateDimension ∈ Complexity.FP := by
  have h := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineKuhnStateDimension] using!
    machineCompose_mem_FP h machinePairFirst_mem_FP
theorem machineKuhnStateColumns_mem_FP :
    machineKuhnStateColumns ∈ Complexity.FP := by
  have h2 := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have h3 := machineCompose_mem_FP h2 machinePairSecond_mem_FP
  simpa only [machineKuhnStateColumns] using!
    machineCompose_mem_FP h3 machinePairFirst_mem_FP
theorem machineKuhnStateFalseSeen_mem_FP :
    machineKuhnStateFalseSeen ∈ Complexity.FP := by
  have h2 := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have h3 := machineCompose_mem_FP h2 machinePairSecond_mem_FP
  have h4 := machineCompose_mem_FP h3 machinePairSecond_mem_FP
  simpa only [machineKuhnStateFalseSeen] using!
    machineCompose_mem_FP h4 machinePairFirst_mem_FP
theorem machineKuhnStateBound_mem_FP :
    machineKuhnStateBound ∈ Complexity.FP := by
  have h2 := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have h3 := machineCompose_mem_FP h2 machinePairSecond_mem_FP
  have h4 := machineCompose_mem_FP h3 machinePairSecond_mem_FP
  simpa only [machineKuhnStateBound] using!
    machineCompose_mem_FP h4 machinePairSecond_mem_FP
theorem machineKuhnFrameTag_mem_FP :
    machineKuhnFrameTag ∈ Complexity.FP := machinePairFirst_mem_FP
theorem machineKuhnFramePayload_mem_FP :
    machineKuhnFramePayload ∈ Complexity.FP := machinePairSecond_mem_FP
theorem machineKuhnStackHead_mem_FP :
    machineKuhnStackHead ∈ Complexity.FP := machineListHead_mem_FP
theorem machineKuhnStackTail_mem_FP :
    machineKuhnStackTail ∈ Complexity.FP := machineListTail_mem_FP
theorem machineKuhnControlTag_mem_FP :
    machineKuhnControlTag ∈ Complexity.FP := machinePairFirst_mem_FP
theorem machineKuhnControlPayload_mem_FP :
    machineKuhnControlPayload ∈ Complexity.FP := machinePairSecond_mem_FP

/-- Follows the second projection of a nested pair exactly `depth` times. -/
def machinePairSecondN (depth : ℕ) (word : List Bool) : List Bool :=
  (machinePairSecond)^[depth] word

theorem machinePairSecondN_mem_FP (depth : ℕ) :
    machinePairSecondN depth ∈ Complexity.FP := by
  induction depth with
  | zero => simpa [machinePairSecondN] using! id_mem_FP
  | succ depth ih =>
      simpa [machinePairSecondN, Function.iterate_succ_apply] using!
        machineCompose_mem_FP machinePairSecond_mem_FP ih

theorem machineKuhnControlIsDoneBit_mem_FP :
    machineKuhnControlIsDoneBit ∈ Complexity.FP := by
  have htagTail := machineCompose_mem_FP
    (machineCompose_mem_FP machineKuhnControlTag_mem_FP machineTail_mem_FP)
    machineHeadBit_mem_FP
  simpa only [machineKuhnControlIsDoneBit] using! htagTail

theorem machineKuhnCallFuel_mem_FP :
    machineKuhnCallFuel ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 1)
    machinePairFirst_mem_FP
  simpa [machineKuhnCallFuel, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnCallRemaining_mem_FP :
    machineKuhnCallRemaining ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 2)
    machinePairFirst_mem_FP
  simpa [machineKuhnCallRemaining, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnCallRow_mem_FP :
    machineKuhnCallRow ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 3)
    machinePairFirst_mem_FP
  simpa [machineKuhnCallRow, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnCallSeen_mem_FP :
    machineKuhnCallSeen ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 4)
    machinePairFirst_mem_FP
  simpa [machineKuhnCallSeen, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnCallMate_mem_FP :
    machineKuhnCallMate ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 5)
    machinePairFirst_mem_FP
  simpa [machineKuhnCallMate, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnCallStack_mem_FP :
    machineKuhnCallStack ∈ Complexity.FP := by
  simpa [machineKuhnCallStack, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using!
      machinePairSecondN_mem_FP 6

theorem machineKuhnReturnSuccess_mem_FP :
    machineKuhnReturnSuccess ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 1)
    machinePairFirst_mem_FP
  simpa [machineKuhnReturnSuccess, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnReturnSeen_mem_FP :
    machineKuhnReturnSeen ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 2)
    machinePairFirst_mem_FP
  simpa [machineKuhnReturnSeen, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnReturnMate_mem_FP :
    machineKuhnReturnMate ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 3)
    machinePairFirst_mem_FP
  simpa [machineKuhnReturnMate, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnReturnStack_mem_FP :
    machineKuhnReturnStack ∈ Complexity.FP := by
  simpa [machineKuhnReturnStack, machineKuhnControlPayload,
    machinePairSecondN, Function.iterate_succ_apply'] using!
      machinePairSecondN_mem_FP 4

theorem machineKuhnDoneMate_mem_FP :
    machineKuhnDoneMate ∈ Complexity.FP := machinePairSecond_mem_FP

theorem machineKuhnSearchFrameFuel_mem_FP :
    machineKuhnSearchFrameFuel ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 1)
    machinePairFirst_mem_FP
  simpa [machineKuhnSearchFrameFuel, machineKuhnFramePayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnSearchFrameRemaining_mem_FP :
    machineKuhnSearchFrameRemaining ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 2)
    machinePairFirst_mem_FP
  simpa [machineKuhnSearchFrameRemaining, machineKuhnFramePayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnSearchFrameRow_mem_FP :
    machineKuhnSearchFrameRow ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 3)
    machinePairFirst_mem_FP
  simpa [machineKuhnSearchFrameRow, machineKuhnFramePayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnSearchFrameMate_mem_FP :
    machineKuhnSearchFrameMate ∈ Complexity.FP := by
  have h := machineCompose_mem_FP (machinePairSecondN_mem_FP 4)
    machinePairFirst_mem_FP
  simpa [machineKuhnSearchFrameMate, machineKuhnFramePayload,
    machinePairSecondN, Function.iterate_succ_apply'] using! h

theorem machineKuhnSearchFrameColumn_mem_FP :
    machineKuhnSearchFrameColumn ∈ Complexity.FP := by
  simpa [machineKuhnSearchFrameColumn, machineKuhnFramePayload,
    machinePairSecondN, Function.iterate_succ_apply'] using!
      machinePairSecondN_mem_FP 5

theorem machineKuhnBuildFrameRows_mem_FP :
    machineKuhnBuildFrameRows ∈ Complexity.FP := by
  have h := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairFirst_mem_FP
  simpa [machineKuhnBuildFrameRows, machineKuhnFramePayload] using! h

theorem machineKuhnBuildFrameFallback_mem_FP :
    machineKuhnBuildFrameFallback ∈ Complexity.FP := by
  simpa [machineKuhnBuildFrameFallback, machineKuhnFramePayload] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

end BeyondBethe
