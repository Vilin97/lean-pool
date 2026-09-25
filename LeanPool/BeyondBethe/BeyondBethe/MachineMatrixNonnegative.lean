/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalCompare
public import LeanPool.BeyondBethe.BeyondBethe.RawRationalBitBounds

/-!
# Polynomial-time matrix nonnegativity guard

The public matrix encoding is a pair containing a right-nested list of rows,
each itself a right-nested list of rational entries.  This file scans that
encoding directly.  The scan never decodes a binary dimension into unary and
never invokes Lean's decision procedure on the typed matrix.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def machineMatrixNonnegativePack
    (rows current ok : List Bool) : List Bool :=
  pair rows (pair current ok)

def machineMatrixNonnegativeRows (state : List Bool) : List Bool :=
  machinePairFirst state

def machineMatrixNonnegativeCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineMatrixNonnegativeOk (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineMatrixNonnegativeEntry (state : List Bool) : List Bool :=
  machineListHead (machineMatrixNonnegativeCurrent state)

def machineMatrixNonnegativeEntryBit (state : List Bool) : List Bool :=
  machineHeadBit
    (machineRawRatLeBit
      (pair (rawRatBinaryCode RawRat.zero)
        (machineMatrixNonnegativeEntry state)))

def machineMatrixNonnegativeProcessEntry (state : List Bool) : List Bool :=
  machineMatrixNonnegativePack
    (machineMatrixNonnegativeRows state)
    (machineListTail (machineMatrixNonnegativeCurrent state))
    (machineAndBit (machineMatrixNonnegativeOk state)
      (machineMatrixNonnegativeEntryBit state))

def machineMatrixNonnegativeLoadRow (state : List Bool) : List Bool :=
  machineMatrixNonnegativePack
    (machineListTail (machineMatrixNonnegativeRows state))
    (machineListHead (machineMatrixNonnegativeRows state))
    (machineMatrixNonnegativeOk state)

def machineMatrixNonnegativeAfterRow (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixNonnegativeRows state) state
    (machineMatrixNonnegativeLoadRow state)

def machineMatrixNonnegativeStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineMatrixNonnegativeCurrent state)
    (machineMatrixNonnegativeAfterRow state)
    (machineMatrixNonnegativeProcessEntry state)

def machineMatrixNonnegativeInit (word : List Bool) : List Bool :=
  machineMatrixNonnegativePack (machineMatrixRowsWord word) [] [true]

def machineMatrixNonnegativeWidth (word : List Bool) : List Bool :=
  machineMatrixNonnegativePack word word [true]

def machineMatrixNonnegativeFinalState (word : List Bool) : List Bool :=
  (machineMatrixNonnegativeStep)^[word.length]
    (machineMatrixNonnegativeInit word)

/-- One-bit result of the direct nested-list scan. -/
def machineMatrixNonnegativeBit (word : List Bool) : List Bool :=
  machineMatrixNonnegativeOk (machineMatrixNonnegativeFinalState word)

theorem machineMatrixNonnegativeRows_mem_FP :
    machineMatrixNonnegativeRows ∈ Complexity.FP :=
  machinePairFirst_mem_FP

theorem machineMatrixNonnegativeCurrent_mem_FP :
    machineMatrixNonnegativeCurrent ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeCurrent] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineMatrixNonnegativeOk_mem_FP :
    machineMatrixNonnegativeOk ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeOk] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineMatrixNonnegativeEntry_mem_FP :
    machineMatrixNonnegativeEntry ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeEntry, machineListHead] using!
    machineCompose_mem_FP machineMatrixNonnegativeCurrent_mem_FP
      machinePairFirst_mem_FP

theorem machineMatrixNonnegativeEntryBit_mem_FP :
    machineMatrixNonnegativeEntryBit ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP
    (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
    machineMatrixNonnegativeEntry_mem_FP
  simpa only [machineMatrixNonnegativeEntryBit] using!
    machineCompose_mem_FP
      (machineCompose_mem_FP hpair machineRawRatLeBit_mem_FP)
      machineHeadBit_mem_FP

theorem machineMatrixNonnegativeProcessEntry_mem_FP :
    machineMatrixNonnegativeProcessEntry ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP
    machineMatrixNonnegativeCurrent_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP machineMatrixNonnegativeRows_mem_FP
    (machinePair_mem_FP htail
      (machineAndBit_mem_FP machineMatrixNonnegativeOk_mem_FP
        machineMatrixNonnegativeEntryBit_mem_FP))

theorem machineMatrixNonnegativeLoadRow_mem_FP :
    machineMatrixNonnegativeLoadRow ∈ Complexity.FP := by
  have htail := machineCompose_mem_FP
    machineMatrixNonnegativeRows_mem_FP machineListTail_mem_FP
  have hhead := machineCompose_mem_FP
    machineMatrixNonnegativeRows_mem_FP machineListHead_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP hhead machineMatrixNonnegativeOk_mem_FP)

theorem machineMatrixNonnegativeAfterRow_mem_FP :
    machineMatrixNonnegativeAfterRow ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeAfterRow] using!
    machineIfEmpty_mem_FP machineMatrixNonnegativeRows_mem_FP id_mem_FP
      machineMatrixNonnegativeLoadRow_mem_FP

theorem machineMatrixNonnegativeStep_mem_FP :
    machineMatrixNonnegativeStep ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeStep] using!
    machineIfEmpty_mem_FP machineMatrixNonnegativeCurrent_mem_FP
      machineMatrixNonnegativeAfterRow_mem_FP
      machineMatrixNonnegativeProcessEntry_mem_FP

theorem machineMatrixNonnegativeInit_mem_FP :
    machineMatrixNonnegativeInit ∈ Complexity.FP := by
  exact machinePair_mem_FP machineMatrixRowsWord_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machineConst_mem_FP [true]))

theorem machineMatrixNonnegativeWidth_mem_FP :
    machineMatrixNonnegativeWidth ∈ Complexity.FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP (machineConst_mem_FP [true]))

@[simp] theorem machineMatrixNonnegativeRows_pack (rows current ok) :
    machineMatrixNonnegativeRows
        (machineMatrixNonnegativePack rows current ok) = rows := by
  simp [machineMatrixNonnegativeRows, machineMatrixNonnegativePack]

@[simp] theorem machineMatrixNonnegativeCurrent_pack (rows current ok) :
    machineMatrixNonnegativeCurrent
        (machineMatrixNonnegativePack rows current ok) = current := by
  simp [machineMatrixNonnegativeCurrent, machineMatrixNonnegativePack]

@[simp] theorem machineMatrixNonnegativeOk_pack (rows current ok) :
    machineMatrixNonnegativeOk
        (machineMatrixNonnegativePack rows current ok) = ok := by
  simp [machineMatrixNonnegativeOk, machineMatrixNonnegativePack]

def MachineMatrixNonnegativeStateBound
    (word state : List Bool) : Prop :=
  state = machineMatrixNonnegativePack
      (machineMatrixNonnegativeRows state)
      (machineMatrixNonnegativeCurrent state)
      (machineMatrixNonnegativeOk state) ∧
    (machineMatrixNonnegativeRows state).length ≤ word.length ∧
    (machineMatrixNonnegativeCurrent state).length ≤ word.length ∧
    (machineMatrixNonnegativeOk state).length ≤ 1

theorem machineMatrixNonnegativeInit_bound (word : List Bool) :
    MachineMatrixNonnegativeStateBound word
      (machineMatrixNonnegativeInit word) := by
  simp only [MachineMatrixNonnegativeStateBound,
    machineMatrixNonnegativeInit, machineMatrixNonnegativeRows_pack,
    machineMatrixNonnegativeCurrent_pack, machineMatrixNonnegativeOk_pack]
  refine ⟨trivial, ?_, by simp, by simp⟩
  simpa only [machineMatrixRowsWord] using! machinePairSecond_length_le word

theorem machineMatrixNonnegativeStep_bound
    {word state : List Bool}
    (hstate : MachineMatrixNonnegativeStateBound word state) :
    MachineMatrixNonnegativeStateBound word
      (machineMatrixNonnegativeStep state) := by
  rcases hstate with ⟨hdecomp, hrows, hcurrent, hok⟩
  by_cases hc : machineMatrixNonnegativeCurrent state = []
  · rw [machineMatrixNonnegativeStep, hc, machineIfEmpty_nil]
    by_cases hr : machineMatrixNonnegativeRows state = []
    · rw [machineMatrixNonnegativeAfterRow, hr, machineIfEmpty_nil]
      exact ⟨hdecomp, hrows, hcurrent, hok⟩
    · rw [machineMatrixNonnegativeAfterRow]
      cases hrowsCode : machineMatrixNonnegativeRows state with
      | nil => exact False.elim (hr hrowsCode)
      | cons bit tail =>
          rw [machineIfEmpty_cons, machineMatrixNonnegativeLoadRow]
          simp only [MachineMatrixNonnegativeStateBound,
            machineMatrixNonnegativeRows_pack,
            machineMatrixNonnegativeCurrent_pack,
            machineMatrixNonnegativeOk_pack]
          refine ⟨trivial, ?_, ?_, hok⟩
          · exact (machinePairSecond_length_le
              (machineMatrixNonnegativeRows state)).trans hrows
          · exact (machinePairFirst_length_le
              (machineMatrixNonnegativeRows state)).trans hrows
  · rw [machineMatrixNonnegativeStep]
    cases hcurrentCode : machineMatrixNonnegativeCurrent state with
    | nil => exact False.elim (hc hcurrentCode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineMatrixNonnegativeProcessEntry]
        simp only [MachineMatrixNonnegativeStateBound,
          machineMatrixNonnegativeRows_pack,
          machineMatrixNonnegativeCurrent_pack,
          machineMatrixNonnegativeOk_pack]
        refine ⟨trivial, hrows, ?_, ?_⟩
        · exact (machinePairSecond_length_le
            (machineMatrixNonnegativeCurrent state)).trans hcurrent
        · change (machineIfHead (machineMatrixNonnegativeOk state)
              (machineMatrixNonnegativeEntryBit state) [false]).length ≤ 1
          cases hokCode : machineMatrixNonnegativeOk state with
          | nil => simp [machineIfHead, Cobham.selectHead]
          | cons bit tail =>
              cases bit <;>
                simp [machineIfHead, Cobham.selectHead,
                  machineMatrixNonnegativeEntryBit]

theorem machineMatrixNonnegativeIterate_bound (word : List Bool) : ∀ k,
    MachineMatrixNonnegativeStateBound word
      ((machineMatrixNonnegativeStep)^[k]
        (machineMatrixNonnegativeInit word)) := by
  intro k
  induction k with
  | zero => exact machineMatrixNonnegativeInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineMatrixNonnegativeStep_bound ih

theorem machineMatrixNonnegativeIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineMatrixNonnegativeStep)^[iterations]
      (machineMatrixNonnegativeInit word)).length ≤
        (machineMatrixNonnegativeWidth word).length := by
  rcases machineMatrixNonnegativeIterate_bound word iterations with
    ⟨hdecomp, hrows, hcurrent, hok⟩
  rw [hdecomp]
  simp only [machineMatrixNonnegativePack,
    machineMatrixNonnegativeWidth, pair_length, List.length_cons,
    List.length_nil]
  omega

theorem machineMatrixNonnegativeFinalState_mem_FP :
    machineMatrixNonnegativeFinalState ∈ Complexity.FP := by
  exact Cobham.iterate_mem_FP machineMatrixNonnegativeStep_mem_FP
    machineMatrixNonnegativeInit_mem_FP id_mem_FP
    machineMatrixNonnegativeWidth_mem_FP
    machineMatrixNonnegativeIterate_length_le_width

theorem machineMatrixNonnegativeBit_mem_FP :
    machineMatrixNonnegativeBit ∈ Complexity.FP := by
  simpa only [machineMatrixNonnegativeBit] using!
    machineCompose_mem_FP machineMatrixNonnegativeFinalState_mem_FP
      machineMatrixNonnegativeOk_mem_FP

/-! ## Exact semantics on canonical nested-list encodings -/

def rationalNonnegativeBit (q : ℚ) : Bool := decide (0 ≤ q)

theorem machineIfEmpty_of_ne_nil_matrix
    (test whenEmpty whenNonempty : List Bool) (h : test ≠ []) :
    machineIfEmpty test whenEmpty whenNonempty = whenNonempty := by
  cases test with
  | nil => exact False.elim (h rfl)
  | cons bit tail => simp

theorem binaryListCode_cons_ne_nil {α : Type*}
    (encode : α → List Bool) (x : α) (xs : List α) :
    binaryListCode encode (x :: xs) ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp [binaryListCode] at hlen

@[simp] theorem rawRatBinaryCode_rawRatOfRat (q : ℚ) :
    rawRatBinaryCode (rawRatOfRat q) = rationalEntryBinaryCode q := by
  simp [rawRatBinaryCode, rawRatOfRat, rationalEntryBinaryCode]

@[simp] theorem machineMatrixNonnegativeEntryBit_encode
    (rows : List (List ℚ)) (current : List ℚ) (ok : Bool) (q : ℚ) :
    machineMatrixNonnegativeEntryBit
        (machineMatrixNonnegativePack
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
          (binaryListCode rationalEntryBinaryCode (q :: current)) [ok]) =
      [rationalNonnegativeBit q] := by
  rw [machineMatrixNonnegativeEntryBit,
    machineMatrixNonnegativeEntry]
  simp only [machineMatrixNonnegativeCurrent_pack,
    machineListHead_cons, ← rawRatBinaryCode_rawRatOfRat]
  rw [machineRawRatLeBit_encode, machineHeadBit_cons]
  simp [rationalNonnegativeBit]

@[simp] theorem machineMatrixNonnegativeStep_entry_encode
    (rows : List (List ℚ)) (q : ℚ) (current : List ℚ) (ok : Bool) :
    machineMatrixNonnegativeStep
        (machineMatrixNonnegativePack
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
          (binaryListCode rationalEntryBinaryCode (q :: current)) [ok]) =
      machineMatrixNonnegativePack
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
        (binaryListCode rationalEntryBinaryCode current)
        [ok && rationalNonnegativeBit q] := by
  rw [machineMatrixNonnegativeStep]
  simp only [machineMatrixNonnegativeCurrent_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil rationalEntryBinaryCode q current)]
  simp [machineMatrixNonnegativeProcessEntry]

@[simp] theorem machineMatrixNonnegativeStep_row_encode
    (row : List ℚ) (rows : List (List ℚ)) (ok : Bool) :
    machineMatrixNonnegativeStep
        (machineMatrixNonnegativePack
          (binaryListCode (binaryListCode rationalEntryBinaryCode)
            (row :: rows)) [] [ok]) =
      machineMatrixNonnegativePack
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
        (binaryListCode rationalEntryBinaryCode row) [ok] := by
  rw [machineMatrixNonnegativeStep]
  simp only [machineMatrixNonnegativeCurrent_pack]
  rw [machineIfEmpty_nil, machineMatrixNonnegativeAfterRow]
  simp only [machineMatrixNonnegativeRows_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil
      (binaryListCode rationalEntryBinaryCode) row rows)]
  simp [machineMatrixNonnegativeLoadRow]

@[simp] theorem machineMatrixNonnegativeStep_done_encode (ok : Bool) :
    machineMatrixNonnegativeStep
        (machineMatrixNonnegativePack [] [] [ok]) =
      machineMatrixNonnegativePack [] [] [ok] := by
  simp [machineMatrixNonnegativeStep, machineMatrixNonnegativeAfterRow]

def matrixNonnegativeRowBit (row : List ℚ) : Bool :=
  row.all rationalNonnegativeBit

def matrixNonnegativeRowsBit (rows : List (List ℚ)) : Bool :=
  rows.all matrixNonnegativeRowBit

theorem machineMatrixNonnegativeProcessRow_encode
    (rows : List (List ℚ)) (row : List ℚ) (ok : Bool) :
    (machineMatrixNonnegativeStep)^[row.length]
        (machineMatrixNonnegativePack
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
          (binaryListCode rationalEntryBinaryCode row) [ok]) =
      machineMatrixNonnegativePack
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows) []
        [ok && matrixNonnegativeRowBit row] := by
  induction row generalizing ok with
  | nil => simp [matrixNonnegativeRowBit, binaryListCode]
  | cons q row ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        machineMatrixNonnegativeStep_entry_encode, ih]
      simp [matrixNonnegativeRowBit, Bool.and_assoc]

def matrixNonnegativeRowsWork : List (List ℚ) → ℕ
  | [] => 0
  | row :: rows => 1 + row.length + matrixNonnegativeRowsWork rows

theorem machineMatrixNonnegativeProcessRows_encode
    (rows : List (List ℚ)) (ok : Bool) :
    (machineMatrixNonnegativeStep)^[matrixNonnegativeRowsWork rows]
        (machineMatrixNonnegativePack
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
          [] [ok]) =
      machineMatrixNonnegativePack [] []
        [ok && matrixNonnegativeRowsBit rows] := by
  induction rows generalizing ok with
  | nil =>
      simp [matrixNonnegativeRowsWork, matrixNonnegativeRowsBit,
        binaryListCode]
  | cons row rows ih =>
      rw [matrixNonnegativeRowsWork, show 1 + row.length +
          matrixNonnegativeRowsWork rows =
          matrixNonnegativeRowsWork rows + row.length + 1 by omega,
        Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, machineMatrixNonnegativeStep_row_encode,
        machineMatrixNonnegativeProcessRow_encode, ih]
      simp [matrixNonnegativeRowsBit, Bool.and_assoc]

theorem binaryListCode_length_ge_work (rows : List (List ℚ)) :
    matrixNonnegativeRowsWork rows ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  induction rows with
  | nil => simp [matrixNonnegativeRowsWork, binaryListCode]
  | cons row rows ih =>
      simp only [matrixNonnegativeRowsWork, binaryListCode, pair_length]
      have hrow : row.length ≤
          (binaryListCode rationalEntryBinaryCode row).length := by
        induction row with
        | nil => simp [binaryListCode]
        | cons q row ihrow =>
            simp only [binaryListCode, pair_length, List.length_cons]
            omega
      omega

theorem machineMatrixNonnegativeDone_iterate (extra : ℕ) (ok : Bool) :
    (machineMatrixNonnegativeStep)^[extra]
        (machineMatrixNonnegativePack [] [] [ok]) =
      machineMatrixNonnegativePack [] [] [ok] := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        machineMatrixNonnegativeStep_done_encode]

theorem machineMatrixNonnegativeFinalState_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNonnegativeFinalState
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      machineMatrixNonnegativePack [] []
        [matrixNonnegativeRowsBit (rationalMatrixRows A)] := by
  let rows := rationalMatrixRows A
  let word := rationalMatrixBinaryEncoding.encode ⟨n, A⟩
  have hwork : matrixNonnegativeRowsWork rows ≤ word.length := by
    have hcode := binaryListCode_length_ge_work rows
    have hrows :
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
          word.length := by
      calc
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length =
            (machineMatrixRowsWord word).length := by
              simpa only [word, rows] using! congrArg List.length
                (machineMatrixRowsWord_encode A).symm
        _ ≤ word.length := by
          simpa only [machineMatrixRowsWord] using!
            machinePairSecond_length_le word
    exact hcode.trans hrows
  have hsplit : word.length =
      (word.length - matrixNonnegativeRowsWork rows) +
        matrixNonnegativeRowsWork rows := by omega
  change machineMatrixNonnegativeFinalState word = _
  rw [machineMatrixNonnegativeFinalState, hsplit,
    Function.iterate_add_apply]
  have hinit : machineMatrixNonnegativeInit word =
      machineMatrixNonnegativePack
        (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
        [] [true] := by
    simp [machineMatrixNonnegativeInit, word, rows]
  rw [hinit, machineMatrixNonnegativeProcessRows_encode,
    machineMatrixNonnegativeDone_iterate]
  simp [rows]

theorem matrixNonnegativeRowsBit_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixNonnegativeRowsBit (rationalMatrixRows A) = true ↔
      Matrix.Nonnegative A := by
  simp [matrixNonnegativeRowsBit, matrixNonnegativeRowBit,
    rationalNonnegativeBit, rationalMatrixRows, Matrix.Nonnegative]

open scoped Classical in
@[simp] theorem machineMatrixNonnegativeBit_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixNonnegativeBit
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      [decide (∀ i : Fin n, ∀ j : Fin n, 0 ≤ A i j)] := by
  rw [machineMatrixNonnegativeBit,
    machineMatrixNonnegativeFinalState_encode]
  simp only [machineMatrixNonnegativeOk_pack]
  apply congrArg singleton
  apply Bool.eq_iff_iff.mpr
  simpa [Matrix.Nonnegative] using! matrixNonnegativeRowsBit_iff A

end BeyondBethe
