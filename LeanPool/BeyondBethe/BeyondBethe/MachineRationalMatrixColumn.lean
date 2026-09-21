/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorDot
import Mathlib.Data.List.GetD

/-!
# Polynomial-time extraction of rational matrix columns

Rational ellipsoid bases are stored row by row.  This transducer scans those
rows, reads one unary-indexed entry from each row, and returns the resulting
column as a canonical rational-vector word.  It is total on arbitrary words;
the exactness theorem only assumes that the selected column exists in every
row.
-/

namespace BeyondBethe

open Complexity

def machineRationalMatrixColumnIndex (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRationalMatrixColumnRows (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRationalMatrixColumnPack
    (remaining accumulator column bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair column bound))

def machineRationalMatrixColumnRemaining
    (state : List Bool) : List Bool :=
  machinePairFirst state

def machineRationalMatrixColumnAccumulator
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRationalMatrixColumnColumn
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineRationalMatrixColumnBound
    (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineRationalMatrixColumnCurrentRow
    (state : List Bool) : List Bool :=
  machineListHead (machineRationalMatrixColumnRemaining state)

def machineRationalMatrixColumnCurrentEntry
    (state : List Bool) : List Bool :=
  machineListIndex
    (pair (machineRationalMatrixColumnColumn state)
      (machineRationalMatrixColumnCurrentRow state))

def machineRationalMatrixColumnCandidate
    (state : List Bool) : List Bool :=
  pair (machineRationalMatrixColumnCurrentEntry state)
    (machineRationalMatrixColumnAccumulator state)

def machineRationalMatrixColumnNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalMatrixColumnCandidate state).take
    (machineRationalMatrixColumnBound state).length

def machineRationalMatrixColumnAdvance
    (state : List Bool) : List Bool :=
  machineRationalMatrixColumnPack
    (machineListTail (machineRationalMatrixColumnRemaining state))
    (machineRationalMatrixColumnNextAccumulator state)
    (machineRationalMatrixColumnColumn state)
    (machineRationalMatrixColumnBound state)

def machineRationalMatrixColumnStep
    (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalMatrixColumnRemaining state) state
    (machineRationalMatrixColumnAdvance state)

def machineRationalMatrixColumnInit (word : List Bool) : List Bool :=
  machineRationalMatrixColumnPack
    (machineRationalMatrixColumnRows word) []
    (machineRationalMatrixColumnIndex word) word

def machineRationalMatrixColumnWidth (word : List Bool) : List Bool :=
  machineRationalMatrixColumnPack word word word word

def machineRationalMatrixColumnFinalState
    (word : List Bool) : List Bool :=
  (machineRationalMatrixColumnStep)^[word.length]
    (machineRationalMatrixColumnInit word)

def machineRationalMatrixColumnReversedCode
    (word : List Bool) : List Bool :=
  machineRationalMatrixColumnAccumulator
    (machineRationalMatrixColumnFinalState word)

/-- Input: `pair columnUnary nestedRowsCode`. -/
def machineRationalMatrixColumnCode (word : List Bool) : List Bool :=
  machineListReverse (machineRationalMatrixColumnReversedCode word)

theorem machineRationalMatrixColumnIndex_mem_FP :
    machineRationalMatrixColumnIndex ∈ FP := machinePairFirst_mem_FP

theorem machineRationalMatrixColumnRows_mem_FP :
    machineRationalMatrixColumnRows ∈ FP := machinePairSecond_mem_FP

theorem machineRationalMatrixColumnRemaining_mem_FP :
    machineRationalMatrixColumnRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineRationalMatrixColumnAccumulator_mem_FP :
    machineRationalMatrixColumnAccumulator ∈ FP := by
  simpa only [machineRationalMatrixColumnAccumulator] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalMatrixColumnColumn_mem_FP :
    machineRationalMatrixColumnColumn ∈ FP := by
  simpa only [machineRationalMatrixColumnColumn] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP)
      machinePairFirst_mem_FP

theorem machineRationalMatrixColumnBound_mem_FP :
    machineRationalMatrixColumnBound ∈ FP := by
  simpa only [machineRationalMatrixColumnBound] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP)
      machinePairSecond_mem_FP

theorem machineRationalMatrixColumnCurrentRow_mem_FP :
    machineRationalMatrixColumnCurrentRow ∈ FP := by
  simpa only [machineRationalMatrixColumnCurrentRow] using
    machineCompose_mem_FP machineRationalMatrixColumnRemaining_mem_FP
      machineListHead_mem_FP

theorem machineRationalMatrixColumnCurrentEntry_mem_FP :
    machineRationalMatrixColumnCurrentEntry ∈ FP := by
  have hp := machinePair_mem_FP machineRationalMatrixColumnColumn_mem_FP
    machineRationalMatrixColumnCurrentRow_mem_FP
  simpa only [machineRationalMatrixColumnCurrentEntry] using
    machineCompose_mem_FP hp machineListIndex_mem_FP

theorem machineRationalMatrixColumnCandidate_mem_FP :
    machineRationalMatrixColumnCandidate ∈ FP :=
  machinePair_mem_FP machineRationalMatrixColumnCurrentEntry_mem_FP
    machineRationalMatrixColumnAccumulator_mem_FP

theorem machineRationalMatrixColumnNextAccumulator_mem_FP :
    machineRationalMatrixColumnNextAccumulator ∈ FP := by
  simpa only [machineRationalMatrixColumnNextAccumulator] using
    machineTake_mem_FP machineRationalMatrixColumnBound_mem_FP
      machineRationalMatrixColumnCandidate_mem_FP

theorem machineRationalMatrixColumnAdvance_mem_FP :
    machineRationalMatrixColumnAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalMatrixColumnRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalMatrixColumnNextAccumulator_mem_FP
      (machinePair_mem_FP machineRationalMatrixColumnColumn_mem_FP
        machineRationalMatrixColumnBound_mem_FP))

theorem machineRationalMatrixColumnStep_mem_FP :
    machineRationalMatrixColumnStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalMatrixColumnRemaining_mem_FP
    id_mem_FP machineRationalMatrixColumnAdvance_mem_FP

theorem machineRationalMatrixColumnInit_mem_FP :
    machineRationalMatrixColumnInit ∈ FP := by
  exact machinePair_mem_FP machineRationalMatrixColumnRows_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineRationalMatrixColumnIndex_mem_FP id_mem_FP))

theorem machineRationalMatrixColumnWidth_mem_FP :
    machineRationalMatrixColumnWidth ∈ FP := by
  exact machinePair_mem_FP id_mem_FP
    (machinePair_mem_FP id_mem_FP
      (machinePair_mem_FP id_mem_FP id_mem_FP))

@[simp] theorem machineRationalMatrixColumnRemaining_pack (a b c d) :
    machineRationalMatrixColumnRemaining
      (machineRationalMatrixColumnPack a b c d) = a := by
  simp [machineRationalMatrixColumnRemaining,
    machineRationalMatrixColumnPack]

@[simp] theorem machineRationalMatrixColumnAccumulator_pack (a b c d) :
    machineRationalMatrixColumnAccumulator
      (machineRationalMatrixColumnPack a b c d) = b := by
  simp [machineRationalMatrixColumnAccumulator,
    machineRationalMatrixColumnPack]

@[simp] theorem machineRationalMatrixColumnColumn_pack (a b c d) :
    machineRationalMatrixColumnColumn
      (machineRationalMatrixColumnPack a b c d) = c := by
  simp [machineRationalMatrixColumnColumn,
    machineRationalMatrixColumnPack]

@[simp] theorem machineRationalMatrixColumnBound_pack (a b c d) :
    machineRationalMatrixColumnBound
      (machineRationalMatrixColumnPack a b c d) = d := by
  simp [machineRationalMatrixColumnBound,
    machineRationalMatrixColumnPack]

def MachineRationalMatrixColumnStateBound
    (word state : List Bool) : Prop :=
  state = machineRationalMatrixColumnPack
      (machineRationalMatrixColumnRemaining state)
      (machineRationalMatrixColumnAccumulator state)
      (machineRationalMatrixColumnColumn state)
      (machineRationalMatrixColumnBound state) ∧
    (machineRationalMatrixColumnRemaining state).length ≤ word.length ∧
    (machineRationalMatrixColumnAccumulator state).length ≤ word.length ∧
    (machineRationalMatrixColumnColumn state).length ≤ word.length ∧
    machineRationalMatrixColumnBound state = word

theorem machineRationalMatrixColumnInit_bound (word : List Bool) :
    MachineRationalMatrixColumnStateBound word
      (machineRationalMatrixColumnInit word) := by
  simp only [MachineRationalMatrixColumnStateBound,
    machineRationalMatrixColumnInit,
    machineRationalMatrixColumnRemaining_pack,
    machineRationalMatrixColumnAccumulator_pack,
    machineRationalMatrixColumnColumn_pack,
    machineRationalMatrixColumnBound_pack]
  exact ⟨trivial, machinePairSecond_length_le word, by simp,
    machinePairFirst_length_le word, trivial⟩

theorem machineRationalMatrixColumnStep_bound {word state : List Bool}
    (hs : MachineRationalMatrixColumnStateBound word state) :
    MachineRationalMatrixColumnStateBound word
      (machineRationalMatrixColumnStep state) := by
  rcases hs with ⟨hdecomp, hremaining, hacc, hcolumn, hbound⟩
  by_cases hnil : machineRationalMatrixColumnRemaining state = []
  · rw [machineRationalMatrixColumnStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hcolumn, hbound⟩
  · rw [machineRationalMatrixColumnStep]
    cases hcode : machineRationalMatrixColumnRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineRationalMatrixColumnAdvance]
        simp only [MachineRationalMatrixColumnStateBound,
          machineRationalMatrixColumnRemaining_pack,
          machineRationalMatrixColumnAccumulator_pack,
          machineRationalMatrixColumnColumn_pack,
          machineRationalMatrixColumnBound_pack]
        refine ⟨trivial, ?_, ?_, hcolumn, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalMatrixColumnRemaining state)).trans hremaining
        · rw [machineRationalMatrixColumnNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalMatrixColumnIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalMatrixColumnStateBound word
      ((machineRationalMatrixColumnStep)^[k]
        (machineRationalMatrixColumnInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalMatrixColumnInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalMatrixColumnStep_bound ih

theorem machineRationalMatrixColumnIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalMatrixColumnStep)^[iterations]
      (machineRationalMatrixColumnInit word)).length ≤
        (machineRationalMatrixColumnWidth word).length := by
  rcases machineRationalMatrixColumnIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hcolumn, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalMatrixColumnPack,
    machineRationalMatrixColumnWidth, pair_length]
  omega

theorem machineRationalMatrixColumnFinalState_mem_FP :
    machineRationalMatrixColumnFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalMatrixColumnStep_mem_FP
    machineRationalMatrixColumnInit_mem_FP id_mem_FP
    machineRationalMatrixColumnWidth_mem_FP
    machineRationalMatrixColumnIterate_length_le_width

theorem machineRationalMatrixColumnReversedCode_mem_FP :
    machineRationalMatrixColumnReversedCode ∈ FP := by
  simpa only [machineRationalMatrixColumnReversedCode] using
    machineCompose_mem_FP machineRationalMatrixColumnFinalState_mem_FP
      machineRationalMatrixColumnAccumulator_mem_FP

theorem machineRationalMatrixColumnCode_mem_FP :
    machineRationalMatrixColumnCode ∈ FP := by
  simpa only [machineRationalMatrixColumnCode] using
    machineCompose_mem_FP machineRationalMatrixColumnReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact semantics -/

def rationalColumnOfRows (rows : List (List ℚ)) (j : ℕ) : List ℚ :=
  rows.map fun row => row.getD j 0

def RationalRowsHaveColumn (rows : List (List ℚ)) (j : ℕ) : Prop :=
  ∀ row ∈ rows, j < row.length

theorem rationalEntryCode_getD_length_le
    (row : List ℚ) (j : ℕ) (hj : j < row.length) :
    (rationalEntryBinaryCode (row.getD j 0)).length ≤
      (binaryListCode rationalEntryBinaryCode row).length := by
  have hlength := machineListIndex_length_le_data
    (pair (List.replicate j true)
      (binaryListCode rationalEntryBinaryCode row))
  have hencode := machineListIndex_binaryListCode
    rationalEntryBinaryCode row j hj
  rw [hencode, machineListIndexData, machinePairSecond_pair] at hlength
  simpa only [List.getD_eq_getElem row 0 hj] using hlength

theorem rationalColumnOfRows_code_length_le
    (j : ℕ) : ∀ rows : List (List ℚ),
    RationalRowsHaveColumn rows j →
    (binaryListCode rationalEntryBinaryCode
      (rationalColumnOfRows rows j)).length ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  intro rows
  induction rows with
  | nil => intro h; simp [rationalColumnOfRows, binaryListCode]
  | cons row rows ih =>
      intro hvalid
      have hrow : j < row.length := hvalid row (by simp)
      have htail : RationalRowsHaveColumn rows j := by
        intro r hr
        exact hvalid r (by simp [hr])
      have hentry := rationalEntryCode_getD_length_le row j hrow
      have hrec := ih htail
      have hrec' :
          (binaryListCode rationalEntryBinaryCode
            ((rows.map fun r => r.getD j 0))).length ≤
            (binaryListCode (binaryListCode rationalEntryBinaryCode)
              rows).length := by
        simpa only [rationalColumnOfRows] using hrec
      change
        (pair (rationalEntryBinaryCode (row.getD j 0))
          (binaryListCode rationalEntryBinaryCode
            (rows.map fun r => r.getD j 0))).length ≤
        (pair (binaryListCode rationalEntryBinaryCode row)
          (binaryListCode (binaryListCode rationalEntryBinaryCode)
            rows)).length
      simp only [pair_length]
      omega

theorem rationalColumnOfRows_take_reverse_code_length_le
    (rows : List (List ℚ)) (j k : ℕ)
    (hvalid : RationalRowsHaveColumn rows j) :
    (binaryListCode rationalEntryBinaryCode
      (rationalColumnOfRows (rows.take k) j).reverse).length ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length := by
  have hmap : rationalColumnOfRows (rows.take k) j =
      (rationalColumnOfRows rows j).take k := by
    simp [rationalColumnOfRows, List.map_take]
  rw [hmap]
  exact (binaryListCode_take_reverse_length_le
      rationalEntryBinaryCode (rationalColumnOfRows rows j) k).trans
    (rationalColumnOfRows_code_length_le j rows hvalid)

def machineRationalMatrixColumnSemanticState
    (rows : List (List ℚ)) (j k : ℕ)
    (bound : List Bool) : List Bool :=
  machineRationalMatrixColumnPack
    (binaryListCode (binaryListCode rationalEntryBinaryCode) (rows.drop k))
    (binaryListCode rationalEntryBinaryCode
      (rationalColumnOfRows (rows.take k) j).reverse)
    (List.replicate j true) bound

theorem machineRationalMatrixColumnInit_semantics
    (rows : List (List ℚ)) (j : ℕ) :
    let word := pair (List.replicate j true)
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
    machineRationalMatrixColumnInit word =
      machineRationalMatrixColumnSemanticState rows j 0 word := by
  simp [machineRationalMatrixColumnInit,
    machineRationalMatrixColumnSemanticState,
    machineRationalMatrixColumnRows,
    machineRationalMatrixColumnIndex, rationalColumnOfRows,
    binaryListCode]

theorem machineRationalMatrixColumnStep_semantics
    (rows : List (List ℚ)) (j k : ℕ) (bound : List Bool)
    (hk : k < rows.length)
    (hvalid : RationalRowsHaveColumn rows j)
    (hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        bound.length) :
    machineRationalMatrixColumnStep
        (machineRationalMatrixColumnSemanticState rows j k bound) =
      machineRationalMatrixColumnSemanticState rows j (k + 1) bound := by
  have hdrop := List.drop_eq_getElem_cons hk
  have hrow : j < rows[k].length :=
    hvalid rows[k] (List.getElem_mem hk)
  have hprefix :
      rationalColumnOfRows (rows.take (k + 1)) j =
        rationalColumnOfRows (rows.take k) j ++ [rows[k].getD j 0] := by
    simp only [rationalColumnOfRows, List.map_take]
    have hkm : k <
        (rows.map fun row => row.getD j 0).length := by
      simpa using hk
    simpa using
      (List.take_concat_get
        (l := rows.map fun row => row.getD j 0) hkm).symm
  have hreverse :
      (rationalColumnOfRows (rows.take (k + 1)) j).reverse =
        rows[k].getD j 0 ::
          (rationalColumnOfRows (rows.take k) j).reverse := by
    rw [hprefix, List.reverse_append]
    simp
  have hcand :
      (binaryListCode rationalEntryBinaryCode
        (rationalColumnOfRows (rows.take (k + 1)) j).reverse).length ≤
        bound.length :=
    (rationalColumnOfRows_take_reverse_code_length_le
      rows j (k + 1) hvalid).trans hbound
  have hnonempty :
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rows.drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil
      (binaryListCode rationalEntryBinaryCode) rows[k]
      (rows.drop (k + 1))
  have hcandPair :
      (pair (rationalEntryBinaryCode (rows[k].getD j 0))
        (binaryListCode rationalEntryBinaryCode
          (rationalColumnOfRows (rows.take k) j).reverse)).length ≤
        bound.length := by
    simpa only [hreverse, binaryListCode] using hcand
  rw [machineRationalMatrixColumnStep]
  simp only [machineRationalMatrixColumnSemanticState,
    machineRationalMatrixColumnRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalMatrixColumnAdvance]
  simp only [machineRationalMatrixColumnRemaining_pack,
    machineRationalMatrixColumnAccumulator_pack,
    machineRationalMatrixColumnColumn_pack,
    machineRationalMatrixColumnBound_pack,
    machineRationalMatrixColumnNextAccumulator,
    machineRationalMatrixColumnCandidate,
    machineRationalMatrixColumnCurrentEntry,
    machineRationalMatrixColumnCurrentRow]
  rw [hdrop, machineListHead_cons, machineListTail_cons,
    machineListIndex_binaryListCode rationalEntryBinaryCode rows[k] j hrow]
  rw [← List.getD_eq_getElem rows[k] 0 hrow]
  rw [List.take_of_length_le hcandPair]
  rw [hreverse]
  rfl

theorem machineRationalMatrixColumnIterate_semantics
    (rows : List (List ℚ)) (j : ℕ)
    (hvalid : RationalRowsHaveColumn rows j) : ∀ k ≤ rows.length,
    let word := pair (List.replicate j true)
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
    (machineRationalMatrixColumnStep)^[k]
        (machineRationalMatrixColumnInit word) =
      machineRationalMatrixColumnSemanticState rows j k word := by
  intro k hk
  let word := pair (List.replicate j true)
    (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
  change (machineRationalMatrixColumnStep)^[k]
      (machineRationalMatrixColumnInit word) =
    machineRationalMatrixColumnSemanticState rows j k word
  have hrowsBound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machinePairSecond word).length := by simp [word]
      _ ≤ word.length := machinePairSecond_length_le word
  induction k with
  | zero =>
      simpa only [word] using
        (machineRationalMatrixColumnInit_semantics rows j)
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalMatrixColumnStep_semantics
        rows j k word (by omega) hvalid hrowsBound

theorem machineRationalMatrixColumn_done_iterate
    (extra : ℕ) (accumulator column bound : List Bool) :
    (machineRationalMatrixColumnStep)^[extra]
        (machineRationalMatrixColumnPack [] accumulator column bound) =
      machineRationalMatrixColumnPack [] accumulator column bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalMatrixColumnStep]

theorem machineRationalMatrixColumnReversedCode_encode
    (rows : List (List ℚ)) (j : ℕ)
    (hvalid : RationalRowsHaveColumn rows j) :
    let word := pair (List.replicate j true)
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
    machineRationalMatrixColumnReversedCode word =
      binaryListCode rationalEntryBinaryCode
        (rationalColumnOfRows rows j).reverse := by
  let word := pair (List.replicate j true)
    (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)
  change machineRationalMatrixColumnReversedCode word = _
  have hrowsCode :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        word.length := by
    calc
      _ = (machinePairSecond word).length := by simp [word]
      _ ≤ word.length := machinePairSecond_length_le word
  have hwork : rows.length ≤ word.length :=
    (list_length_le_binaryListCode_length
      (binaryListCode rationalEntryBinaryCode) rows).trans hrowsCode
  have hsplit : word.length = (word.length - rows.length) + rows.length := by
    omega
  rw [machineRationalMatrixColumnReversedCode,
    machineRationalMatrixColumnFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalMatrixColumnIterate_semantics rows j hvalid
      rows.length le_rfl]
  simp only [machineRationalMatrixColumnSemanticState,
    List.drop_length, List.take_length,
    binaryListCode]
  rw [machineRationalMatrixColumn_done_iterate]
  simp

@[simp] theorem machineRationalMatrixColumnCode_rows_encode
    (rows : List (List ℚ)) (j : ℕ)
    (hvalid : RationalRowsHaveColumn rows j) :
    machineRationalMatrixColumnCode
        (pair (List.replicate j true)
          (binaryListCode (binaryListCode rationalEntryBinaryCode) rows)) =
      binaryListCode rationalEntryBinaryCode
        (rationalColumnOfRows rows j) := by
  rw [machineRationalMatrixColumnCode,
    machineRationalMatrixColumnReversedCode_encode rows j hvalid,
    machineListReverse_encode, List.reverse_reverse]

theorem rationalMatrixRows_haveColumn {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (j : Fin d) :
    RationalRowsHaveColumn (rationalMatrixRows A) j.1 := by
  intro row hrow
  rw [rationalMatrixRows] at hrow
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hrow
  subst row
  simp

theorem rationalColumnOfRows_matrix {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (j : Fin d) :
    rationalColumnOfRows (rationalMatrixRows A) j.1 =
      List.ofFn (fun i : Fin d => A i j) := by
  apply List.ext_getElem
  · simp [rationalColumnOfRows, rationalMatrixRows]
  · intro i hiLeft hiRight
    simp only [rationalColumnOfRows, rationalMatrixRows,
      List.getElem_map, List.getElem_ofFn]
    have hj : j.1 <
        (List.ofFn fun j' : Fin d => A ⟨i, by simpa using hiRight⟩ j').length := by
      simp
    rw [List.getD_eq_getElem _ _ hj]
    simp

@[simp] theorem machineRationalMatrixColumnCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (j : Fin d) :
    machineRationalMatrixColumnCode
        (pair (List.replicate j.1 true)
          (rationalSquareMatrixRowsCode A)) =
      rationalFiniteVectorCode (fun i : Fin d => A i j) := by
  rw [rationalSquareMatrixRowsCode,
    machineRationalMatrixColumnCode_rows_encode
      (rationalMatrixRows A) j.1 (rationalMatrixRows_haveColumn A j),
    rationalColumnOfRows_matrix]
  rfl

/-! ## One coordinate of a transpose--vector product -/

/-- Input:
`pair columnUnary (pair nestedMatrixRowsCode rationalVectorCode)`. -/
def machineRationalMatrixTransposeMulVectorEntryCode
    (word : List Bool) : List Bool :=
  let column := machinePairFirst word
  let payload := machinePairSecond word
  let matrixRows := machinePairFirst payload
  let vector := machinePairSecond payload
  machineRationalVectorDotEntryCode
    (pair
      (machineRationalMatrixColumnCode (pair column matrixRows))
      vector)

theorem machineRationalMatrixTransposeMulVectorEntryCode_mem_FP :
    machineRationalMatrixTransposeMulVectorEntryCode ∈ FP := by
  have hcolumn := machinePairFirst_mem_FP
  have hpayload := machinePairSecond_mem_FP
  have hmatrix := machineCompose_mem_FP hpayload machinePairFirst_mem_FP
  have hvector := machineCompose_mem_FP hpayload machinePairSecond_mem_FP
  have hcolumnInput := machinePair_mem_FP hcolumn hmatrix
  have hcolumnCode := machineCompose_mem_FP hcolumnInput
    machineRationalMatrixColumnCode_mem_FP
  have hdotInput := machinePair_mem_FP hcolumnCode hvector
  simpa only [machineRationalMatrixTransposeMulVectorEntryCode] using
    machineCompose_mem_FP hdotInput
      machineRationalVectorDotEntryCode_mem_FP

@[simp] theorem
    machineRationalMatrixTransposeMulVectorEntryCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) (j : Fin d) :
    machineRationalMatrixTransposeMulVectorEntryCode
        (pair (List.replicate j.1 true)
          (pair (rationalSquareMatrixRowsCode A)
            (rationalFiniteVectorCode v))) =
      rationalEntryBinaryCode (∑ i, A i j * v i) := by
  rw [machineRationalMatrixTransposeMulVectorEntryCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair]
  rw [machineRationalMatrixColumnCode_encode,
    machineRationalVectorDotEntryCode_encode]

end BeyondBethe
