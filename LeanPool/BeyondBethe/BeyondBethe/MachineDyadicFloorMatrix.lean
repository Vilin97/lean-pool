/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineDyadicFloorVector

/-!
# Polynomial-time coordinatewise matrix dyadic floor

The outer scan maps the verified vector-floor machine over the encoded rows
of a square rational matrix.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Encodes unary precision `p` followed by the rows of the rational square matrix to round. -/
def dyadicFloorMatrixCanonicalWord {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) : List Bool :=
  pair (List.replicate p true) (rationalSquareMatrixRowsCode A)

theorem dyadicFloorMatrix_entry_code_length_le {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    (rationalEntryBinaryCode (dyadicFloorMatrix p A i j)).length ≤
      100 + 72 * (dyadicFloorMatrixCanonicalWord p A).length := by
  let word := dyadicFloorMatrixCanonicalWord p A
  let q := rawRatOfRat (A i j)
  have hq0 := rawRatWidth_le_binaryCode_length q
  rw [rawRatBinaryCode_rawRatOfRat] at hq0
  let row := List.ofFn fun k : Fin d ↦ A i k
  have hentry := binaryListCode_element_length_le rationalEntryBinaryCode
    (show A i j ∈ row by simp [row])
  have hrow := binaryListCode_element_length_le
    (binaryListCode rationalEntryBinaryCode)
    (show row ∈ rationalMatrixRows A by
      simp [rationalMatrixRows, row])
  have hq : rawRatWidth q ≤ word.length := by
    apply hq0.trans
    apply hentry.trans
    apply hrow.trans
    simp only [word, dyadicFloorMatrixCanonicalWord,
      rationalSquareMatrixRowsCode, pair_length, List.length_replicate]
    omega
  have hp : p ≤ word.length := by
    simp only [word, dyadicFloorMatrixCanonicalWord, pair_length,
      List.length_replicate]
    omega
  have hraw := binaryRawDyadicFloor_width_le p q
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (binaryRawDyadicFloor p q)
  rw [binaryNormalizeRawRat_eq_value, binaryRawDyadicFloor_value,
    binaryDyadicFloor_eq_dyadicFloor, rawRatOfRat_value] at hcanonical
  exact hcanonical.trans (by nlinarith)

/-- Reuses the rational transpose-vector input bound to bound the dyadic matrix scan. -/
def machineDyadicFloorMatrixInputBound (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineDyadicFloorMatrixInputBound_mem_FP :
    machineDyadicFloorMatrixInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem dyadicFloorMatrix_code_length_le_cubic {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    (rationalSquareMatrixRowsCode (dyadicFloorMatrix p A)).length ≤
      d * (2 * (d *
        (2 * (100 + 72 * (dyadicFloorMatrixCanonicalWord p A).length) +
          2)) + 2) := by
  let L := 100 + 72 * (dyadicFloorMatrixCanonicalWord p A).length
  have hentry : ∀ i j : Fin d,
      (rationalEntryBinaryCode (dyadicFloorMatrix p A i j)).length ≤ L := by
    intro i j
    exact dyadicFloorMatrix_entry_code_length_le p A i j
  rw [rationalSquareMatrixRowsCode, binaryListCode_length_eq_sum]
  simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  calc
    (∑ i : Fin d,
        (2 * (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ dyadicFloorMatrix p A i j)).length + 2)) ≤
      ∑ _i : Fin d, (2 * (d * (2 * L + 2)) + 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        rw [binaryListCode_length_eq_sum]
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
        calc
          (∑ j : Fin d,
              (2 * (rationalEntryBinaryCode
                (dyadicFloorMatrix p A i j)).length + 2)) ≤
            ∑ _j : Fin d, (2 * L + 2) := by
              apply Finset.sum_le_sum
              intro j _
              have h := hentry i j
              omega
          _ = d * (2 * L + 2) := by simp
    _ = d * (2 * (d * (2 * L + 2)) + 2) := by simp

theorem dyadicFloorMatrix_code_length_le_bound {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    (rationalSquareMatrixRowsCode (dyadicFloorMatrix p A)).length ≤
      (machineDyadicFloorMatrixInputBound
        (dyadicFloorMatrixCanonicalWord p A)).length := by
  let word := dyadicFloorMatrixCanonicalWord p A
  let n := word.length
  let x := 16 + n
  let y := 16 + x ^ 2
  let z := 16 + y ^ 2
  have hd : d ≤ word.length := by
    have hrows := binaryListCode_listLength_le
      (binaryListCode rationalEntryBinaryCode) (rationalMatrixRows A)
    have hmatrix : (rationalSquareMatrixRowsCode A).length ≤ word.length := by
      simp only [word, dyadicFloorMatrixCanonicalWord, pair_length,
        List.length_replicate]
      omega
    simpa only [rationalSquareMatrixRowsCode, rationalMatrixRows,
      List.length_ofFn] using! hrows.trans hmatrix
  have hn2 : 2 ≤ n := by
    simp only [n, word, dyadicFloorMatrixCanonicalWord, pair_length,
      List.length_replicate]
    omega
  have hcubic := dyadicFloorMatrix_code_length_le_cubic p A
  have hd' : d ≤ n := by simpa only [n] using! hd
  have hdd : d * d ≤ n * n := Nat.mul_le_mul hd' hd'
  have hddn : (d * d) * n ≤ (n * n) * n :=
    Nat.mul_le_mul hdd le_rfl
  have hpoly :
      d * (2 * (d * (2 * (100 + 72 * n) + 2)) + 2) ≤
        1000 * n ^ 3 := by
    nlinarith
  have hout :
      (rationalSquareMatrixRowsCode (dyadicFloorMatrix p A)).length ≤
        1000 * n ^ 3 := by
    apply hcubic.trans
    simpa only [n, word] using! hpoly
  have hnx : n ≤ x := by simp [x]
  have hxpos : 0 < x := by omega
  have h1000 : 1000 ≤ x ^ 3 := by
    dsimp only [x]
    nlinarith
  have hnx3 : n ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hnx 3
  have hto6 : 1000 * n ^ 3 ≤ x ^ 6 := by
    have h := Nat.mul_le_mul h1000 hnx3
    simpa only [← pow_add] using! h
  have hto8 : x ^ 6 ≤ x ^ 8 :=
    Nat.pow_le_pow_right hxpos (by omega)
  have hxy : x ^ 2 ≤ y := by simp [y]
  have hx4y2 : x ^ 4 ≤ y ^ 2 := by
    have h := Nat.pow_le_pow_left hxy 2
    simpa only [← pow_mul] using! h
  have hyz : y ^ 2 ≤ z := by simp [z]
  have hx4z : x ^ 4 ≤ z := hx4y2.trans hyz
  have hx8z2 : x ^ 8 ≤ z ^ 2 := by
    have h := Nat.pow_le_pow_left hx4z 2
    simpa only [← pow_mul] using! h
  apply hout.trans
  apply hto6.trans
  apply hto8.trans
  apply hx8z2.trans_eq
  simp only [machineDyadicFloorMatrixInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, n, x, y, z, word, pow_two]

/-! ## Bounded outer row scan -/

/-- Extracts the unary rounding precision from a dyadic matrix request. -/
def machineDyadicFloorMatrixPrecision (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the encoded matrix rows from a dyadic matrix request. -/
def machineDyadicFloorMatrixRows (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Rounds every entry of the next unprocessed matrix row using the precision stored in the scan
payload. -/
def machineDyadicFloorMatrixCurrentRow (state : List Bool) : List Bool :=
  machineDyadicFloorVectorCode
    (pair (machineRationalTransposeMulVectorStatePayload state)
      (machineListHead
        (machineRationalTransposeMulVectorRemaining state)))

/-- Prepends the newly rounded row to the encoded reverse-order accumulator. -/
def machineDyadicFloorMatrixCandidate (state : List Bool) : List Bool :=
  pair (machineDyadicFloorMatrixCurrentRow state)
    (machineRationalTransposeMulVectorAccumulator state)

/-- Truncates the candidate row accumulator to the length of the scan bound word. -/
def machineDyadicFloorMatrixNextAccumulator
    (state : List Bool) : List Bool :=
  (machineDyadicFloorMatrixCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

/-- Drops the processed matrix row and stores the bounded updated accumulator while preserving
precision and bound. -/
def machineDyadicFloorMatrixAdvance (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineDyadicFloorMatrixNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

/-- Fixes a matrix scan with no remaining rows and otherwise processes its next row. -/
def machineDyadicFloorMatrixStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineDyadicFloorMatrixAdvance state)

/-- Initializes the matrix scan with all input rows, an empty accumulator, the requested
precision, and its input bound. -/
def machineDyadicFloorMatrixInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineDyadicFloorMatrixRows word) []
    (machineDyadicFloorMatrixPrecision word)
    (machineDyadicFloorMatrixInputBound word)

/-- Packs four copies of the input bound to bound the encoded matrix scan state. -/
def machineDyadicFloorMatrixWidth (word : List Bool) : List Bool :=
  let bound := machineDyadicFloorMatrixInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

/-- Runs the dyadic matrix scan for as many steps as there are bits in the input word. -/
def machineDyadicFloorMatrixFinalState (word : List Bool) : List Bool :=
  (machineDyadicFloorMatrixStep)^[word.length]
    (machineDyadicFloorMatrixInit word)

/-- Extracts the reversed encoded rounded rows from the final matrix scan state. -/
def machineDyadicFloorMatrixReversedCode (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineDyadicFloorMatrixFinalState word)

/-- Reverses the accumulated rounded rows to recover the original matrix row order. -/
def machineDyadicFloorMatrixCode (word : List Bool) : List Bool :=
  machineListReverse (machineDyadicFloorMatrixReversedCode word)

theorem machineDyadicFloorMatrixPrecision_mem_FP :
    machineDyadicFloorMatrixPrecision ∈ FP := machinePairFirst_mem_FP

theorem machineDyadicFloorMatrixRows_mem_FP :
    machineDyadicFloorMatrixRows ∈ FP := machinePairSecond_mem_FP

theorem machineDyadicFloorMatrixCurrentRow_mem_FP :
    machineDyadicFloorMatrixCurrentRow ∈ FP := by
  have hhead := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListHead_mem_FP
  have hinput := machinePair_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP hhead
  simpa only [machineDyadicFloorMatrixCurrentRow] using!
    machineCompose_mem_FP hinput machineDyadicFloorVectorCode_mem_FP

theorem machineDyadicFloorMatrixCandidate_mem_FP :
    machineDyadicFloorMatrixCandidate ∈ FP :=
  machinePair_mem_FP machineDyadicFloorMatrixCurrentRow_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineDyadicFloorMatrixNextAccumulator_mem_FP :
    machineDyadicFloorMatrixNextAccumulator ∈ FP := by
  simpa only [machineDyadicFloorMatrixNextAccumulator] using!
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineDyadicFloorMatrixCandidate_mem_FP

theorem machineDyadicFloorMatrixAdvance_mem_FP :
    machineDyadicFloorMatrixAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineDyadicFloorMatrixNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineDyadicFloorMatrixStep_mem_FP :
    machineDyadicFloorMatrixStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineDyadicFloorMatrixAdvance_mem_FP

theorem machineDyadicFloorMatrixInit_mem_FP :
    machineDyadicFloorMatrixInit ∈ FP :=
  machinePair_mem_FP machineDyadicFloorMatrixRows_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineDyadicFloorMatrixPrecision_mem_FP
        machineDyadicFloorMatrixInputBound_mem_FP))

theorem machineDyadicFloorMatrixWidth_mem_FP :
    machineDyadicFloorMatrixWidth ∈ FP := by
  have hbound := machineDyadicFloorMatrixInputBound_mem_FP
  exact machinePair_mem_FP hbound
    (machinePair_mem_FP hbound (machinePair_mem_FP hbound hbound))

theorem machineDyadicFloorMatrixInit_bound (word : List Bool) :
    MachineRationalTransposeMulVectorStateBound word
      (machineDyadicFloorMatrixInit word) := by
  simp only [MachineRationalTransposeMulVectorStateBound,
    machineDyadicFloorMatrixInit,
    machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineDyadicFloorMatrixInputBound]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · exact (machinePairSecond_length_le word).trans
      (machineRationalTransposeMulVector_word_le_bound word)
  · exact (machinePairFirst_length_le word).trans
      (machineRationalTransposeMulVector_word_le_bound word)

theorem machineDyadicFloorMatrixStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineDyadicFloorMatrixStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineDyadicFloorMatrixStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineDyadicFloorMatrixStep, hcode, machineIfEmpty_cons,
          machineDyadicFloorMatrixAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineDyadicFloorMatrixNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineDyadicFloorMatrixIterate_bound (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineDyadicFloorMatrixStep)^[k]
        (machineDyadicFloorMatrixInit word)) := by
  intro k
  induction k with
  | zero => exact machineDyadicFloorMatrixInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineDyadicFloorMatrixStep_bound ih

theorem machineDyadicFloorMatrixIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineDyadicFloorMatrixStep)^[iterations]
      (machineDyadicFloorMatrixInit word)).length ≤
        (machineDyadicFloorMatrixWidth word).length := by
  rcases machineDyadicFloorMatrixIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineDyadicFloorMatrixWidth, machineDyadicFloorMatrixInputBound,
    pair_length]
  omega

theorem machineDyadicFloorMatrixFinalState_mem_FP :
    machineDyadicFloorMatrixFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineDyadicFloorMatrixStep_mem_FP
    machineDyadicFloorMatrixInit_mem_FP id_mem_FP
    machineDyadicFloorMatrixWidth_mem_FP
    machineDyadicFloorMatrixIterate_length_le_width

theorem machineDyadicFloorMatrixReversedCode_mem_FP :
    machineDyadicFloorMatrixReversedCode ∈ FP := by
  simpa only [machineDyadicFloorMatrixReversedCode] using!
    machineCompose_mem_FP machineDyadicFloorMatrixFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineDyadicFloorMatrixCode_mem_FP :
    machineDyadicFloorMatrixCode ∈ FP := by
  simpa only [machineDyadicFloorMatrixCode] using!
    machineCompose_mem_FP machineDyadicFloorMatrixReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact scan semantics -/

/-- Takes the first `k` rational matrix rows and applies dyadic floor at precision `p` to every
entry. -/
def dyadicFloorMatrixRowsPrefix {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) : List (List ℚ) :=
  (rationalMatrixRows A).take k |>.map
    (List.map (dyadicFloor p))

/-- Encodes the remaining matrix rows and reversed rounded prefix after `k` rows, retaining the
canonical precision and input bound. -/
def machineDyadicFloorMatrixSemanticState {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) : List Bool :=
  let word := dyadicFloorMatrixCanonicalWord p A
  machineRationalTransposeMulVectorPack
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      ((rationalMatrixRows A).drop k))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (dyadicFloorMatrixRowsPrefix p A k).reverse)
    (List.replicate p true) (machineDyadicFloorMatrixInputBound word)

theorem machineDyadicFloorMatrixInit_semantics {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    machineDyadicFloorMatrixInit (dyadicFloorMatrixCanonicalWord p A) =
      machineDyadicFloorMatrixSemanticState p A 0 := by
  simp [machineDyadicFloorMatrixInit,
    machineDyadicFloorMatrixSemanticState, machineDyadicFloorMatrixRows,
    machineDyadicFloorMatrixPrecision, dyadicFloorMatrixCanonicalWord,
    rationalSquareMatrixRowsCode, dyadicFloorMatrixRowsPrefix,
    binaryListCode]

theorem dyadicFloorMatrixRowsPrefix_succ {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ)
    (k : ℕ) (hk : k < d) :
    dyadicFloorMatrixRowsPrefix p A (k + 1) =
      dyadicFloorMatrixRowsPrefix p A k ++
        [List.ofFn fun j ↦ dyadicFloor p (A ⟨k, hk⟩ j)] := by
  simp only [dyadicFloorMatrixRowsPrefix, List.map_take]
  have hkm : k < (rationalMatrixRows A).length := by
    simp [rationalMatrixRows, hk]
  simpa [rationalMatrixRows, List.map_ofFn] using!
    congrArg (List.map (List.map (dyadicFloor p)))
      (List.take_concat_get hkm).symm

theorem machineDyadicFloorMatrixStep_semantics {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ)
    (k : ℕ) (hk : k < d) :
    machineDyadicFloorMatrixStep
        (machineDyadicFloorMatrixSemanticState p A k) =
      machineDyadicFloorMatrixSemanticState p A (k + 1) := by
  let word := dyadicFloorMatrixCanonicalWord p A
  let row := List.ofFn fun j : Fin d ↦ A ⟨k, hk⟩ j
  have hdrop : (rationalMatrixRows A).drop k =
      row :: (rationalMatrixRows A).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (rationalMatrixRows A).length by
        simp [rationalMatrixRows, hk]) using 1
    simp [rationalMatrixRows, row]
  have hprefix := dyadicFloorMatrixRowsPrefix_succ p A k hk
  let roundedRow := List.ofFn fun j : Fin d ↦ dyadicFloor p (A ⟨k, hk⟩ j)
  have hreverse : (dyadicFloorMatrixRowsPrefix p A (k + 1)).reverse =
      roundedRow :: (dyadicFloorMatrixRowsPrefix p A k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [roundedRow]
  have hcand :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (dyadicFloorMatrixRowsPrefix p A (k + 1)).reverse).length ≤
        (machineDyadicFloorMatrixInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows (dyadicFloorMatrix p A)) (k + 1)
    have hprefixEq : dyadicFloorMatrixRowsPrefix p A (k + 1) =
        (rationalMatrixRows (dyadicFloorMatrix p A)).take (k + 1) := by
      apply List.ext_getElem
      · simp [dyadicFloorMatrixRowsPrefix, rationalMatrixRows]
      · intro r hrLeft hrRight
        simp [dyadicFloorMatrixRowsPrefix, rationalMatrixRows,
          List.map_ofFn]
        funext j
        rfl
    rw [hprefixEq]
    exact hprefixBound.trans (dyadicFloorMatrix_code_length_le_bound p A)
  have hcandPair :
      (pair (binaryListCode rationalEntryBinaryCode roundedRow)
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (dyadicFloorMatrixRowsPrefix p A k).reverse)).length ≤
        (machineDyadicFloorMatrixInputBound word).length := by
    simpa only [hreverse, binaryListCode] using! hcand
  have hnonempty :
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        ((rationalMatrixRows A).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil
      (binaryListCode rationalEntryBinaryCode) row
      ((rationalMatrixRows A).drop (k + 1))
  rw [machineDyadicFloorMatrixStep]
  simp only [machineDyadicFloorMatrixSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineDyadicFloorMatrixAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineDyadicFloorMatrixNextAccumulator,
    machineDyadicFloorMatrixCandidate,
    machineDyadicFloorMatrixCurrentRow]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineDyadicFloorVectorCode
          (pair (List.replicate p true)
            (binaryListCode rationalEntryBinaryCode row)))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (dyadicFloorMatrixRowsPrefix p A k).reverse)).take
        (machineDyadicFloorMatrixInputBound word).length) _ _ = _
  let rowFn : Fin d → ℚ := fun j ↦ A ⟨k, hk⟩ j
  change machineRationalTransposeMulVectorPack _
      ((pair (machineDyadicFloorVectorCode
          (dyadicFloorVectorCanonicalWord p rowFn))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (dyadicFloorMatrixRowsPrefix p A k).reverse)).take
        (machineDyadicFloorMatrixInputBound word).length) _ _ = _
  rw [machineDyadicFloorVectorCode_encode]
  change machineRationalTransposeMulVectorPack _
      ((pair (binaryListCode rationalEntryBinaryCode roundedRow)
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (dyadicFloorMatrixRowsPrefix p A k).reverse)).take
        (machineDyadicFloorMatrixInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineDyadicFloorMatrixIterate_semantics {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) : ∀ k ≤ d,
    (machineDyadicFloorMatrixStep)^[k]
      (machineDyadicFloorMatrixInit
        (dyadicFloorMatrixCanonicalWord p A)) =
      machineDyadicFloorMatrixSemanticState p A k := by
  intro k hk
  induction k with
  | zero => exact machineDyadicFloorMatrixInit_semantics p A
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineDyadicFloorMatrixStep_semantics p A k (by omega)

theorem machineDyadicFloorMatrix_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineDyadicFloorMatrixStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineDyadicFloorMatrixStep]

theorem dyadicFloorMatrixRowsPrefix_all {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    dyadicFloorMatrixRowsPrefix p A d =
      rationalMatrixRows (dyadicFloorMatrix p A) := by
  apply List.ext_getElem
  · simp [dyadicFloorMatrixRowsPrefix, rationalMatrixRows]
  · intro i hiLeft hiRight
    simp [dyadicFloorMatrixRowsPrefix, rationalMatrixRows, List.map_ofFn]
    funext j
    rfl

theorem machineDyadicFloorMatrixReversedCode_encode {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    machineDyadicFloorMatrixReversedCode
        (dyadicFloorMatrixCanonicalWord p A) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows (dyadicFloorMatrix p A)).reverse := by
  let word := dyadicFloorMatrixCanonicalWord p A
  have hd : d ≤ word.length := by
    have hrows := binaryListCode_listLength_le
      (binaryListCode rationalEntryBinaryCode) (rationalMatrixRows A)
    have hmatrix : (rationalSquareMatrixRowsCode A).length ≤ word.length := by
      simp only [word, dyadicFloorMatrixCanonicalWord, pair_length,
        List.length_replicate]
      omega
    simpa only [rationalSquareMatrixRowsCode, rationalMatrixRows,
      List.length_ofFn] using! hrows.trans hmatrix
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineDyadicFloorMatrixReversedCode word = _
  rw [machineDyadicFloorMatrixReversedCode,
    machineDyadicFloorMatrixFinalState, hsplit,
    Function.iterate_add_apply,
    machineDyadicFloorMatrixIterate_semantics p A d le_rfl]
  simp only [machineDyadicFloorMatrixSemanticState]
  rw [show binaryListCode (binaryListCode rationalEntryBinaryCode)
      ((rationalMatrixRows A).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp [rationalMatrixRows])]
    rfl]
  rw [machineDyadicFloorMatrix_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [dyadicFloorMatrixRowsPrefix_all]

@[simp] theorem machineDyadicFloorMatrixCode_encode {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :
    machineDyadicFloorMatrixCode
        (dyadicFloorMatrixCanonicalWord p A) =
      rationalSquareMatrixRowsCode (dyadicFloorMatrix p A) := by
  rw [machineDyadicFloorMatrixCode,
    machineDyadicFloorMatrixReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
