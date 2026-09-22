/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMatrixMulVector

/-!
# Polynomial-time rational matrix multiplication

This module gives an ordinary finite-word implementation of exact square
matrix multiplication.  A row of `A * B` is obtained as `Bᵀ` times the
corresponding row of `A`; the already verified transpose--vector machine
therefore supplies the arithmetic kernel.  A bounded outer scan assembles
the rows.
-/

namespace BeyondBethe

open Complexity

def rationalMatrixMul {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j ↦ ∑ k, A i k * B k j

theorem rationalMatrixMul_eq_matrix_mul {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixMul A B = A * B := by
  rfl

def rationalMatrixMulCanonicalWord {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair (rationalSquareMatrixRowsCode A)
      (rationalSquareMatrixRowsCode B))

def machineRationalMatrixMulDimensionUnary
    (word : List Bool) : List Bool := machinePairFirst word

def machineRationalMatrixMulMatrices
    (word : List Bool) : List Bool := machinePairSecond word

def machineRationalMatrixMulLeftRows
    (word : List Bool) : List Bool :=
  machinePairFirst (machineRationalMatrixMulMatrices word)

def machineRationalMatrixMulRightRows
    (word : List Bool) : List Bool :=
  machinePairSecond (machineRationalMatrixMulMatrices word)

/-- Input: `pair rowUnary canonicalMatrixMulWord`. -/
def machineRationalMatrixMulRowCode
    (word : List Bool) : List Bool :=
  let rowUnary := machinePairFirst word
  let payload := machinePairSecond word
  let leftRow := machineListIndex
    (pair rowUnary (machineRationalMatrixMulLeftRows payload))
  machineRationalTransposeMulVectorCode
    (pair (machineRationalMatrixMulDimensionUnary payload)
      (pair (machineRationalMatrixMulRightRows payload) leftRow))

theorem machineRationalMatrixMulDimensionUnary_mem_FP :
    machineRationalMatrixMulDimensionUnary ∈ FP := machinePairFirst_mem_FP

theorem machineRationalMatrixMulMatrices_mem_FP :
    machineRationalMatrixMulMatrices ∈ FP := machinePairSecond_mem_FP

theorem machineRationalMatrixMulLeftRows_mem_FP :
    machineRationalMatrixMulLeftRows ∈ FP := by
  simpa only [machineRationalMatrixMulLeftRows] using!
    machineCompose_mem_FP machineRationalMatrixMulMatrices_mem_FP
      machinePairFirst_mem_FP

theorem machineRationalMatrixMulRightRows_mem_FP :
    machineRationalMatrixMulRightRows ∈ FP := by
  simpa only [machineRationalMatrixMulRightRows] using!
    machineCompose_mem_FP machineRationalMatrixMulMatrices_mem_FP
      machinePairSecond_mem_FP

theorem machineRationalMatrixMulRowCode_mem_FP :
    machineRationalMatrixMulRowCode ∈ FP := by
  have hrow := machinePairFirst_mem_FP
  have hpayload := machinePairSecond_mem_FP
  have hleftRows := machineCompose_mem_FP hpayload
    machineRationalMatrixMulLeftRows_mem_FP
  have hleftRow := machineCompose_mem_FP
    (machinePair_mem_FP hrow hleftRows) machineListIndex_mem_FP
  have hdim := machineCompose_mem_FP hpayload
    machineRationalMatrixMulDimensionUnary_mem_FP
  have hrightRows := machineCompose_mem_FP hpayload
    machineRationalMatrixMulRightRows_mem_FP
  have hinput := machinePair_mem_FP hdim
    (machinePair_mem_FP hrightRows hleftRow)
  simpa only [machineRationalMatrixMulRowCode] using!
    machineCompose_mem_FP hinput machineRationalTransposeMulVectorCode_mem_FP

theorem rationalTransposeMulVector_row_eq_matrixMul {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    rationalTransposeMulVector B (fun k ↦ A i k) =
      fun j ↦ rationalMatrixMul A B i j := by
  funext j
  simp only [rationalTransposeMulVector, rationalMatrixMul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

@[simp] theorem machineRationalMatrixMulRowCode_encode {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    machineRationalMatrixMulRowCode
        (pair (List.replicate i.1 true)
          (rationalMatrixMulCanonicalWord A B)) =
      rationalFiniteVectorCode (fun j ↦ rationalMatrixMul A B i j) := by
  rw [machineRationalMatrixMulRowCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    machineRationalMatrixMulLeftRows,
    machineRationalMatrixMulRightRows,
    machineRationalMatrixMulMatrices,
    machineRationalMatrixMulDimensionUnary,
    rationalMatrixMulCanonicalWord,
    rationalSquareMatrixRowsCode]
  rw [machineListIndex_binaryListCode]
  · simp only [rationalMatrixRows, List.getElem_ofFn]
    change machineRationalTransposeMulVectorCode
        (rationalTransposeMulVectorCanonicalWord B (fun k ↦ A i k)) = _
    rw [machineRationalTransposeMulVectorCode_encode,
      rationalTransposeMulVector_row_eq_matrixMul]
  · simp [rationalMatrixRows]

/-! ## A global ordinary-binary output bound -/

def rawRationalMatrixMulCoordinate {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) : RawRat :=
  rawRatListDot RawRat.zero (List.ofFn fun k ↦ A i k)
    (rationalColumnOfRows (rationalMatrixRows B) j.1)

theorem rawRationalMatrixMulCoordinate_value {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    (rawRationalMatrixMulCoordinate A B i j).value =
      rationalMatrixMul A B i j := by
  rw [rawRationalMatrixMulCoordinate,
    rationalColumnOfRows_matrix, rawRatListDot_ofFn_value]
  rfl

theorem rawRationalMatrixMulCoordinate_width_le_word {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    rawRatWidth (rawRationalMatrixMulCoordinate A B i j) ≤
      (rationalMatrixMulCanonicalWord A B).length := by
  let row := List.ofFn fun k : Fin d ↦ A i k
  let column := rationalColumnOfRows (rationalMatrixRows B) j.1
  have hwidth := rawRatWidth_listDot_le RawRat.zero row column
  simp only [rawRatWidth_zero] at hwidth
  have hcost := rawRatListDotCost_le_codeLength row column
  have hrow :
      (binaryListCode rationalEntryBinaryCode row).length ≤
        (rationalSquareMatrixRowsCode A).length := by
    have helem := binaryListCode_element_length_le
      (binaryListCode rationalEntryBinaryCode)
      (show row ∈ rationalMatrixRows A by
        simp [rationalMatrixRows, row])
    simpa only [rationalSquareMatrixRowsCode] using! helem
  have hcolumn :
      (binaryListCode rationalEntryBinaryCode column).length ≤
        (rationalSquareMatrixRowsCode B).length := by
    simpa only [column, rationalSquareMatrixRowsCode] using!
      rationalColumnOfRows_code_length_le j.1
        (rationalMatrixRows B) (rationalMatrixRows_haveColumn B j)
  have hcombined :
      1 + (binaryListCode rationalEntryBinaryCode row).length +
        (binaryListCode rationalEntryBinaryCode column).length ≤
          (rationalMatrixMulCanonicalWord A B).length := by
    simp only [rationalMatrixMulCanonicalWord, pair_length,
      List.length_replicate]
    omega
  change rawRatWidth (rawRatListDot RawRat.zero row column) ≤ _
  omega

theorem rationalMatrixMul_entry_code_length_le {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    (rationalEntryBinaryCode (rationalMatrixMul A B i j)).length ≤
      64 + 36 * (rationalMatrixMulCanonicalWord A B).length := by
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (rawRationalMatrixMulCoordinate A B i j)
  rw [binaryNormalizeRawRat_eq_value,
    rawRationalMatrixMulCoordinate_value] at hcanonical
  exact hcanonical.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 36
      (rawRationalMatrixMulCoordinate_width_le_word A B i j)) 64)

def machineRationalMatrixMulInputBound (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineRationalMatrixMulInputBound_mem_FP :
    machineRationalMatrixMulInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem rationalMatrixMul_code_length_le_cubic {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    (rationalSquareMatrixRowsCode (rationalMatrixMul A B)).length ≤
      d * (2 * (d *
        (2 * (64 + 36 * (rationalMatrixMulCanonicalWord A B).length) + 2)) +
        2) := by
  let L := 64 + 36 * (rationalMatrixMulCanonicalWord A B).length
  have hentry : ∀ i j : Fin d,
      (rationalEntryBinaryCode (rationalMatrixMul A B i j)).length ≤ L := by
    intro i j
    exact rationalMatrixMul_entry_code_length_le A B i j
  rw [rationalSquareMatrixRowsCode, binaryListCode_length_eq_sum]
  simp only [rationalMatrixRows, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  calc
    (∑ i : Fin d,
        (2 * (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalMatrixMul A B i j)).length + 2)) ≤
      ∑ _i : Fin d, (2 * (d * (2 * L + 2)) + 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        rw [binaryListCode_length_eq_sum]
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
        calc
          (∑ j : Fin d,
              (2 * (rationalEntryBinaryCode
                (rationalMatrixMul A B i j)).length + 2)) ≤
            ∑ _j : Fin d, (2 * L + 2) := by
              apply Finset.sum_le_sum
              intro j _
              have h := hentry i j
              omega
          _ = d * (2 * L + 2) := by simp [mul_comm]
    _ = d * (2 * (d * (2 * L + 2)) + 2) := by simp [mul_comm]

theorem rationalMatrixMul_code_length_le_bound {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    (rationalSquareMatrixRowsCode (rationalMatrixMul A B)).length ≤
      (machineRationalMatrixMulInputBound
        (rationalMatrixMulCanonicalWord A B)).length := by
  let word := rationalMatrixMulCanonicalWord A B
  let n := word.length
  let x := 16 + n
  let y := 16 + x ^ 2
  let z := 16 + y ^ 2
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalMatrixMulCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! h
  have hn4 : 4 ≤ n := by
    simp only [n, word, rationalMatrixMulCanonicalWord, pair_length,
      List.length_replicate]
    omega
  have hcubic := rationalMatrixMul_code_length_le_cubic A B
  have hd' : d ≤ n := by simpa only [n] using! hd
  have hdn : d * n ≤ n * n := Nat.mul_le_mul hd' le_rfl
  have hdd : d * d ≤ n * n := Nat.mul_le_mul hd' hd'
  have hddn : (d * d) * n ≤ (n * n) * n :=
    Nat.mul_le_mul hdd le_rfl
  have hpoly :
      d * (2 * (d * (2 * (64 + 36 * n) + 2)) + 2) ≤
        211 * n ^ 3 := by
    nlinarith
  have hout :
      (rationalSquareMatrixRowsCode (rationalMatrixMul A B)).length ≤
        211 * n ^ 3 := by
    apply hcubic.trans
    simpa only [n, word] using! hpoly
  have hnx : n ≤ x := by simp [x]
  have hxpos : 0 < x := by omega
  have h211 : 211 ≤ x ^ 2 := by
    dsimp only [x]
    nlinarith
  have hnx3 : n ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hnx 3
  have hto5 : 211 * n ^ 3 ≤ x ^ 5 := by
    have h := Nat.mul_le_mul h211 hnx3
    simpa only [pow_succ, pow_two, mul_assoc, mul_left_comm,
      mul_comm] using! h
  have hto8 : x ^ 5 ≤ x ^ 8 :=
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
  apply hto5.trans
  apply hto8.trans
  apply hx8z2.trans_eq
  simp only [machineRationalMatrixMulInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, n, x, y, z, word, pow_two]

/-! ## Bounded outer row scan -/

def machineRationalMatrixMulIndices (word : List Bool) : List Bool :=
  machineUnaryRangeCode (machineRationalMatrixMulDimensionUnary word)

def machineRationalMatrixMulCurrentRow (state : List Bool) : List Bool :=
  machineRationalMatrixMulRowCode
    (pair (machineRationalTransposeMulVectorCurrentIndex state)
      (machineRationalTransposeMulVectorStatePayload state))

def machineRationalMatrixMulCandidate (state : List Bool) : List Bool :=
  pair (machineRationalMatrixMulCurrentRow state)
    (machineRationalTransposeMulVectorAccumulator state)

def machineRationalMatrixMulNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalMatrixMulCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

def machineRationalMatrixMulAdvance (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineRationalMatrixMulNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

def machineRationalMatrixMulStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineRationalMatrixMulAdvance state)

def machineRationalMatrixMulInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineRationalMatrixMulIndices word) [] word
    (machineRationalMatrixMulInputBound word)

def machineRationalMatrixMulWidth (word : List Bool) : List Bool :=
  let bound := machineRationalMatrixMulInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

def machineRationalMatrixMulFinalState (word : List Bool) : List Bool :=
  (machineRationalMatrixMulStep)^[word.length]
    (machineRationalMatrixMulInit word)

def machineRationalMatrixMulReversedCode (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineRationalMatrixMulFinalState word)

/-- Input: `pair dimensionUnary (pair leftRowsCode rightRowsCode)`. -/
def machineRationalMatrixMulCode (word : List Bool) : List Bool :=
  machineListReverse (machineRationalMatrixMulReversedCode word)

theorem machineRationalMatrixMulIndices_mem_FP :
    machineRationalMatrixMulIndices ∈ FP := by
  simpa only [machineRationalMatrixMulIndices] using!
    machineCompose_mem_FP machineRationalMatrixMulDimensionUnary_mem_FP
      machineUnaryRangeCode_mem_FP

theorem machineRationalMatrixMulCurrentRow_mem_FP :
    machineRationalMatrixMulCurrentRow ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalTransposeMulVectorCurrentIndex_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP
  simpa only [machineRationalMatrixMulCurrentRow] using!
    machineCompose_mem_FP hinput machineRationalMatrixMulRowCode_mem_FP

theorem machineRationalMatrixMulCandidate_mem_FP :
    machineRationalMatrixMulCandidate ∈ FP :=
  machinePair_mem_FP machineRationalMatrixMulCurrentRow_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalMatrixMulNextAccumulator_mem_FP :
    machineRationalMatrixMulNextAccumulator ∈ FP := by
  simpa only [machineRationalMatrixMulNextAccumulator] using!
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineRationalMatrixMulCandidate_mem_FP

theorem machineRationalMatrixMulAdvance_mem_FP :
    machineRationalMatrixMulAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalMatrixMulNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineRationalMatrixMulStep_mem_FP :
    machineRationalMatrixMulStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineRationalMatrixMulAdvance_mem_FP

theorem machineRationalMatrixMulInit_mem_FP :
    machineRationalMatrixMulInit ∈ FP := by
  exact machinePair_mem_FP machineRationalMatrixMulIndices_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP id_mem_FP
        machineRationalMatrixMulInputBound_mem_FP))

theorem machineRationalMatrixMulWidth_mem_FP :
    machineRationalMatrixMulWidth ∈ FP := by
  have hbound := machineRationalMatrixMulInputBound_mem_FP
  exact machinePair_mem_FP hbound
    (machinePair_mem_FP hbound (machinePair_mem_FP hbound hbound))

theorem machineRationalMatrixMulInit_bound (word : List Bool) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalMatrixMulInit word) := by
  simp only [MachineRationalTransposeMulVectorStateBound,
    machineRationalMatrixMulInit,
    machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalMatrixMulInputBound]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · simpa only [machineRationalMatrixMulIndices,
      machineRationalMatrixMulDimensionUnary,
      machineRationalTransposeMulVectorIndices,
      machineRationalTransposeMulVectorDimension] using!
        machineRationalTransposeMulVector_indices_le_bound word
  · exact machineRationalTransposeMulVector_word_le_bound word

theorem machineRationalMatrixMulStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalMatrixMulStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineRationalMatrixMulStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineRationalMatrixMulStep, hcode, machineIfEmpty_cons,
          machineRationalMatrixMulAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineRationalMatrixMulNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalMatrixMulIterate_bound (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineRationalMatrixMulStep)^[k]
        (machineRationalMatrixMulInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalMatrixMulInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalMatrixMulStep_bound ih

theorem machineRationalMatrixMulIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalMatrixMulStep)^[iterations]
      (machineRationalMatrixMulInit word)).length ≤
        (machineRationalMatrixMulWidth word).length := by
  rcases machineRationalMatrixMulIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp]
  change (machineRationalTransposeMulVectorPack _ _ _ _).length ≤ _
  rw [hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineRationalMatrixMulWidth, machineRationalMatrixMulInputBound,
    pair_length]
  omega

theorem machineRationalMatrixMulFinalState_mem_FP :
    machineRationalMatrixMulFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalMatrixMulStep_mem_FP
    machineRationalMatrixMulInit_mem_FP id_mem_FP
    machineRationalMatrixMulWidth_mem_FP
    machineRationalMatrixMulIterate_length_le_width

theorem machineRationalMatrixMulReversedCode_mem_FP :
    machineRationalMatrixMulReversedCode ∈ FP := by
  simpa only [machineRationalMatrixMulReversedCode] using!
    machineCompose_mem_FP machineRationalMatrixMulFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalMatrixMulCode_mem_FP :
    machineRationalMatrixMulCode ∈ FP := by
  simpa only [machineRationalMatrixMulCode] using!
    machineCompose_mem_FP machineRationalMatrixMulReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact scan semantics -/

def rationalMatrixMulRowsPrefix {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) : List (List ℚ) :=
  ((List.finRange d).take k).map
    fun i ↦ List.ofFn fun j ↦ rationalMatrixMul A B i j

def machineRationalMatrixMulSemanticState {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) : List Bool :=
  let word := rationalMatrixMulCanonicalWord A B
  machineRationalTransposeMulVectorPack
    (binaryListCode finUnaryCode ((List.finRange d).drop k))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixMulRowsPrefix A B k).reverse)
    word (machineRationalMatrixMulInputBound word)

theorem machineRationalMatrixMulInit_semantics {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    machineRationalMatrixMulInit (rationalMatrixMulCanonicalWord A B) =
      machineRationalMatrixMulSemanticState A B 0 := by
  simp [machineRationalMatrixMulInit,
    machineRationalMatrixMulSemanticState,
    machineRationalMatrixMulIndices,
    machineRationalMatrixMulDimensionUnary,
    rationalMatrixMulCanonicalWord, machineUnaryRangeCode_encode,
    finRangeUnaryCode, rationalMatrixMulRowsPrefix, binaryListCode]

theorem rationalMatrixMulRowsPrefix_succ {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) (hk : k < d) :
    rationalMatrixMulRowsPrefix A B (k + 1) =
      rationalMatrixMulRowsPrefix A B k ++
        [List.ofFn fun j ↦ rationalMatrixMul A B ⟨k, hk⟩ j] := by
  simp only [rationalMatrixMulRowsPrefix, List.map_take]
  have hkm : k < (List.finRange d).length := by simpa
  simpa [List.getElem_finRange] using!
    congrArg (List.map fun i ↦
      List.ofFn fun j ↦ rationalMatrixMul A B i j)
      (List.take_concat_get hkm).symm

theorem machineRationalMatrixMulStep_semantics {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) (k : ℕ) (hk : k < d) :
    machineRationalMatrixMulStep
        (machineRationalMatrixMulSemanticState A B k) =
      machineRationalMatrixMulSemanticState A B (k + 1) := by
  let word := rationalMatrixMulCanonicalWord A B
  let i : Fin d := ⟨k, hk⟩
  have hdrop :
      (List.finRange d).drop k =
        i :: (List.finRange d).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.finRange d).length by simpa) using 1
    simp [i, List.getElem_finRange]
  have hprefix := rationalMatrixMulRowsPrefix_succ A B k hk
  have hreverse :
      (rationalMatrixMulRowsPrefix A B (k + 1)).reverse =
        (List.ofFn fun j ↦ rationalMatrixMul A B i j) ::
          (rationalMatrixMulRowsPrefix A B k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [i]
  have hcand :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixMulRowsPrefix A B (k + 1)).reverse).length ≤
        (machineRationalMatrixMulInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      (binaryListCode rationalEntryBinaryCode)
      (rationalMatrixRows (rationalMatrixMul A B)) (k + 1)
    have hprefixEq : rationalMatrixMulRowsPrefix A B (k + 1) =
        (rationalMatrixRows (rationalMatrixMul A B)).take (k + 1) := by
      apply List.ext_getElem
      · simp [rationalMatrixMulRowsPrefix, rationalMatrixRows]
      · intro r hrLeft hrRight
        simp [rationalMatrixMulRowsPrefix, rationalMatrixRows,
          List.getElem_finRange]
    rw [hprefixEq]
    exact hprefixBound.trans (rationalMatrixMul_code_length_le_bound A B)
  have hcandPair :
      (pair
        (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalMatrixMul A B i j))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixMulRowsPrefix A B k).reverse)).length ≤
        (machineRationalMatrixMulInputBound word).length := by
    simpa only [hreverse, binaryListCode] using! hcand
  have hnonempty :
      binaryListCode finUnaryCode ((List.finRange d).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil finUnaryCode i
      ((List.finRange d).drop (k + 1))
  rw [machineRationalMatrixMulStep]
  simp only [machineRationalMatrixMulSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalMatrixMulAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalMatrixMulNextAccumulator,
    machineRationalMatrixMulCandidate,
    machineRationalMatrixMulCurrentRow,
    machineRationalTransposeMulVectorCurrentIndex]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineRationalMatrixMulRowCode
          (pair (finUnaryCode i) word))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixMulRowsPrefix A B k).reverse)).take
        (machineRationalMatrixMulInputBound word).length) _ _ = _
  rw [show finUnaryCode i = List.replicate i.1 true by rfl,
    machineRationalMatrixMulRowCode_encode]
  change machineRationalTransposeMulVectorPack _
      ((pair (binaryListCode rationalEntryBinaryCode
          (List.ofFn fun j ↦ rationalMatrixMul A B i j))
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixMulRowsPrefix A B k).reverse)).take
        (machineRationalMatrixMulInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineRationalMatrixMulIterate_semantics {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) : ∀ k ≤ d,
    (machineRationalMatrixMulStep)^[k]
      (machineRationalMatrixMulInit (rationalMatrixMulCanonicalWord A B)) =
      machineRationalMatrixMulSemanticState A B k := by
  intro k hk
  induction k with
  | zero => exact machineRationalMatrixMulInit_semantics A B
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalMatrixMulStep_semantics A B k (by omega)

theorem machineRationalMatrixMul_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalMatrixMulStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalMatrixMulStep]

theorem rationalMatrixMulRowsPrefix_all {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixMulRowsPrefix A B d =
      rationalMatrixRows (rationalMatrixMul A B) := by
  apply List.ext_getElem
  · simp [rationalMatrixMulRowsPrefix, rationalMatrixRows]
  · intro i hiLeft hiRight
    simp [rationalMatrixMulRowsPrefix, rationalMatrixRows,
      List.getElem_finRange]

theorem machineRationalMatrixMulReversedCode_encode {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    machineRationalMatrixMulReversedCode
        (rationalMatrixMulCanonicalWord A B) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows (rationalMatrixMul A B)).reverse := by
  let word := rationalMatrixMulCanonicalWord A B
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalMatrixMulCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! h
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineRationalMatrixMulReversedCode word = _
  rw [machineRationalMatrixMulReversedCode,
    machineRationalMatrixMulFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalMatrixMulIterate_semantics A B d le_rfl]
  simp only [machineRationalMatrixMulSemanticState]
  rw [show binaryListCode finUnaryCode ((List.finRange d).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineRationalMatrixMul_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [rationalMatrixMulRowsPrefix_all]

@[simp] theorem machineRationalMatrixMulCode_encode {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℚ) :
    machineRationalMatrixMulCode (rationalMatrixMulCanonicalWord A B) =
      rationalSquareMatrixRowsCode (rationalMatrixMul A B) := by
  rw [machineRationalMatrixMulCode,
    machineRationalMatrixMulReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
