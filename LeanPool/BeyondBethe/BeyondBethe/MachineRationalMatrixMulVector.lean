/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalNormalizedDirection
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalTransposeMulVector

/-!
# Polynomial-time rational matrix--vector multiplication

The center update requires `E.basis * v`, whereas the pulled-back cut uses
`E.basisᵀ * a`.  This module begins with the row-coordinate primitive.  Its
input is a unary row index followed by the nested row code and the rational
vector code; it extracts that row and invokes the already verified exact dot
product machine.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- The rational matrix-vector product computed as row dot products. -/
def rationalMatrixMulVector {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ ∑ j, A i j * v j

/-- Input: `pair rowUnary (pair nestedMatrixRowsCode rationalVectorCode)`. -/
def machineRationalMatrixMulVectorEntryCode
    (word : List Bool) : List Bool :=
  let row := machinePairFirst word
  let payload := machinePairSecond word
  let matrixRows := machinePairFirst payload
  let vector := machinePairSecond payload
  let rowCode := machineListIndex (pair row matrixRows)
  machineRationalVectorDotEntryCode (pair rowCode vector)

theorem machineRationalMatrixMulVectorEntryCode_mem_FP :
    machineRationalMatrixMulVectorEntryCode ∈ FP := by
  have hrow := machinePairFirst_mem_FP
  have hpayload := machinePairSecond_mem_FP
  have hmatrix := machineCompose_mem_FP hpayload machinePairFirst_mem_FP
  have hvector := machineCompose_mem_FP hpayload machinePairSecond_mem_FP
  have hrowInput := machinePair_mem_FP hrow hmatrix
  have hrowCode := machineCompose_mem_FP hrowInput machineListIndex_mem_FP
  have hdotInput := machinePair_mem_FP hrowCode hvector
  simpa only [machineRationalMatrixMulVectorEntryCode] using!
    machineCompose_mem_FP hdotInput
      machineRationalVectorDotEntryCode_mem_FP

@[simp] theorem machineRationalMatrixMulVectorEntryCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) (i : Fin d) :
    machineRationalMatrixMulVectorEntryCode
        (pair (List.replicate i.1 true)
          (pair (rationalSquareMatrixRowsCode A)
            (rationalFiniteVectorCode v))) =
      rationalEntryBinaryCode (rationalMatrixMulVector A v i) := by
  rw [machineRationalMatrixMulVectorEntryCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    rationalSquareMatrixRowsCode]
  rw [machineListIndex_binaryListCode]
  · simp only [rationalMatrixRows, List.getElem_ofFn,
      rationalFiniteVectorCode]
    change machineRationalVectorDotEntryCode
        (pair
          (rationalFiniteVectorCode (fun j : Fin d ↦ A i j))
          (rationalFiniteVectorCode v)) = _
    rw [machineRationalVectorDotEntryCode_encode]
    rfl
  · simp [rationalMatrixRows]

/-! ## The full vector -/

/-- Computes one matrix-vector product coordinate as a raw-rational dot product. -/
def rawRationalMatrixCoordinate {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (i : Fin d) : RawRat :=
  rawRatListDot RawRat.zero (List.ofFn fun j ↦ A i j) (List.ofFn v)

theorem rawRationalMatrixCoordinate_value {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (i : Fin d) :
    (rawRationalMatrixCoordinate A v i).value =
      rationalMatrixMulVector A v i := by
  exact rawRatListDot_ofFn_value (fun j ↦ A i j) v

/-- Encodes a unary dimension, square matrix rows, and rational vector for multiplication. -/
def rationalMatrixMulVectorCanonicalWord {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair (rationalSquareMatrixRowsCode A)
      (rationalFiniteVectorCode v))

theorem rawRationalMatrixCoordinate_width_le_word {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (i : Fin d) :
    rawRatWidth (rawRationalMatrixCoordinate A v i) ≤
      (rationalMatrixMulVectorCanonicalWord A v).length := by
  let row := List.ofFn fun j : Fin d ↦ A i j
  let vector := List.ofFn v
  have hwidth := rawRatWidth_listDot_le RawRat.zero row vector
  simp only [rawRatWidth_zero] at hwidth
  have hcost := rawRatListDotCost_le_codeLength row vector
  have hrow :
      (binaryListCode rationalEntryBinaryCode row).length ≤
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A)).length := by
    have helem := binaryListCode_element_length_le
      (binaryListCode rationalEntryBinaryCode)
      (show row ∈ rationalMatrixRows A by
        simp [rationalMatrixRows, row])
    simpa only [rationalMatrixRows, List.getElem_ofFn, row] using! helem
  have hcombined :
      1 + (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A)).length +
        (binaryListCode rationalEntryBinaryCode vector).length ≤
          (rationalMatrixMulVectorCanonicalWord A v).length := by
    simp only [rationalMatrixMulVectorCanonicalWord,
      rationalSquareMatrixRowsCode, rationalFiniteVectorCode,
      vector, pair_length, List.length_replicate]
    omega
  change rawRatWidth (rawRatListDot RawRat.zero row vector) ≤ _
  omega

theorem rationalMatrixMulVector_entry_code_length_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (i : Fin d) :
    (rationalEntryBinaryCode
      (rationalMatrixMulVector A v i)).length ≤
      64 + 36 * (rationalMatrixMulVectorCanonicalWord A v).length := by
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (rawRationalMatrixCoordinate A v i)
  rw [binaryNormalizeRawRat_eq_value,
    rawRationalMatrixCoordinate_value] at hcanonical
  exact hcanonical.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 36
      (rawRationalMatrixCoordinate_width_le_word A v i)) 64)

/-- Reuses the transpose-vector input bound for matrix-vector multiplication. -/
def machineRationalMatrixMulVectorInputBound
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineRationalMatrixMulVectorInputBound_mem_FP :
    machineRationalMatrixMulVectorInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem rationalMatrixMulVector_code_length_le_bound {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    (rationalFiniteVectorCode (rationalMatrixMulVector A v)).length ≤
      (machineRationalMatrixMulVectorInputBound
        (rationalMatrixMulVectorCanonicalWord A v)).length := by
  let word := rationalMatrixMulVectorCanonicalWord A v
  let B := 64 + 36 * word.length
  have hdim : d ≤ word.length := by
    have hfirst := machinePairFirst_length_le word
    simpa only [word, rationalMatrixMulVectorCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! hfirst
  have heach : ∀ q ∈ List.ofFn (rationalMatrixMulVector A v),
      (rationalEntryBinaryCode q).length ≤ B := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact rationalMatrixMulVector_entry_code_length_le A v i
  have hsum := List.sum_le_card_nsmul
    ((List.ofFn (rationalMatrixMulVector A v)).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    (2 * B + 2) (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum]
  simp only [machineRationalMatrixMulVectorInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, List.length_map, List.length_ofFn,
    Nat.nsmul_eq_mul] at hsum ⊢
  dsimp only [B, word] at hsum ⊢
  nlinarith [sq_nonneg
    (rationalMatrixMulVectorCanonicalWord A v).length]

/-! The state layout and the degree-eight envelope are shared with the
transpose--vector machine; only the one-coordinate routine changes. -/

/-- Computes the matrix-vector product entry at the current scan index. -/
def machineRationalMatrixMulVectorCurrentEntry
    (state : List Bool) : List Bool :=
  machineRationalMatrixMulVectorEntryCode
    (pair (machineRationalTransposeMulVectorCurrentIndex state)
      (machineRationalTransposeMulVectorStatePayload state))

/-- Prepends the current product entry to the reversed vector accumulator. -/
def machineRationalMatrixMulVectorCandidate
    (state : List Bool) : List Bool :=
  pair (machineRationalMatrixMulVectorCurrentEntry state)
    (machineRationalTransposeMulVectorAccumulator state)

/-- Truncates the candidate product-vector accumulator to the stored width bound. -/
def machineRationalMatrixMulVectorNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalMatrixMulVectorCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

/-- Consumes one coordinate index and updates the bounded product vector, retaining payload and
bound. -/
def machineRationalMatrixMulVectorAdvance
    (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineRationalMatrixMulVectorNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

/-- Generates the next product coordinate, leaving exhausted scans fixed. -/
def machineRationalMatrixMulVectorStep
    (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineRationalMatrixMulVectorAdvance state)

/-- Reuses the transpose-vector state layout to initialize matrix-vector multiplication. -/
def machineRationalMatrixMulVectorInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInit word

/-- Reuses the transpose-vector width envelope for matrix-vector multiplication. -/
def machineRationalMatrixMulVectorWidth (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorWidth word

/-- Runs matrix-vector coordinate generation for one step per input bit. -/
def machineRationalMatrixMulVectorFinalState
    (word : List Bool) : List Bool :=
  (machineRationalMatrixMulVectorStep)^[word.length]
    (machineRationalMatrixMulVectorInit word)

/-- Extracts the generated matrix-vector product coordinates in reverse order. -/
def machineRationalMatrixMulVectorReversedCode
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineRationalMatrixMulVectorFinalState word)

/-- Reverses the accumulated matrix-vector product entries to restore row order. -/
def machineRationalMatrixMulVectorCode
    (word : List Bool) : List Bool :=
  machineListReverse (machineRationalMatrixMulVectorReversedCode word)

theorem machineRationalMatrixMulVectorCurrentEntry_mem_FP :
    machineRationalMatrixMulVectorCurrentEntry ∈ FP := by
  have hp := machinePair_mem_FP
    machineRationalTransposeMulVectorCurrentIndex_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP
  simpa only [machineRationalMatrixMulVectorCurrentEntry] using!
    machineCompose_mem_FP hp
      machineRationalMatrixMulVectorEntryCode_mem_FP

theorem machineRationalMatrixMulVectorCandidate_mem_FP :
    machineRationalMatrixMulVectorCandidate ∈ FP :=
  machinePair_mem_FP machineRationalMatrixMulVectorCurrentEntry_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalMatrixMulVectorNextAccumulator_mem_FP :
    machineRationalMatrixMulVectorNextAccumulator ∈ FP := by
  simpa only [machineRationalMatrixMulVectorNextAccumulator] using!
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineRationalMatrixMulVectorCandidate_mem_FP

theorem machineRationalMatrixMulVectorAdvance_mem_FP :
    machineRationalMatrixMulVectorAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalMatrixMulVectorNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineRationalMatrixMulVectorStep_mem_FP :
    machineRationalMatrixMulVectorStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineRationalMatrixMulVectorAdvance_mem_FP

theorem machineRationalMatrixMulVectorInit_mem_FP :
    machineRationalMatrixMulVectorInit ∈ FP :=
  machineRationalTransposeMulVectorInit_mem_FP

theorem machineRationalMatrixMulVectorWidth_mem_FP :
    machineRationalMatrixMulVectorWidth ∈ FP :=
  machineRationalTransposeMulVectorWidth_mem_FP

theorem machineRationalMatrixMulVectorStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalMatrixMulVectorStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineRationalMatrixMulVectorStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineRationalMatrixMulVectorStep, hcode,
          machineIfEmpty_cons, machineRationalMatrixMulVectorAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineRationalMatrixMulVectorNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalMatrixMulVectorIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineRationalMatrixMulVectorStep)^[k]
        (machineRationalMatrixMulVectorInit word)) := by
  intro k
  induction k with
  | zero =>
      simpa only [machineRationalMatrixMulVectorInit] using!
        machineRationalTransposeMulVectorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalMatrixMulVectorStep_bound ih

theorem machineRationalMatrixMulVectorIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalMatrixMulVectorStep)^[iterations]
      (machineRationalMatrixMulVectorInit word)).length ≤
        (machineRationalMatrixMulVectorWidth word).length := by
  rcases machineRationalMatrixMulVectorIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineRationalMatrixMulVectorWidth,
    machineRationalTransposeMulVectorWidth, pair_length]
  omega

theorem machineRationalMatrixMulVectorFinalState_mem_FP :
    machineRationalMatrixMulVectorFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalMatrixMulVectorStep_mem_FP
    machineRationalMatrixMulVectorInit_mem_FP id_mem_FP
    machineRationalMatrixMulVectorWidth_mem_FP
    machineRationalMatrixMulVectorIterate_length_le_width

theorem machineRationalMatrixMulVectorReversedCode_mem_FP :
    machineRationalMatrixMulVectorReversedCode ∈ FP := by
  simpa only [machineRationalMatrixMulVectorReversedCode] using!
    machineCompose_mem_FP machineRationalMatrixMulVectorFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalMatrixMulVectorCode_mem_FP :
    machineRationalMatrixMulVectorCode ∈ FP := by
  simpa only [machineRationalMatrixMulVectorCode] using!
    machineCompose_mem_FP
      machineRationalMatrixMulVectorReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact iteration semantics -/

/-- Lists the first `k` coordinates of the rational matrix-vector product in row order. -/
def rationalMatrixMulVectorPrefix {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) : List ℚ :=
  ((List.finRange d).take k).map
    fun i ↦ rationalMatrixMulVector A v i

/-- Encodes the remaining row indices and reversed product prefix after `k` rows, retaining the
matrix-vector payload and input bound. -/
def machineRationalMatrixMulVectorSemanticState {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) : List Bool :=
  let word := rationalMatrixMulVectorCanonicalWord A v
  machineRationalTransposeMulVectorPack
    (binaryListCode finUnaryCode ((List.finRange d).drop k))
    (binaryListCode rationalEntryBinaryCode
      (rationalMatrixMulVectorPrefix A v k).reverse)
    (pair (rationalSquareMatrixRowsCode A)
      (rationalFiniteVectorCode v))
    (machineRationalMatrixMulVectorInputBound word)

theorem machineRationalMatrixMulVectorInit_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalMatrixMulVectorInit
        (rationalMatrixMulVectorCanonicalWord A v) =
      machineRationalMatrixMulVectorSemanticState A v 0 := by
  simp [machineRationalMatrixMulVectorInit,
    machineRationalTransposeMulVectorInit,
    machineRationalMatrixMulVectorSemanticState,
    machineRationalTransposeMulVectorIndices,
    machineRationalTransposeMulVectorDimension,
    machineRationalTransposeMulVectorPayload,
    rationalMatrixMulVectorCanonicalWord,
    machineUnaryRangeCode_encode, finRangeUnaryCode,
    rationalMatrixMulVectorPrefix, binaryListCode,
    machineRationalMatrixMulVectorInputBound]

theorem rationalMatrixMulVectorPrefix_succ {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) (hk : k < d) :
    rationalMatrixMulVectorPrefix A v (k + 1) =
      rationalMatrixMulVectorPrefix A v k ++
        [rationalMatrixMulVector A v ⟨k, hk⟩] := by
  simp only [rationalMatrixMulVectorPrefix, List.map_take]
  have hkm : k < (List.finRange d).length := by simpa
  simpa [List.getElem_finRange] using!
    congrArg (List.map fun i ↦ rationalMatrixMulVector A v i)
      (List.take_concat_get hkm).symm

theorem machineRationalMatrixMulVectorStep_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) (hk : k < d) :
    machineRationalMatrixMulVectorStep
        (machineRationalMatrixMulVectorSemanticState A v k) =
      machineRationalMatrixMulVectorSemanticState A v (k + 1) := by
  let word := rationalMatrixMulVectorCanonicalWord A v
  let i : Fin d := ⟨k, hk⟩
  have hdrop :
      (List.finRange d).drop k =
        i :: (List.finRange d).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.finRange d).length by simpa) using 1
    simp [i, List.getElem_finRange]
  have hprefix := rationalMatrixMulVectorPrefix_succ A v k hk
  have hreverse :
      (rationalMatrixMulVectorPrefix A v (k + 1)).reverse =
        rationalMatrixMulVector A v i ::
          (rationalMatrixMulVectorPrefix A v k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [i]
  have hcand :
      (binaryListCode rationalEntryBinaryCode
        (rationalMatrixMulVectorPrefix A v (k + 1)).reverse).length ≤
        (machineRationalMatrixMulVectorInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      rationalEntryBinaryCode
      (List.ofFn (rationalMatrixMulVector A v)) (k + 1)
    have hprefixEq : rationalMatrixMulVectorPrefix A v (k + 1) =
        (List.ofFn (rationalMatrixMulVector A v)).take (k + 1) := by
      apply List.ext_getElem
      · simp [rationalMatrixMulVectorPrefix]
      · intro r hrLeft hrRight
        simp [rationalMatrixMulVectorPrefix, List.getElem_finRange]
    rw [hprefixEq]
    exact hprefixBound.trans
      (rationalMatrixMulVector_code_length_le_bound A v)
  have hcandPair :
      (pair (rationalEntryBinaryCode
          (rationalMatrixMulVector A v i))
        (binaryListCode rationalEntryBinaryCode
          (rationalMatrixMulVectorPrefix A v k).reverse)).length ≤
        (machineRationalMatrixMulVectorInputBound word).length := by
    simpa only [hreverse, binaryListCode] using! hcand
  have hnonempty :
      binaryListCode finUnaryCode ((List.finRange d).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil finUnaryCode i
      ((List.finRange d).drop (k + 1))
  rw [machineRationalMatrixMulVectorStep]
  simp only [machineRationalMatrixMulVectorSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalMatrixMulVectorAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalMatrixMulVectorNextAccumulator,
    machineRationalMatrixMulVectorCandidate,
    machineRationalMatrixMulVectorCurrentEntry,
    machineRationalTransposeMulVectorCurrentIndex]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineRationalMatrixMulVectorEntryCode
        (pair (finUnaryCode i)
          (pair (rationalSquareMatrixRowsCode A)
            (rationalFiniteVectorCode v))))
          (binaryListCode rationalEntryBinaryCode
            (rationalMatrixMulVectorPrefix A v k).reverse)).take
        (machineRationalMatrixMulVectorInputBound word).length) _ _ = _
  rw [show finUnaryCode i = List.replicate i.1 true by rfl,
    machineRationalMatrixMulVectorEntryCode_encode]
  change machineRationalTransposeMulVectorPack _
      ((pair (rationalEntryBinaryCode
        (rationalMatrixMulVector A v i))
        (binaryListCode rationalEntryBinaryCode
          (rationalMatrixMulVectorPrefix A v k).reverse)).take
        (machineRationalMatrixMulVectorInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineRationalMatrixMulVectorIterate_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : ∀ k ≤ d,
    (machineRationalMatrixMulVectorStep)^[k]
      (machineRationalMatrixMulVectorInit
        (rationalMatrixMulVectorCanonicalWord A v)) =
      machineRationalMatrixMulVectorSemanticState A v k := by
  intro k hk
  induction k with
  | zero => exact machineRationalMatrixMulVectorInit_semantics A v
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalMatrixMulVectorStep_semantics A v k (by omega)

theorem machineRationalMatrixMulVector_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalMatrixMulVectorStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalMatrixMulVectorStep]

theorem rationalMatrixMulVectorPrefix_all {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    rationalMatrixMulVectorPrefix A v d =
      List.ofFn (rationalMatrixMulVector A v) := by
  apply List.ext_getElem
  · simp [rationalMatrixMulVectorPrefix]
  · intro i hiLeft hiRight
    simp [rationalMatrixMulVectorPrefix, List.getElem_finRange]

theorem machineRationalMatrixMulVectorReversedCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalMatrixMulVectorReversedCode
        (rationalMatrixMulVectorCanonicalWord A v) =
      binaryListCode rationalEntryBinaryCode
        (List.ofFn (rationalMatrixMulVector A v)).reverse := by
  let word := rationalMatrixMulVectorCanonicalWord A v
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalMatrixMulVectorCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! h
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineRationalMatrixMulVectorReversedCode word = _
  rw [machineRationalMatrixMulVectorReversedCode,
    machineRationalMatrixMulVectorFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalMatrixMulVectorIterate_semantics A v d le_rfl]
  simp only [machineRationalMatrixMulVectorSemanticState]
  rw [show binaryListCode finUnaryCode ((List.finRange d).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineRationalMatrixMulVector_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [rationalMatrixMulVectorPrefix_all]

@[simp] theorem machineRationalMatrixMulVectorCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalMatrixMulVectorCode
        (rationalMatrixMulVectorCanonicalWord A v) =
      rationalFiniteVectorCode (rationalMatrixMulVector A v) := by
  rw [machineRationalMatrixMulVectorCode,
    machineRationalMatrixMulVectorReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
