/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMatrixColumn
import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryRange

/-!
# Polynomial-time rational transpose--vector multiplication

This module maps the verified one-coordinate routine over all unary column
indices.  The output is the canonical vector word for `Aᵀ v`.  A concrete
degree-eight word bounds every intermediate accumulator even on malformed
inputs; on canonical inputs a separate encoding estimate proves that the
clamp never truncates.
-/

namespace BeyondBethe

open Complexity

/-- The semantic transpose--vector product used by the exactness theorem. -/
def rationalTransposeMulVector {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : Fin d → ℚ :=
  fun j ↦ ∑ i, A i j * v i

def rawRationalTransposeCoordinate {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (j : Fin d) : RawRat :=
  rawRatListDot RawRat.zero
    (rationalColumnOfRows (rationalMatrixRows A) j.1)
    (List.ofFn v)

theorem rawRationalTransposeCoordinate_value {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (j : Fin d) :
    (rawRationalTransposeCoordinate A v j).value =
      rationalTransposeMulVector A v j := by
  rw [rawRationalTransposeCoordinate,
    rationalColumnOfRows_matrix]
  exact rawRatListDot_ofFn_value (fun i => A i j) v

def rationalTransposeMulVectorCanonicalWord {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair (rationalSquareMatrixRowsCode A)
      (rationalFiniteVectorCode v))

theorem rawRationalTransposeCoordinate_width_le_word {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (j : Fin d) :
    rawRatWidth (rawRationalTransposeCoordinate A v j) ≤
      (rationalTransposeMulVectorCanonicalWord A v).length := by
  let column := rationalColumnOfRows (rationalMatrixRows A) j.1
  let vector := List.ofFn v
  have hwidth := rawRatWidth_listDot_le RawRat.zero column vector
  simp only [rawRatWidth_zero] at hwidth
  have hcost := rawRatListDotCost_le_codeLength column vector
  have hcolumn := rationalColumnOfRows_code_length_le j.1
    (rationalMatrixRows A) (rationalMatrixRows_haveColumn A j)
  have hcolumn' :
      (binaryListCode rationalEntryBinaryCode column).length ≤
        (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A)).length := by
    simpa only [column] using hcolumn
  have hcombined :
      1 + (binaryListCode (binaryListCode rationalEntryBinaryCode)
          (rationalMatrixRows A)).length +
        (binaryListCode rationalEntryBinaryCode vector).length ≤
          (rationalTransposeMulVectorCanonicalWord A v).length := by
    simp only [rationalTransposeMulVectorCanonicalWord,
      rationalSquareMatrixRowsCode, rationalFiniteVectorCode,
      vector, pair_length, List.length_replicate]
    omega
  change rawRatWidth
      (rawRatListDot RawRat.zero column vector) ≤ _
  omega

theorem rationalTransposeMulVector_entry_code_length_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (j : Fin d) :
    (rationalEntryBinaryCode
      (rationalTransposeMulVector A v j)).length ≤
      64 + 36 * (rationalTransposeMulVectorCanonicalWord A v).length := by
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (rawRationalTransposeCoordinate A v j)
  rw [binaryNormalizeRawRat_eq_value,
    rawRationalTransposeCoordinate_value] at hcanonical
  exact hcanonical.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 36
      (rawRationalTransposeCoordinate_width_le_word A v j)) 64)

def machineRationalTransposeMulVectorInputBound
    (word : List Bool) : List Bool :=
  machineBinaryMulWidth
    (machineBinaryMulWidth (machineBinaryMulWidth word))

theorem machineRationalTransposeMulVectorInputBound_mem_FP :
    machineRationalTransposeMulVectorInputBound ∈ FP := by
  have h1 := machineBinaryMulWidth_mem_FP
  have h2 := machineCompose_mem_FP h1 machineBinaryMulWidth_mem_FP
  have h3 := machineCompose_mem_FP h2 machineBinaryMulWidth_mem_FP
  simpa only [machineRationalTransposeMulVectorInputBound] using h3

theorem rationalTransposeMulVector_code_length_le_bound {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    (rationalFiniteVectorCode
      (rationalTransposeMulVector A v)).length ≤
      (machineRationalTransposeMulVectorInputBound
        (rationalTransposeMulVectorCanonicalWord A v)).length := by
  let word := rationalTransposeMulVectorCanonicalWord A v
  let B := 64 + 36 * word.length
  have hdim : d ≤ word.length := by
    have hfirst := machinePairFirst_length_le word
    simpa only [word, rationalTransposeMulVectorCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using hfirst
  have heach : ∀ q ∈ List.ofFn (rationalTransposeMulVector A v),
      (rationalEntryBinaryCode q).length ≤ B := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact rationalTransposeMulVector_entry_code_length_le A v j
  have hsum := List.sum_le_card_nsmul
    ((List.ofFn (rationalTransposeMulVector A v)).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    (2 * B + 2) (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum]
  simp only [machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, List.length_map, List.length_ofFn,
    Nat.nsmul_eq_mul] at hsum ⊢
  dsimp only [B, word] at hsum ⊢
  nlinarith [sq_nonneg
    (rationalTransposeMulVectorCanonicalWord A v).length]

/-! ## Finite-word transducer -/

def machineRationalTransposeMulVectorDimension
    (word : List Bool) : List Bool := machinePairFirst word

def machineRationalTransposeMulVectorPayload
    (word : List Bool) : List Bool := machinePairSecond word

def machineRationalTransposeMulVectorIndices
    (word : List Bool) : List Bool :=
  machineUnaryRangeCode
    (machineRationalTransposeMulVectorDimension word)

def machineRationalTransposeMulVectorPack
    (remaining accumulator payload bound : List Bool) : List Bool :=
  pair remaining (pair accumulator (pair payload bound))

def machineRationalTransposeMulVectorRemaining
    (state : List Bool) : List Bool := machinePairFirst state

def machineRationalTransposeMulVectorAccumulator
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineRationalTransposeMulVectorStatePayload
    (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineRationalTransposeMulVectorBound
    (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond state))

def machineRationalTransposeMulVectorCurrentIndex
    (state : List Bool) : List Bool :=
  machineListHead (machineRationalTransposeMulVectorRemaining state)

def machineRationalTransposeMulVectorCurrentEntry
    (state : List Bool) : List Bool :=
  machineRationalMatrixTransposeMulVectorEntryCode
    (pair (machineRationalTransposeMulVectorCurrentIndex state)
      (machineRationalTransposeMulVectorStatePayload state))

def machineRationalTransposeMulVectorCandidate
    (state : List Bool) : List Bool :=
  pair (machineRationalTransposeMulVectorCurrentEntry state)
    (machineRationalTransposeMulVectorAccumulator state)

def machineRationalTransposeMulVectorNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalTransposeMulVectorCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

def machineRationalTransposeMulVectorAdvance
    (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineRationalTransposeMulVectorNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

def machineRationalTransposeMulVectorStep
    (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineRationalTransposeMulVectorAdvance state)

def machineRationalTransposeMulVectorInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineRationalTransposeMulVectorIndices word) []
    (machineRationalTransposeMulVectorPayload word)
    (machineRationalTransposeMulVectorInputBound word)

def machineRationalTransposeMulVectorWidth (word : List Bool) : List Bool :=
  let bound := machineRationalTransposeMulVectorInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

def machineRationalTransposeMulVectorFinalState
    (word : List Bool) : List Bool :=
  (machineRationalTransposeMulVectorStep)^[word.length]
    (machineRationalTransposeMulVectorInit word)

def machineRationalTransposeMulVectorReversedCode
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineRationalTransposeMulVectorFinalState word)

/-- Input: `pair dimensionUnary (pair nestedMatrixRowsCode vectorCode)`. -/
def machineRationalTransposeMulVectorCode
    (word : List Bool) : List Bool :=
  machineListReverse
    (machineRationalTransposeMulVectorReversedCode word)

theorem machineRationalTransposeMulVectorDimension_mem_FP :
    machineRationalTransposeMulVectorDimension ∈ FP := machinePairFirst_mem_FP

theorem machineRationalTransposeMulVectorPayload_mem_FP :
    machineRationalTransposeMulVectorPayload ∈ FP := machinePairSecond_mem_FP

theorem machineRationalTransposeMulVectorIndices_mem_FP :
    machineRationalTransposeMulVectorIndices ∈ FP := by
  simpa only [machineRationalTransposeMulVectorIndices] using
    machineCompose_mem_FP machineRationalTransposeMulVectorDimension_mem_FP
      machineUnaryRangeCode_mem_FP

theorem machineRationalTransposeMulVectorRemaining_mem_FP :
    machineRationalTransposeMulVectorRemaining ∈ FP := machinePairFirst_mem_FP

theorem machineRationalTransposeMulVectorAccumulator_mem_FP :
    machineRationalTransposeMulVectorAccumulator ∈ FP := by
  simpa only [machineRationalTransposeMulVectorAccumulator] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineRationalTransposeMulVectorStatePayload_mem_FP :
    machineRationalTransposeMulVectorStatePayload ∈ FP := by
  simpa only [machineRationalTransposeMulVectorStatePayload] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP) machinePairFirst_mem_FP

theorem machineRationalTransposeMulVectorBound_mem_FP :
    machineRationalTransposeMulVectorBound ∈ FP := by
  simpa only [machineRationalTransposeMulVectorBound] using
    machineCompose_mem_FP
      (machineCompose_mem_FP machinePairSecond_mem_FP
        machinePairSecond_mem_FP) machinePairSecond_mem_FP

theorem machineRationalTransposeMulVectorCurrentIndex_mem_FP :
    machineRationalTransposeMulVectorCurrentIndex ∈ FP := by
  simpa only [machineRationalTransposeMulVectorCurrentIndex] using
    machineCompose_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
      machineListHead_mem_FP

theorem machineRationalTransposeMulVectorCurrentEntry_mem_FP :
    machineRationalTransposeMulVectorCurrentEntry ∈ FP := by
  have hp := machinePair_mem_FP
    machineRationalTransposeMulVectorCurrentIndex_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP
  simpa only [machineRationalTransposeMulVectorCurrentEntry] using
    machineCompose_mem_FP hp
      machineRationalMatrixTransposeMulVectorEntryCode_mem_FP

theorem machineRationalTransposeMulVectorCandidate_mem_FP :
    machineRationalTransposeMulVectorCandidate ∈ FP :=
  machinePair_mem_FP machineRationalTransposeMulVectorCurrentEntry_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalTransposeMulVectorNextAccumulator_mem_FP :
    machineRationalTransposeMulVectorNextAccumulator ∈ FP := by
  simpa only [machineRationalTransposeMulVectorNextAccumulator] using
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineRationalTransposeMulVectorCandidate_mem_FP

theorem machineRationalTransposeMulVectorAdvance_mem_FP :
    machineRationalTransposeMulVectorAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalTransposeMulVectorNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineRationalTransposeMulVectorStep_mem_FP :
    machineRationalTransposeMulVectorStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineRationalTransposeMulVectorAdvance_mem_FP

theorem machineRationalTransposeMulVectorInit_mem_FP :
    machineRationalTransposeMulVectorInit ∈ FP := by
  exact machinePair_mem_FP machineRationalTransposeMulVectorIndices_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineRationalTransposeMulVectorPayload_mem_FP
        machineRationalTransposeMulVectorInputBound_mem_FP))

theorem machineRationalTransposeMulVectorWidth_mem_FP :
    machineRationalTransposeMulVectorWidth ∈ FP := by
  exact machinePair_mem_FP machineRationalTransposeMulVectorInputBound_mem_FP
    (machinePair_mem_FP machineRationalTransposeMulVectorInputBound_mem_FP
      (machinePair_mem_FP machineRationalTransposeMulVectorInputBound_mem_FP
        machineRationalTransposeMulVectorInputBound_mem_FP))

@[simp] theorem machineRationalTransposeMulVectorRemaining_pack (a b c d) :
    machineRationalTransposeMulVectorRemaining
      (machineRationalTransposeMulVectorPack a b c d) = a := by
  simp [machineRationalTransposeMulVectorRemaining,
    machineRationalTransposeMulVectorPack]

@[simp] theorem machineRationalTransposeMulVectorAccumulator_pack (a b c d) :
    machineRationalTransposeMulVectorAccumulator
      (machineRationalTransposeMulVectorPack a b c d) = b := by
  simp [machineRationalTransposeMulVectorAccumulator,
    machineRationalTransposeMulVectorPack]

@[simp] theorem machineRationalTransposeMulVectorStatePayload_pack (a b c d) :
    machineRationalTransposeMulVectorStatePayload
      (machineRationalTransposeMulVectorPack a b c d) = c := by
  simp [machineRationalTransposeMulVectorStatePayload,
    machineRationalTransposeMulVectorPack]

@[simp] theorem machineRationalTransposeMulVectorBound_pack (a b c d) :
    machineRationalTransposeMulVectorBound
      (machineRationalTransposeMulVectorPack a b c d) = d := by
  simp [machineRationalTransposeMulVectorBound,
    machineRationalTransposeMulVectorPack]

def MachineRationalTransposeMulVectorStateBound
    (word state : List Bool) : Prop :=
  let bound := machineRationalTransposeMulVectorInputBound word
  state = machineRationalTransposeMulVectorPack
      (machineRationalTransposeMulVectorRemaining state)
      (machineRationalTransposeMulVectorAccumulator state)
      (machineRationalTransposeMulVectorStatePayload state)
      (machineRationalTransposeMulVectorBound state) ∧
    (machineRationalTransposeMulVectorRemaining state).length ≤ bound.length ∧
    (machineRationalTransposeMulVectorAccumulator state).length ≤ bound.length ∧
    (machineRationalTransposeMulVectorStatePayload state).length ≤ bound.length ∧
    machineRationalTransposeMulVectorBound state = bound

theorem machineRationalTransposeMulVector_word_le_bound (word : List Bool) :
    word.length ≤
      (machineRationalTransposeMulVectorInputBound word).length := by
  simp only [machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith [sq_nonneg word.length]

theorem machineRationalTransposeMulVector_indices_le_bound
    (word : List Bool) :
    (machineRationalTransposeMulVectorIndices word).length ≤
      (machineRationalTransposeMulVectorInputBound word).length := by
  have hrange := machineUnaryRangeCode_length_le_inputBound
    (machineRationalTransposeMulVectorDimension word)
  have hdimension := machinePairFirst_length_le word
  have hdimension' :
      (machineRationalTransposeMulVectorDimension word).length ≤
        word.length := by
    simpa only [machineRationalTransposeMulVectorDimension] using hdimension
  have hmono := machineListUpdateInputBound_length_mono hdimension'
  apply hrange.trans (hmono.trans ?_)
  simp only [machineListUpdateInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  nlinarith [sq_nonneg word.length]

theorem machineRationalTransposeMulVectorInit_bound (word : List Bool) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalTransposeMulVectorInit word) := by
  simp only [MachineRationalTransposeMulVectorStateBound,
    machineRationalTransposeMulVectorInit,
    machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack]
  refine ⟨trivial,
    machineRationalTransposeMulVector_indices_le_bound word,
    by simp, ?_, trivial⟩
  exact (machinePairSecond_length_le word).trans
    (machineRationalTransposeMulVector_word_le_bound word)

theorem machineRationalTransposeMulVectorStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalTransposeMulVectorStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineRationalTransposeMulVectorStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · rw [machineRationalTransposeMulVectorStep]
    cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineRationalTransposeMulVectorAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineRationalTransposeMulVectorNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalTransposeMulVectorIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineRationalTransposeMulVectorStep)^[k]
        (machineRationalTransposeMulVectorInit word)) := by
  intro k
  induction k with
  | zero => exact machineRationalTransposeMulVectorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalTransposeMulVectorStep_bound ih

theorem machineRationalTransposeMulVectorIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalTransposeMulVectorStep)^[iterations]
      (machineRationalTransposeMulVectorInit word)).length ≤
        (machineRationalTransposeMulVectorWidth word).length := by
  rcases machineRationalTransposeMulVectorIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineRationalTransposeMulVectorWidth, pair_length]
  omega

theorem machineRationalTransposeMulVectorFinalState_mem_FP :
    machineRationalTransposeMulVectorFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalTransposeMulVectorStep_mem_FP
    machineRationalTransposeMulVectorInit_mem_FP id_mem_FP
    machineRationalTransposeMulVectorWidth_mem_FP
    machineRationalTransposeMulVectorIterate_length_le_width

theorem machineRationalTransposeMulVectorReversedCode_mem_FP :
    machineRationalTransposeMulVectorReversedCode ∈ FP := by
  simpa only [machineRationalTransposeMulVectorReversedCode] using
    machineCompose_mem_FP machineRationalTransposeMulVectorFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalTransposeMulVectorCode_mem_FP :
    machineRationalTransposeMulVectorCode ∈ FP := by
  simpa only [machineRationalTransposeMulVectorCode] using
    machineCompose_mem_FP
      machineRationalTransposeMulVectorReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact iteration semantics -/

def rationalTransposePrefix {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) : List ℚ :=
  ((List.finRange d).take k).map
    fun j ↦ rationalTransposeMulVector A v j

def machineRationalTransposeMulVectorSemanticState {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) : List Bool :=
  let word := rationalTransposeMulVectorCanonicalWord A v
  machineRationalTransposeMulVectorPack
    (binaryListCode finUnaryCode ((List.finRange d).drop k))
    (binaryListCode rationalEntryBinaryCode
      (rationalTransposePrefix A v k).reverse)
    (pair (rationalSquareMatrixRowsCode A)
      (rationalFiniteVectorCode v))
    (machineRationalTransposeMulVectorInputBound word)

theorem machineRationalTransposeMulVectorInit_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalTransposeMulVectorInit
        (rationalTransposeMulVectorCanonicalWord A v) =
      machineRationalTransposeMulVectorSemanticState A v 0 := by
  simp [machineRationalTransposeMulVectorInit,
    machineRationalTransposeMulVectorSemanticState,
    machineRationalTransposeMulVectorIndices,
    machineRationalTransposeMulVectorDimension,
    machineRationalTransposeMulVectorPayload,
    rationalTransposeMulVectorCanonicalWord,
    machineUnaryRangeCode_encode, finRangeUnaryCode,
    rationalTransposePrefix, binaryListCode]

theorem rationalTransposePrefix_succ {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) (hk : k < d) :
    rationalTransposePrefix A v (k + 1) =
      rationalTransposePrefix A v k ++
        [rationalTransposeMulVector A v ⟨k, hk⟩] := by
  simp only [rationalTransposePrefix, List.map_take]
  have hkm : k < (List.finRange d).length := by simpa
  simpa [List.getElem_finRange] using
    congrArg (List.map fun j ↦ rationalTransposeMulVector A v j)
      (List.take_concat_get hkm).symm

theorem machineRationalTransposeMulVectorStep_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ)
    (k : ℕ) (hk : k < d) :
    machineRationalTransposeMulVectorStep
        (machineRationalTransposeMulVectorSemanticState A v k) =
      machineRationalTransposeMulVectorSemanticState A v (k + 1) := by
  let word := rationalTransposeMulVectorCanonicalWord A v
  let j : Fin d := ⟨k, hk⟩
  have hdrop :
      (List.finRange d).drop k =
        j :: (List.finRange d).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.finRange d).length by simpa) using 1
    simp [j, List.getElem_finRange]
  have hprefix := rationalTransposePrefix_succ A v k hk
  have hreverse :
      (rationalTransposePrefix A v (k + 1)).reverse =
        rationalTransposeMulVector A v j ::
          (rationalTransposePrefix A v k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [j]
  have hcand :
      (binaryListCode rationalEntryBinaryCode
        (rationalTransposePrefix A v (k + 1)).reverse).length ≤
        (machineRationalTransposeMulVectorInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      rationalEntryBinaryCode
      (List.ofFn (rationalTransposeMulVector A v)) (k + 1)
    have hprefixEq : rationalTransposePrefix A v (k + 1) =
        (List.ofFn (rationalTransposeMulVector A v)).take (k + 1) := by
      apply List.ext_getElem
      · simp [rationalTransposePrefix]
      · intro i hiLeft hiRight
        simp [rationalTransposePrefix, List.getElem_finRange]
    rw [hprefixEq]
    exact hprefixBound.trans
      (rationalTransposeMulVector_code_length_le_bound A v)
  have hcandPair :
      (pair (rationalEntryBinaryCode
          (rationalTransposeMulVector A v j))
        (binaryListCode rationalEntryBinaryCode
          (rationalTransposePrefix A v k).reverse)).length ≤
        (machineRationalTransposeMulVectorInputBound word).length := by
    simpa only [hreverse, binaryListCode] using hcand
  have hnonempty :
      binaryListCode finUnaryCode ((List.finRange d).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil finUnaryCode j
      ((List.finRange d).drop (k + 1))
  rw [machineRationalTransposeMulVectorStep]
  simp only [machineRationalTransposeMulVectorSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalTransposeMulVectorAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalTransposeMulVectorNextAccumulator,
    machineRationalTransposeMulVectorCandidate,
    machineRationalTransposeMulVectorCurrentEntry,
    machineRationalTransposeMulVectorCurrentIndex]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineRationalMatrixTransposeMulVectorEntryCode
        (pair (finUnaryCode j)
          (pair (rationalSquareMatrixRowsCode A)
            (rationalFiniteVectorCode v))))
          (binaryListCode rationalEntryBinaryCode
            (rationalTransposePrefix A v k).reverse)).take
        (machineRationalTransposeMulVectorInputBound word).length) _ _ = _
  rw [show finUnaryCode j = List.replicate j.1 true by rfl,
    machineRationalMatrixTransposeMulVectorEntryCode_encode]
  change machineRationalTransposeMulVectorPack _
      ((pair (rationalEntryBinaryCode
        (rationalTransposeMulVector A v j))
        (binaryListCode rationalEntryBinaryCode
          (rationalTransposePrefix A v k).reverse)).take
        (machineRationalTransposeMulVectorInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineRationalTransposeMulVectorIterate_semantics {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : ∀ k ≤ d,
    (machineRationalTransposeMulVectorStep)^[k]
      (machineRationalTransposeMulVectorInit
        (rationalTransposeMulVectorCanonicalWord A v)) =
      machineRationalTransposeMulVectorSemanticState A v k := by
  intro k hk
  induction k with
  | zero => exact machineRationalTransposeMulVectorInit_semantics A v
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalTransposeMulVectorStep_semantics A v k (by omega)

theorem machineRationalTransposeMulVector_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalTransposeMulVectorStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalTransposeMulVectorStep]

theorem rationalTransposePrefix_all {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    rationalTransposePrefix A v d =
      List.ofFn (rationalTransposeMulVector A v) := by
  apply List.ext_getElem
  · simp [rationalTransposePrefix]
  · intro i hiLeft hiRight
    simp [rationalTransposePrefix, List.getElem_finRange]

theorem machineRationalTransposeMulVectorReversedCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalTransposeMulVectorReversedCode
        (rationalTransposeMulVectorCanonicalWord A v) =
      binaryListCode rationalEntryBinaryCode
        (List.ofFn (rationalTransposeMulVector A v)).reverse := by
  let word := rationalTransposeMulVectorCanonicalWord A v
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalTransposeMulVectorCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using h
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineRationalTransposeMulVectorReversedCode word = _
  rw [machineRationalTransposeMulVectorReversedCode,
    machineRationalTransposeMulVectorFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalTransposeMulVectorIterate_semantics A v d le_rfl]
  simp only [machineRationalTransposeMulVectorSemanticState]
  rw [show binaryListCode finUnaryCode ((List.finRange d).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineRationalTransposeMulVector_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [rationalTransposePrefix_all]

@[simp] theorem machineRationalTransposeMulVectorCode_encode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    machineRationalTransposeMulVectorCode
        (rationalTransposeMulVectorCanonicalWord A v) =
      rationalFiniteVectorCode (rationalTransposeMulVector A v) := by
  rw [machineRationalTransposeMulVectorCode,
    machineRationalTransposeMulVectorReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

theorem rationalTransposeMulVector_eq_pulledBack {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    rationalTransposeMulVector E.basis a =
      rationalPulledBackNormal E a := by
  rfl

end BeyondBethe
