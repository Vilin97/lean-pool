/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineRationalMatrixMulVector
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorScale

/-!
# Polynomial-time componentwise subtraction of rational vectors

The canonical input stores a unary dimension followed by two rational-vector
words.  A verified coordinate routine indexes both words, negates the second
raw rational, adds, and normalizes.  A bounded finite-word scan maps this
routine over all coordinates and reverses its accumulator once at the end.
-/

namespace BeyondBethe

open Complexity

def rationalVectorSub {d : ℕ}
    (x y : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ x i - y i

def machineRationalVectorSubEntryCode
    (word : List Bool) : List Bool :=
  let index := machinePairFirst word
  let payload := machinePairSecond word
  let xCode := machinePairFirst payload
  let yCode := machinePairSecond payload
  let xEntry := machineListIndex (pair index xCode)
  let yEntry := machineListIndex (pair index yCode)
  machineNormalizeRawRatEntryCode
    (machineRawRatAddCode
      (pair xEntry (machineRawRatNegCode yEntry)))

theorem machineRationalVectorSubEntryCode_mem_FP :
    machineRationalVectorSubEntryCode ∈ FP := by
  have hindex := machinePairFirst_mem_FP
  have hpayload := machinePairSecond_mem_FP
  have hxCode := machineCompose_mem_FP hpayload machinePairFirst_mem_FP
  have hyCode := machineCompose_mem_FP hpayload machinePairSecond_mem_FP
  have hxInput := machinePair_mem_FP hindex hxCode
  have hyInput := machinePair_mem_FP hindex hyCode
  have hxEntry := machineCompose_mem_FP hxInput machineListIndex_mem_FP
  have hyEntry := machineCompose_mem_FP hyInput machineListIndex_mem_FP
  have hnegY := machineCompose_mem_FP hyEntry machineRawRatNegCode_mem_FP
  have haddInput := machinePair_mem_FP hxEntry hnegY
  have hadd := machineCompose_mem_FP haddInput machineRawRatAddCode_mem_FP
  simpa only [machineRationalVectorSubEntryCode] using!
    machineCompose_mem_FP hadd machineNormalizeRawRatEntryCode_mem_FP

@[simp] theorem machineRationalVectorSubEntryCode_encode {d : ℕ}
    (x y : Fin d → ℚ) (i : Fin d) :
    machineRationalVectorSubEntryCode
        (pair (List.replicate i.1 true)
          (pair (rationalFiniteVectorCode x)
            (rationalFiniteVectorCode y))) =
      rationalEntryBinaryCode (rationalVectorSub x y i) := by
  rw [machineRationalVectorSubEntryCode]
  simp only [machinePairFirst_pair, machinePairSecond_pair,
    rationalFiniteVectorCode]
  rw [machineListIndex_binaryListCode (k := i.1),
    machineListIndex_binaryListCode (k := i.1)]
  · simp only [List.getElem_ofFn, ← rawRatBinaryCode_rawRatOfRat,
      machineRawRatNegCode_encode, machineRawRatAddCode_encode,
      machineNormalizeRawRatEntryCode_encode]
    simp [binaryNormalizeRawRat_eq_value, RawRat.value_add,
      RawRat.value_neg, rawRatOfRat_value, rationalVectorSub,
      sub_eq_add_neg]
  · simp
  · simp

def rawRationalVectorSubCoordinate {d : ℕ}
    (x y : Fin d → ℚ) (i : Fin d) : RawRat :=
  (rawRatOfRat (x i)).sub (rawRatOfRat (y i))

theorem rawRationalVectorSubCoordinate_value {d : ℕ}
    (x y : Fin d → ℚ) (i : Fin d) :
    (rawRationalVectorSubCoordinate x y i).value =
      rationalVectorSub x y i := by
  simp [rawRationalVectorSubCoordinate, rationalVectorSub,
    RawRat.sub, RawRat.value_add, RawRat.value_neg, rawRatOfRat_value,
    sub_eq_add_neg]

def rationalVectorSubCanonicalWord {d : ℕ}
    (x y : Fin d → ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair (rationalFiniteVectorCode x)
      (rationalFiniteVectorCode y))

theorem rawRationalVectorSubCoordinate_width_le {d : ℕ}
    (x y : Fin d → ℚ) (i : Fin d) :
    rawRatWidth (rawRationalVectorSubCoordinate x y i) ≤
      2 * (rationalVectorSubCanonicalWord x y).length + 1 := by
  let word := rationalVectorSubCanonicalWord x y
  have hxElem := binaryListCode_element_length_le
    rationalEntryBinaryCode
    (show x i ∈ List.ofFn x by simp)
  have hyElem := binaryListCode_element_length_le
    rationalEntryBinaryCode
    (show y i ∈ List.ofFn y by simp)
  have hxVector : (rationalFiniteVectorCode x).length ≤ word.length := by
    have hinner := machinePairFirst_length_le
      (pair (rationalFiniteVectorCode x) (rationalFiniteVectorCode y))
    have hpayload :
        (pair (rationalFiniteVectorCode x)
          (rationalFiniteVectorCode y)).length ≤ word.length := by
      simpa only [word, rationalVectorSubCanonicalWord,
        machinePairSecond_pair] using! machinePairSecond_length_le word
    simpa only [machinePairFirst_pair] using! hinner.trans hpayload
  have hyVector : (rationalFiniteVectorCode y).length ≤ word.length := by
    have hinner := machinePairSecond_length_le
      (pair (rationalFiniteVectorCode x) (rationalFiniteVectorCode y))
    have hpayload :
        (pair (rationalFiniteVectorCode x)
          (rationalFiniteVectorCode y)).length ≤ word.length := by
      simpa only [word, rationalVectorSubCanonicalWord,
        machinePairSecond_pair] using! machinePairSecond_length_le word
    simpa only [machinePairSecond_pair] using! hinner.trans hpayload
  have hxWidth : rawRatWidth (rawRatOfRat (x i)) ≤ word.length := by
    have hxCode :
        (rawRatBinaryCode (rawRatOfRat (x i))).length ≤
          (rationalFiniteVectorCode x).length := by
      simpa only [rationalFiniteVectorCode,
        rawRatBinaryCode_rawRatOfRat] using! hxElem
    exact (rawRatWidth_le_binaryCode_length _).trans
      (hxCode.trans hxVector)
  have hyWidth : rawRatWidth (rawRatOfRat (y i)) ≤ word.length := by
    have hyCode :
        (rawRatBinaryCode (rawRatOfRat (y i))).length ≤
          (rationalFiniteVectorCode y).length := by
      simpa only [rationalFiniteVectorCode,
        rawRatBinaryCode_rawRatOfRat] using! hyElem
    exact (rawRatWidth_le_binaryCode_length _).trans
      (hyCode.trans hyVector)
  change rawRatWidth ((rawRatOfRat (x i)).sub (rawRatOfRat (y i))) ≤
    2 * word.length + 1
  exact (rawRatWidth_sub_le _ _).trans (by omega)

theorem rationalVectorSub_entry_code_length_le {d : ℕ}
    (x y : Fin d → ℚ) (i : Fin d) :
    (rationalEntryBinaryCode (rationalVectorSub x y i)).length ≤
      100 + 72 * (rationalVectorSubCanonicalWord x y).length := by
  have hnormalize :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (rawRationalVectorSubCoordinate x y i)
  rw [binaryNormalizeRawRat_eq_value,
    rawRationalVectorSubCoordinate_value] at hnormalize
  have hwidth := rawRationalVectorSubCoordinate_width_le x y i
  omega

def machineRationalVectorSubInputBound
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineRationalVectorSubInputBound_mem_FP :
    machineRationalVectorSubInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem rationalVectorSub_code_length_le_bound {d : ℕ}
    (x y : Fin d → ℚ) :
    (rationalFiniteVectorCode (rationalVectorSub x y)).length ≤
      (machineRationalVectorSubInputBound
        (rationalVectorSubCanonicalWord x y)).length := by
  let word := rationalVectorSubCanonicalWord x y
  let B := 100 + 72 * word.length
  have hdim : d ≤ word.length := by
    have hfirst := machinePairFirst_length_le word
    simpa only [word, rationalVectorSubCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! hfirst
  have heach : ∀ q ∈ List.ofFn (rationalVectorSub x y),
      (rationalEntryBinaryCode q).length ≤ B := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact rationalVectorSub_entry_code_length_le x y i
  have hsum := List.sum_le_card_nsmul
    ((List.ofFn (rationalVectorSub x y)).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    (2 * B + 2) (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum]
  simp only [machineRationalVectorSubInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, List.length_map, List.length_ofFn,
    Nat.nsmul_eq_mul] at hsum ⊢
  dsimp only [B, word] at hsum ⊢
  nlinarith [sq_nonneg (rationalVectorSubCanonicalWord x y).length]

/-! ## Bounded scan -/

def machineRationalVectorSubCurrentEntry
    (state : List Bool) : List Bool :=
  machineRationalVectorSubEntryCode
    (pair (machineRationalTransposeMulVectorCurrentIndex state)
      (machineRationalTransposeMulVectorStatePayload state))

def machineRationalVectorSubCandidate
    (state : List Bool) : List Bool :=
  pair (machineRationalVectorSubCurrentEntry state)
    (machineRationalTransposeMulVectorAccumulator state)

def machineRationalVectorSubNextAccumulator
    (state : List Bool) : List Bool :=
  (machineRationalVectorSubCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

def machineRationalVectorSubAdvance
    (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineRationalVectorSubNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

def machineRationalVectorSubStep
    (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineRationalVectorSubAdvance state)

def machineRationalVectorSubInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineRationalTransposeMulVectorIndices word) []
    (machineRationalTransposeMulVectorPayload word)
    (machineRationalVectorSubInputBound word)

def machineRationalVectorSubWidth (word : List Bool) : List Bool :=
  let bound := machineRationalVectorSubInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

def machineRationalVectorSubFinalState
    (word : List Bool) : List Bool :=
  (machineRationalVectorSubStep)^[word.length]
    (machineRationalVectorSubInit word)

def machineRationalVectorSubReversedCode
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineRationalVectorSubFinalState word)

def machineRationalVectorSubCode
    (word : List Bool) : List Bool :=
  machineListReverse (machineRationalVectorSubReversedCode word)

theorem machineRationalVectorSubCurrentEntry_mem_FP :
    machineRationalVectorSubCurrentEntry ∈ FP := by
  have hp := machinePair_mem_FP
    machineRationalTransposeMulVectorCurrentIndex_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP
  simpa only [machineRationalVectorSubCurrentEntry] using!
    machineCompose_mem_FP hp machineRationalVectorSubEntryCode_mem_FP

theorem machineRationalVectorSubCandidate_mem_FP :
    machineRationalVectorSubCandidate ∈ FP :=
  machinePair_mem_FP machineRationalVectorSubCurrentEntry_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalVectorSubNextAccumulator_mem_FP :
    machineRationalVectorSubNextAccumulator ∈ FP := by
  simpa only [machineRationalVectorSubNextAccumulator] using!
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineRationalVectorSubCandidate_mem_FP

theorem machineRationalVectorSubAdvance_mem_FP :
    machineRationalVectorSubAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineRationalVectorSubNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineRationalVectorSubStep_mem_FP :
    machineRationalVectorSubStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineRationalVectorSubAdvance_mem_FP

theorem machineRationalVectorSubInit_mem_FP :
    machineRationalVectorSubInit ∈ FP := by
  exact machinePair_mem_FP machineRationalTransposeMulVectorIndices_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineRationalTransposeMulVectorPayload_mem_FP
        machineRationalVectorSubInputBound_mem_FP))

theorem machineRationalVectorSubWidth_mem_FP :
    machineRationalVectorSubWidth ∈ FP := by
  exact machinePair_mem_FP machineRationalVectorSubInputBound_mem_FP
    (machinePair_mem_FP machineRationalVectorSubInputBound_mem_FP
      (machinePair_mem_FP machineRationalVectorSubInputBound_mem_FP
        machineRationalVectorSubInputBound_mem_FP))

theorem machineRationalVectorSubStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineRationalVectorSubStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineRationalVectorSubStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineRationalVectorSubStep, hcode,
          machineIfEmpty_cons, machineRationalVectorSubAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineRationalVectorSubNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineRationalVectorSubIterate_bound
    (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineRationalVectorSubStep)^[k]
        (machineRationalVectorSubInit word)) := by
  intro k
  induction k with
  | zero =>
      simpa only [machineRationalVectorSubInit,
        machineRationalVectorSubInputBound,
        machineRationalTransposeMulVectorInit] using!
          machineRationalTransposeMulVectorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineRationalVectorSubStep_bound ih

theorem machineRationalVectorSubIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineRationalVectorSubStep)^[iterations]
      (machineRationalVectorSubInit word)).length ≤
        (machineRationalVectorSubWidth word).length := by
  rcases machineRationalVectorSubIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineRationalVectorSubWidth, machineRationalVectorSubInputBound,
    pair_length]
  omega

theorem machineRationalVectorSubFinalState_mem_FP :
    machineRationalVectorSubFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineRationalVectorSubStep_mem_FP
    machineRationalVectorSubInit_mem_FP id_mem_FP
    machineRationalVectorSubWidth_mem_FP
    machineRationalVectorSubIterate_length_le_width

theorem machineRationalVectorSubReversedCode_mem_FP :
    machineRationalVectorSubReversedCode ∈ FP := by
  simpa only [machineRationalVectorSubReversedCode] using!
    machineCompose_mem_FP machineRationalVectorSubFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineRationalVectorSubCode_mem_FP :
    machineRationalVectorSubCode ∈ FP := by
  simpa only [machineRationalVectorSubCode] using!
    machineCompose_mem_FP machineRationalVectorSubReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact scan semantics -/

def rationalVectorSubPrefix {d : ℕ}
    (x y : Fin d → ℚ) (k : ℕ) : List ℚ :=
  ((List.finRange d).take k).map fun i ↦ rationalVectorSub x y i

def machineRationalVectorSubSemanticState {d : ℕ}
    (x y : Fin d → ℚ) (k : ℕ) : List Bool :=
  let word := rationalVectorSubCanonicalWord x y
  machineRationalTransposeMulVectorPack
    (binaryListCode finUnaryCode ((List.finRange d).drop k))
    (binaryListCode rationalEntryBinaryCode
      (rationalVectorSubPrefix x y k).reverse)
    (pair (rationalFiniteVectorCode x) (rationalFiniteVectorCode y))
    (machineRationalVectorSubInputBound word)

theorem machineRationalVectorSubInit_semantics {d : ℕ}
    (x y : Fin d → ℚ) :
    machineRationalVectorSubInit (rationalVectorSubCanonicalWord x y) =
      machineRationalVectorSubSemanticState x y 0 := by
  simp [machineRationalVectorSubInit,
    machineRationalVectorSubSemanticState,
    machineRationalTransposeMulVectorIndices,
    machineRationalTransposeMulVectorDimension,
    machineRationalTransposeMulVectorPayload,
    rationalVectorSubCanonicalWord, machineUnaryRangeCode_encode,
    finRangeUnaryCode, rationalVectorSubPrefix, binaryListCode]

theorem rationalVectorSubPrefix_succ {d : ℕ}
    (x y : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    rationalVectorSubPrefix x y (k + 1) =
      rationalVectorSubPrefix x y k ++
        [rationalVectorSub x y ⟨k, hk⟩] := by
  simp only [rationalVectorSubPrefix, List.map_take]
  have hkm : k < (List.finRange d).length := by simpa
  simpa [List.getElem_finRange] using!
    congrArg (List.map fun i ↦ rationalVectorSub x y i)
      (List.take_concat_get hkm).symm

theorem machineRationalVectorSubStep_semantics {d : ℕ}
    (x y : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    machineRationalVectorSubStep
        (machineRationalVectorSubSemanticState x y k) =
      machineRationalVectorSubSemanticState x y (k + 1) := by
  let word := rationalVectorSubCanonicalWord x y
  let i : Fin d := ⟨k, hk⟩
  have hdrop :
      (List.finRange d).drop k =
        i :: (List.finRange d).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.finRange d).length by simpa) using 1
    simp [i, List.getElem_finRange]
  have hprefix := rationalVectorSubPrefix_succ x y k hk
  have hreverse :
      (rationalVectorSubPrefix x y (k + 1)).reverse =
        rationalVectorSub x y i ::
          (rationalVectorSubPrefix x y k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [i]
  have hcand :
      (binaryListCode rationalEntryBinaryCode
        (rationalVectorSubPrefix x y (k + 1)).reverse).length ≤
        (machineRationalVectorSubInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      rationalEntryBinaryCode (List.ofFn (rationalVectorSub x y)) (k + 1)
    have hprefixEq : rationalVectorSubPrefix x y (k + 1) =
        (List.ofFn (rationalVectorSub x y)).take (k + 1) := by
      apply List.ext_getElem
      · simp [rationalVectorSubPrefix]
      · intro r hrLeft hrRight
        simp [rationalVectorSubPrefix, List.getElem_finRange]
    rw [hprefixEq]
    exact hprefixBound.trans (rationalVectorSub_code_length_le_bound x y)
  have hcandPair :
      (pair (rationalEntryBinaryCode (rationalVectorSub x y i))
        (binaryListCode rationalEntryBinaryCode
          (rationalVectorSubPrefix x y k).reverse)).length ≤
        (machineRationalVectorSubInputBound word).length := by
    simpa only [hreverse, binaryListCode] using! hcand
  have hnonempty :
      binaryListCode finUnaryCode ((List.finRange d).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil finUnaryCode i _
  rw [machineRationalVectorSubStep]
  simp only [machineRationalVectorSubSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineRationalVectorSubAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineRationalVectorSubNextAccumulator,
    machineRationalVectorSubCandidate,
    machineRationalVectorSubCurrentEntry,
    machineRationalTransposeMulVectorCurrentIndex]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineRationalVectorSubEntryCode
        (pair (finUnaryCode i)
          (pair (rationalFiniteVectorCode x)
            (rationalFiniteVectorCode y))))
        (binaryListCode rationalEntryBinaryCode
          (rationalVectorSubPrefix x y k).reverse)).take
        (machineRationalVectorSubInputBound word).length) _ _ = _
  rw [show finUnaryCode i = List.replicate i.1 true by rfl,
    machineRationalVectorSubEntryCode_encode]
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineRationalVectorSubIterate_semantics {d : ℕ}
    (x y : Fin d → ℚ) : ∀ k ≤ d,
    (machineRationalVectorSubStep)^[k]
      (machineRationalVectorSubInit (rationalVectorSubCanonicalWord x y)) =
      machineRationalVectorSubSemanticState x y k := by
  intro k hk
  induction k with
  | zero => exact machineRationalVectorSubInit_semantics x y
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineRationalVectorSubStep_semantics x y k (by omega)

theorem machineRationalVectorSub_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalVectorSubStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalVectorSubStep]

theorem rationalVectorSubPrefix_all {d : ℕ}
    (x y : Fin d → ℚ) :
    rationalVectorSubPrefix x y d =
      List.ofFn (rationalVectorSub x y) := by
  apply List.ext_getElem
  · simp [rationalVectorSubPrefix]
  · intro i hiLeft hiRight
    simp [rationalVectorSubPrefix, List.getElem_finRange]

theorem machineRationalVectorSubReversedCode_encode {d : ℕ}
    (x y : Fin d → ℚ) :
    machineRationalVectorSubReversedCode
        (rationalVectorSubCanonicalWord x y) =
      binaryListCode rationalEntryBinaryCode
        (List.ofFn (rationalVectorSub x y)).reverse := by
  let word := rationalVectorSubCanonicalWord x y
  have hd : d ≤ word.length := by
    have h := machinePairFirst_length_le word
    simpa only [word, rationalVectorSubCanonicalWord,
      machinePairFirst_pair, List.length_replicate] using! h
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineRationalVectorSubReversedCode word = _
  rw [machineRationalVectorSubReversedCode,
    machineRationalVectorSubFinalState, hsplit,
    Function.iterate_add_apply,
    machineRationalVectorSubIterate_semantics x y d le_rfl]
  simp only [machineRationalVectorSubSemanticState]
  rw [show binaryListCode finUnaryCode ((List.finRange d).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineRationalVectorSub_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [rationalVectorSubPrefix_all]

@[simp] theorem machineRationalVectorSubCode_encode {d : ℕ}
    (x y : Fin d → ℚ) :
    machineRationalVectorSubCode (rationalVectorSubCanonicalWord x y) =
      rationalFiniteVectorCode (rationalVectorSub x y) := by
  rw [machineRationalVectorSubCode,
    machineRationalVectorSubReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
