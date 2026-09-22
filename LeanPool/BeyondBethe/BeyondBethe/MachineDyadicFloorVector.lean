/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDyadicFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalEllipsoidUpdate

/-!
# Polynomial-time coordinatewise dyadic floor

The scalar dyadic-floor machine returns the public one-natural rational code.
Ellipsoid memory instead uses the self-delimiting numerator--denominator entry
code.  We therefore normalize the same raw result into entry format and map
that exact operation over a bounded encoded vector.
-/

namespace BeyondBethe

open Complexity

def machineDyadicFloorEntryCode (word : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode (machineRawDyadicFloorCode word)

theorem machineDyadicFloorEntryCode_mem_FP :
    machineDyadicFloorEntryCode ∈ FP := by
  simpa only [machineDyadicFloorEntryCode] using!
    machineCompose_mem_FP machineRawDyadicFloorCode_mem_FP
      machineNormalizeRawRatEntryCode_mem_FP

@[simp] theorem machineDyadicFloorEntryCode_encode
    (p : ℕ) (q : RawRat) :
    machineDyadicFloorEntryCode
        (pair (List.replicate p true) (rawRatBinaryCode q)) =
      rationalEntryBinaryCode (dyadicFloor p q.value) := by
  rw [machineDyadicFloorEntryCode, machineRawDyadicFloorCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    binaryNormalizeRawRat_eq_value, binaryRawDyadicFloor_value,
    binaryDyadicFloor_eq_dyadicFloor]

theorem binaryRawDyadicFloorInt_natAbs_le
    (p : ℕ) (q : RawRat) :
    (binaryRawDyadicFloorInt p q).natAbs ≤
      q.num.natAbs * 2 ^ p + 1 := by
  rw [binaryRawDyadicFloorInt, binaryLongDiv_eq_div_mod]
  simp only [Prod.fst, Prod.snd]
  cases hnum : q.num with
  | ofNat n =>
      simp only [hnum, Int.natAbs_ofNat']
      exact (Nat.div_le_self _ _).trans (by omega)
  | negSucc n =>
      simp only [hnum, Int.natAbs_negSucc]
      split
      · simp only [Int.natAbs_neg]
        exact (Nat.div_le_self _ _).trans (by omega)
      · simp only [Int.natAbs_neg]
        have hdiv := Nat.div_le_self ((n + 1) * 2 ^ p) q.den
        simpa only [Nat.succ_eq_add_one] using! Nat.add_le_add_right hdiv 1

theorem binaryRawDyadicFloor_width_le
    (p : ℕ) (q : RawRat) :
    rawRatWidth (binaryRawDyadicFloor p q) ≤
      rawRatWidth q + p + 1 := by
  let w := rawRatWidth q
  have hnumLt := rawRat_num_lt_two_pow_width q
  have hmulLt : q.num.natAbs * 2 ^ p < 2 ^ (w + p) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hnumLt (by positivity)
  have hfloor := binaryRawDyadicFloorInt_natAbs_le p q
  have hfloorPow : (binaryRawDyadicFloorInt p q).natAbs ≤
      2 ^ (w + p) := by omega
  have hfloorSize := nat_size_le_succ_of_le_two_pow hfloorPow
  have hdenSize : (2 ^ p).size = p + 1 := Nat.size_pow
  simp only [binaryRawDyadicFloor, rawRatWidth]
  rw [hdenSize]
  refine max_le (by simpa only [w] using! hfloorSize) ?_
  omega

def dyadicFloorVectorCanonicalWord {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) : List Bool :=
  pair (List.replicate p true) (rationalFiniteVectorCode v)

theorem dyadicFloorVector_entry_code_length_le {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) (i : Fin d) :
    (rationalEntryBinaryCode (dyadicFloor p (v i))).length ≤
      100 + 72 * (dyadicFloorVectorCanonicalWord p v).length := by
  let word := dyadicFloorVectorCanonicalWord p v
  let q := rawRatOfRat (v i)
  have hq0 := rawRatWidth_le_binaryCode_length q
  rw [rawRatBinaryCode_rawRatOfRat] at hq0
  have helem := binaryListCode_element_length_le rationalEntryBinaryCode
    (show v i ∈ List.ofFn v by simp)
  have hq : rawRatWidth q ≤ word.length := by
    have helem' : (rationalEntryBinaryCode (v i)).length ≤
        (rationalFiniteVectorCode v).length := by
      simpa only [rationalFiniteVectorCode] using! helem
    apply hq0.trans
    apply helem'.trans
    simp only [word, dyadicFloorVectorCanonicalWord, pair_length,
      List.length_replicate]
    omega
  have hp : p ≤ word.length := by
    simp only [word, dyadicFloorVectorCanonicalWord, pair_length,
      List.length_replicate]
    omega
  have hraw := binaryRawDyadicFloor_width_le p q
  have hcanonical :=
    rationalEntryBinaryCode_binaryNormalizeRawRat_length_le
      (binaryRawDyadicFloor p q)
  rw [binaryNormalizeRawRat_eq_value, binaryRawDyadicFloor_value,
    binaryDyadicFloor_eq_dyadicFloor, rawRatOfRat_value] at hcanonical
  exact hcanonical.trans (by nlinarith)

def machineDyadicFloorVectorInputBound (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorInputBound word

theorem machineDyadicFloorVectorInputBound_mem_FP :
    machineDyadicFloorVectorInputBound ∈ FP :=
  machineRationalTransposeMulVectorInputBound_mem_FP

theorem dyadicFloorVector_code_length_le_bound {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) :
    (rationalFiniteVectorCode (dyadicFloorVector p v)).length ≤
      (machineDyadicFloorVectorInputBound
        (dyadicFloorVectorCanonicalWord p v)).length := by
  let word := dyadicFloorVectorCanonicalWord p v
  let L := 100 + 72 * word.length
  have hd : d ≤ word.length := by
    have hlist := binaryListCode_listLength_le rationalEntryBinaryCode
      (List.ofFn v)
    have hvector : (rationalFiniteVectorCode v).length ≤ word.length := by
      simp only [word, dyadicFloorVectorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    simpa only [rationalFiniteVectorCode, List.length_ofFn] using!
      hlist.trans hvector
  have heach : ∀ q ∈ List.ofFn (dyadicFloorVector p v),
      (rationalEntryBinaryCode q).length ≤ L := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact dyadicFloorVector_entry_code_length_le p v i
  have hsum := List.sum_le_card_nsmul
    ((List.ofFn (dyadicFloorVector p v)).map
      fun q ↦ 2 * (rationalEntryBinaryCode q).length + 2)
    (2 * L + 2) (by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨q, hq, rfl⟩ := hvalue
      have hq' := heach q hq
      omega)
  rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum]
  simp only [machineDyadicFloorVectorInputBound,
    machineRationalTransposeMulVectorInputBound,
    machineBinaryMulWidth, List.length_replicate,
    List.length_append, List.length_map, List.length_ofFn,
    Nat.nsmul_eq_mul] at hsum ⊢
  dsimp only [L, word] at hsum hd ⊢
  nlinarith [sq_nonneg (dyadicFloorVectorCanonicalWord p v).length]

/-! ## Bounded encoded-list scan -/

def machineDyadicFloorVectorPrecision (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDyadicFloorVectorEntries (word : List Bool) : List Bool :=
  machinePairSecond word

def machineDyadicFloorVectorCurrentEntry
    (state : List Bool) : List Bool :=
  machineDyadicFloorEntryCode
    (pair (machineRationalTransposeMulVectorStatePayload state)
      (machineListHead
        (machineRationalTransposeMulVectorRemaining state)))

def machineDyadicFloorVectorCandidate (state : List Bool) : List Bool :=
  pair (machineDyadicFloorVectorCurrentEntry state)
    (machineRationalTransposeMulVectorAccumulator state)

def machineDyadicFloorVectorNextAccumulator
    (state : List Bool) : List Bool :=
  (machineDyadicFloorVectorCandidate state).take
    (machineRationalTransposeMulVectorBound state).length

def machineDyadicFloorVectorAdvance (state : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineListTail (machineRationalTransposeMulVectorRemaining state))
    (machineDyadicFloorVectorNextAccumulator state)
    (machineRationalTransposeMulVectorStatePayload state)
    (machineRationalTransposeMulVectorBound state)

def machineDyadicFloorVectorStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineRationalTransposeMulVectorRemaining state) state
    (machineDyadicFloorVectorAdvance state)

def machineDyadicFloorVectorInit (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorPack
    (machineDyadicFloorVectorEntries word) []
    (machineDyadicFloorVectorPrecision word)
    (machineDyadicFloorVectorInputBound word)

def machineDyadicFloorVectorWidth (word : List Bool) : List Bool :=
  let bound := machineDyadicFloorVectorInputBound word
  machineRationalTransposeMulVectorPack bound bound bound bound

def machineDyadicFloorVectorFinalState (word : List Bool) : List Bool :=
  (machineDyadicFloorVectorStep)^[word.length]
    (machineDyadicFloorVectorInit word)

def machineDyadicFloorVectorReversedCode (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorAccumulator
    (machineDyadicFloorVectorFinalState word)

def machineDyadicFloorVectorCode (word : List Bool) : List Bool :=
  machineListReverse (machineDyadicFloorVectorReversedCode word)

theorem machineDyadicFloorVectorPrecision_mem_FP :
    machineDyadicFloorVectorPrecision ∈ FP := machinePairFirst_mem_FP

theorem machineDyadicFloorVectorEntries_mem_FP :
    machineDyadicFloorVectorEntries ∈ FP := machinePairSecond_mem_FP

theorem machineDyadicFloorVectorCurrentEntry_mem_FP :
    machineDyadicFloorVectorCurrentEntry ∈ FP := by
  have hhead := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListHead_mem_FP
  have hinput := machinePair_mem_FP
    machineRationalTransposeMulVectorStatePayload_mem_FP hhead
  simpa only [machineDyadicFloorVectorCurrentEntry] using!
    machineCompose_mem_FP hinput machineDyadicFloorEntryCode_mem_FP

theorem machineDyadicFloorVectorCandidate_mem_FP :
    machineDyadicFloorVectorCandidate ∈ FP :=
  machinePair_mem_FP machineDyadicFloorVectorCurrentEntry_mem_FP
    machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineDyadicFloorVectorNextAccumulator_mem_FP :
    machineDyadicFloorVectorNextAccumulator ∈ FP := by
  simpa only [machineDyadicFloorVectorNextAccumulator] using!
    machineTake_mem_FP machineRationalTransposeMulVectorBound_mem_FP
      machineDyadicFloorVectorCandidate_mem_FP

theorem machineDyadicFloorVectorAdvance_mem_FP :
    machineDyadicFloorVectorAdvance ∈ FP := by
  have htail := machineCompose_mem_FP
    machineRationalTransposeMulVectorRemaining_mem_FP machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineDyadicFloorVectorNextAccumulator_mem_FP
      (machinePair_mem_FP
        machineRationalTransposeMulVectorStatePayload_mem_FP
        machineRationalTransposeMulVectorBound_mem_FP))

theorem machineDyadicFloorVectorStep_mem_FP :
    machineDyadicFloorVectorStep ∈ FP :=
  machineIfEmpty_mem_FP machineRationalTransposeMulVectorRemaining_mem_FP
    id_mem_FP machineDyadicFloorVectorAdvance_mem_FP

theorem machineDyadicFloorVectorInit_mem_FP :
    machineDyadicFloorVectorInit ∈ FP :=
  machinePair_mem_FP machineDyadicFloorVectorEntries_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineDyadicFloorVectorPrecision_mem_FP
        machineDyadicFloorVectorInputBound_mem_FP))

theorem machineDyadicFloorVectorWidth_mem_FP :
    machineDyadicFloorVectorWidth ∈ FP := by
  have hbound := machineDyadicFloorVectorInputBound_mem_FP
  exact machinePair_mem_FP hbound
    (machinePair_mem_FP hbound (machinePair_mem_FP hbound hbound))

theorem machineDyadicFloorVectorInit_bound (word : List Bool) :
    MachineRationalTransposeMulVectorStateBound word
      (machineDyadicFloorVectorInit word) := by
  simp only [MachineRationalTransposeMulVectorStateBound,
    machineDyadicFloorVectorInit,
    machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineDyadicFloorVectorInputBound]
  refine ⟨trivial, ?_, by simp, ?_, trivial⟩
  · exact (machinePairSecond_length_le word).trans
      (machineRationalTransposeMulVector_word_le_bound word)
  · exact (machinePairFirst_length_le word).trans
      (machineRationalTransposeMulVector_word_le_bound word)

theorem machineDyadicFloorVectorStep_bound {word state : List Bool}
    (hs : MachineRationalTransposeMulVectorStateBound word state) :
    MachineRationalTransposeMulVectorStateBound word
      (machineDyadicFloorVectorStep state) := by
  dsimp only [MachineRationalTransposeMulVectorStateBound] at hs ⊢
  rcases hs with ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  by_cases hnil : machineRationalTransposeMulVectorRemaining state = []
  · rw [machineDyadicFloorVectorStep, hnil, machineIfEmpty_nil]
    exact ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  · cases hcode : machineRationalTransposeMulVectorRemaining state with
    | nil => exact False.elim (hnil hcode)
    | cons bit tail =>
        rw [machineDyadicFloorVectorStep, hcode, machineIfEmpty_cons,
          machineDyadicFloorVectorAdvance]
        simp only [machineRationalTransposeMulVectorRemaining_pack,
          machineRationalTransposeMulVectorAccumulator_pack,
          machineRationalTransposeMulVectorStatePayload_pack,
          machineRationalTransposeMulVectorBound_pack]
        refine ⟨trivial, ?_, ?_, hpayload, hbound⟩
        · exact (machineListTail_length_le
            (machineRationalTransposeMulVectorRemaining state)).trans
              hremaining
        · rw [machineDyadicFloorVectorNextAccumulator, hbound]
          exact List.length_take_le _ _

theorem machineDyadicFloorVectorIterate_bound (word : List Bool) : ∀ k,
    MachineRationalTransposeMulVectorStateBound word
      ((machineDyadicFloorVectorStep)^[k]
        (machineDyadicFloorVectorInit word)) := by
  intro k
  induction k with
  | zero => exact machineDyadicFloorVectorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineDyadicFloorVectorStep_bound ih

theorem machineDyadicFloorVectorIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ word.length) :
    ((machineDyadicFloorVectorStep)^[iterations]
      (machineDyadicFloorVectorInit word)).length ≤
        (machineDyadicFloorVectorWidth word).length := by
  rcases machineDyadicFloorVectorIterate_bound word iterations with
    ⟨hdecomp, hremaining, hacc, hpayload, hbound⟩
  rw [hdecomp, hbound]
  simp only [machineRationalTransposeMulVectorPack,
    machineDyadicFloorVectorWidth, machineDyadicFloorVectorInputBound,
    pair_length]
  omega

theorem machineDyadicFloorVectorFinalState_mem_FP :
    machineDyadicFloorVectorFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineDyadicFloorVectorStep_mem_FP
    machineDyadicFloorVectorInit_mem_FP id_mem_FP
    machineDyadicFloorVectorWidth_mem_FP
    machineDyadicFloorVectorIterate_length_le_width

theorem machineDyadicFloorVectorReversedCode_mem_FP :
    machineDyadicFloorVectorReversedCode ∈ FP := by
  simpa only [machineDyadicFloorVectorReversedCode] using!
    machineCompose_mem_FP machineDyadicFloorVectorFinalState_mem_FP
      machineRationalTransposeMulVectorAccumulator_mem_FP

theorem machineDyadicFloorVectorCode_mem_FP :
    machineDyadicFloorVectorCode ∈ FP := by
  simpa only [machineDyadicFloorVectorCode] using!
    machineCompose_mem_FP machineDyadicFloorVectorReversedCode_mem_FP
      machineListReverse_mem_FP

/-! ## Exact scan semantics -/

def dyadicFloorVectorPrefix {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) (k : ℕ) : List ℚ :=
  (List.ofFn v).take k |>.map (dyadicFloor p)

def machineDyadicFloorVectorSemanticState {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) (k : ℕ) : List Bool :=
  let word := dyadicFloorVectorCanonicalWord p v
  machineRationalTransposeMulVectorPack
    (binaryListCode rationalEntryBinaryCode ((List.ofFn v).drop k))
    (binaryListCode rationalEntryBinaryCode
      (dyadicFloorVectorPrefix p v k).reverse)
    (List.replicate p true) (machineDyadicFloorVectorInputBound word)

theorem machineDyadicFloorVectorInit_semantics {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) :
    machineDyadicFloorVectorInit (dyadicFloorVectorCanonicalWord p v) =
      machineDyadicFloorVectorSemanticState p v 0 := by
  simp [machineDyadicFloorVectorInit,
    machineDyadicFloorVectorSemanticState,
    machineDyadicFloorVectorEntries,
    machineDyadicFloorVectorPrecision,
    dyadicFloorVectorCanonicalWord,
    rationalFiniteVectorCode, dyadicFloorVectorPrefix, binaryListCode]

theorem dyadicFloorVectorPrefix_succ {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    dyadicFloorVectorPrefix p v (k + 1) =
      dyadicFloorVectorPrefix p v k ++
        [dyadicFloor p (v ⟨k, hk⟩)] := by
  simp only [dyadicFloorVectorPrefix, List.map_take]
  have hkm : k < (List.ofFn v).length := by simpa
  simpa using! congrArg (List.map (dyadicFloor p))
    (List.take_concat_get hkm).symm

theorem machineDyadicFloorVectorStep_semantics {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) (k : ℕ) (hk : k < d) :
    machineDyadicFloorVectorStep
        (machineDyadicFloorVectorSemanticState p v k) =
      machineDyadicFloorVectorSemanticState p v (k + 1) := by
  let word := dyadicFloorVectorCanonicalWord p v
  let i : Fin d := ⟨k, hk⟩
  have hdrop : (List.ofFn v).drop k =
      v i :: (List.ofFn v).drop (k + 1) := by
    convert List.drop_eq_getElem_cons
      (show k < (List.ofFn v).length by simpa) using 1
    simp [i]
  have hprefix := dyadicFloorVectorPrefix_succ p v k hk
  have hreverse : (dyadicFloorVectorPrefix p v (k + 1)).reverse =
      dyadicFloor p (v i) :: (dyadicFloorVectorPrefix p v k).reverse := by
    rw [hprefix, List.reverse_append]
    simp [i]
  have hcand :
      (binaryListCode rationalEntryBinaryCode
        (dyadicFloorVectorPrefix p v (k + 1)).reverse).length ≤
        (machineDyadicFloorVectorInputBound word).length := by
    have hprefixBound := binaryListCode_take_reverse_length_le
      rationalEntryBinaryCode (List.ofFn (dyadicFloorVector p v)) (k + 1)
    have hprefixEq : dyadicFloorVectorPrefix p v (k + 1) =
        (List.ofFn (dyadicFloorVector p v)).take (k + 1) := by
      rw [dyadicFloorVectorPrefix, List.map_take, List.map_ofFn]
      rfl
    rw [hprefixEq]
    exact hprefixBound.trans (dyadicFloorVector_code_length_le_bound p v)
  have hcandPair :
      (pair (rationalEntryBinaryCode (dyadicFloor p (v i)))
        (binaryListCode rationalEntryBinaryCode
          (dyadicFloorVectorPrefix p v k).reverse)).length ≤
        (machineDyadicFloorVectorInputBound word).length := by
    simpa only [hreverse, binaryListCode] using! hcand
  have hnonempty :
      binaryListCode rationalEntryBinaryCode ((List.ofFn v).drop k) ≠ [] := by
    rw [hdrop]
    exact binaryListCode_cons_ne_nil rationalEntryBinaryCode (v i)
      ((List.ofFn v).drop (k + 1))
  rw [machineDyadicFloorVectorStep]
  simp only [machineDyadicFloorVectorSemanticState,
    machineRationalTransposeMulVectorRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _ hnonempty,
    machineDyadicFloorVectorAdvance]
  simp only [machineRationalTransposeMulVectorRemaining_pack,
    machineRationalTransposeMulVectorAccumulator_pack,
    machineRationalTransposeMulVectorStatePayload_pack,
    machineRationalTransposeMulVectorBound_pack,
    machineDyadicFloorVectorNextAccumulator,
    machineDyadicFloorVectorCandidate,
    machineDyadicFloorVectorCurrentEntry]
  rw [hdrop, machineListHead_cons, machineListTail_cons]
  change machineRationalTransposeMulVectorPack _
      ((pair (machineDyadicFloorEntryCode
          (pair (List.replicate p true)
            (rationalEntryBinaryCode (v i))))
        (binaryListCode rationalEntryBinaryCode
          (dyadicFloorVectorPrefix p v k).reverse)).take
        (machineDyadicFloorVectorInputBound word).length) _ _ = _
  rw [← rawRatBinaryCode_rawRatOfRat,
    machineDyadicFloorEntryCode_encode, rawRatOfRat_value]
  change machineRationalTransposeMulVectorPack _
      ((pair (rationalEntryBinaryCode (dyadicFloor p (v i)))
        (binaryListCode rationalEntryBinaryCode
          (dyadicFloorVectorPrefix p v k).reverse)).take
        (machineDyadicFloorVectorInputBound word).length) _ _ = _
  rw [List.take_of_length_le hcandPair, hreverse]
  rfl

theorem machineDyadicFloorVectorIterate_semantics {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) : ∀ k ≤ d,
    (machineDyadicFloorVectorStep)^[k]
      (machineDyadicFloorVectorInit
        (dyadicFloorVectorCanonicalWord p v)) =
      machineDyadicFloorVectorSemanticState p v k := by
  intro k hk
  induction k with
  | zero => exact machineDyadicFloorVectorInit_semantics p v
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineDyadicFloorVectorStep_semantics p v k (by omega)

theorem machineDyadicFloorVector_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineDyadicFloorVectorStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineDyadicFloorVectorStep]

theorem dyadicFloorVectorPrefix_all {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) :
    dyadicFloorVectorPrefix p v d =
      List.ofFn (dyadicFloorVector p v) := by
  rw [dyadicFloorVectorPrefix,
    List.take_of_length_le (by simp), List.map_ofFn]
  rfl

theorem machineDyadicFloorVectorReversedCode_encode {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) :
    machineDyadicFloorVectorReversedCode
        (dyadicFloorVectorCanonicalWord p v) =
      binaryListCode rationalEntryBinaryCode
        (List.ofFn (dyadicFloorVector p v)).reverse := by
  let word := dyadicFloorVectorCanonicalWord p v
  have hd : d ≤ word.length := by
    have hlist := binaryListCode_listLength_le rationalEntryBinaryCode
      (List.ofFn v)
    have hvector : (rationalFiniteVectorCode v).length ≤ word.length := by
      simp only [word, dyadicFloorVectorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    simpa only [rationalFiniteVectorCode, List.length_ofFn] using!
      hlist.trans hvector
  have hsplit : word.length = (word.length - d) + d := by omega
  change machineDyadicFloorVectorReversedCode word = _
  rw [machineDyadicFloorVectorReversedCode,
    machineDyadicFloorVectorFinalState, hsplit,
    Function.iterate_add_apply,
    machineDyadicFloorVectorIterate_semantics p v d le_rfl]
  simp only [machineDyadicFloorVectorSemanticState]
  rw [show binaryListCode rationalEntryBinaryCode
      ((List.ofFn v).drop d) = [] by
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl]
  rw [machineDyadicFloorVector_done_iterate]
  simp only [machineRationalTransposeMulVectorAccumulator_pack]
  rw [dyadicFloorVectorPrefix_all]

@[simp] theorem machineDyadicFloorVectorCode_encode {d : ℕ}
    (p : ℕ) (v : Fin d → ℚ) :
    machineDyadicFloorVectorCode
        (dyadicFloorVectorCanonicalWord p v) =
      rationalFiniteVectorCode (dyadicFloorVector p v) := by
  rw [machineDyadicFloorVectorCode,
    machineDyadicFloorVectorReversedCode_encode,
    machineListReverse_encode, List.reverse_reverse]
  rfl

end BeyondBethe
