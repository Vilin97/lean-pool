/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.StaticDirectCoverage

/-! # Exactness of packed pair-occurrence states -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private theorem bitSetB_eq_getLsbD (code : UInt64) (index : Fin 64) :
    bitSetB code index.val = code.toBitVec.getLsbD index.val := by
  unfold bitSetB
  have hmasked :
      ((code >>> UInt64.ofNat index.val) &&& 1).toBitVec =
        (BitVec.ofBool (code.toBitVec.getLsbD index.val)).setWidth 64 := by
    rw [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_one, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
    change (BitVec.ofBool ((code.toBitVec >>>
      ((UInt64.ofNat index.val).toBitVec % 64).toNat).getLsbD 0)).setWidth 64 =
      (BitVec.ofBool (code.toBitVec.getLsbD index.val)).setWidth 64
    rw [BitVec.getLsbD_ushiftRight]
    congr 3
    simp [index.isLt]
  cases hbit : code.toBitVec.getLsbD index.val with
  | false =>
      have hzero : (code >>> UInt64.ofNat index.val) &&& 1 = 0 := by
        apply UInt64.toBitVec_inj.mp
        rw [hmasked, hbit]
        decide
      simp [hzero]
  | true =>
      have hone : (code >>> UInt64.ofNat index.val) &&& 1 = 1 := by
        apply UInt64.toBitVec_inj.mp
        rw [hmasked, hbit]
        decide
      simp [hone]

@[simp] private theorem bitSetB_or (left right : UInt64) (index : Fin 64) :
    bitSetB (left ||| right) index.val =
      (bitSetB left index.val || bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

@[simp] private theorem bitSetB_and (left right : UInt64) (index : Fin 64) :
    bitSetB (left &&& right) index.val =
      (bitSetB left index.val && bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

@[simp] private theorem bitSetB_zero (index : Fin 64) :
    bitSetB 0 index.val = false := by
  rw [bitSetB_eq_getLsbD]
  simp

private theorem bitSetB_singleBit (shift index : Fin 64) :
    bitSetB (1 <<< UInt64.ofNat shift.val) index.val =
      decide (index = shift) := by
  rw [bitSetB_eq_getLsbD, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_one, BitVec.getLsbD_shiftLeft']
  simp only [Fin.is_lt, decide_true, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_umod, UInt64.toNat_toBitVec, UInt64.toNat_ofNat',
    Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceDvd,
    Nat.mod_mod_of_dvd, Bool.true_and, BitVec.getLsbD_one, Nat.ofNat_pos]
  rw [Nat.mod_eq_of_lt shift.isLt]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq]
  omega

private theorem varIndex_lt (first second : Vertex) :
    varIndex first second < 64 := by
  unfold varIndex
  omega

@[simp] private theorem bitSetB_pairBitAt
    (first second : Vertex) (index : Fin 64) :
    bitSetB (1 <<< UInt64.ofNat (varIndex first second)) index.val =
      decide (index.val = varIndex first second) := by
  let shift : Fin 64 := ⟨varIndex first second, varIndex_lt first second⟩
  calc
    _ = decide (index = shift) := by
      simpa only [shift] using bitSetB_singleBit shift index
    _ = _ := by simp [shift, Fin.ext_iff]

@[simp] private theorem bitSetB_or_pair
    (left right : UInt64) (first second : Vertex) :
    bitSetB (left ||| right) (varIndex first second) =
      (bitSetB left (varIndex first second) ||
        bitSetB right (varIndex first second)) := by
  let index : Fin 64 := ⟨varIndex first second, varIndex_lt first second⟩
  simpa only [index] using bitSetB_or left right index

@[simp] private theorem bitSetB_and_pair
    (left right : UInt64) (first second : Vertex) :
    bitSetB (left &&& right) (varIndex first second) =
      (bitSetB left (varIndex first second) &&
        bitSetB right (varIndex first second)) := by
  let index : Fin 64 := ⟨varIndex first second, varIndex_lt first second⟩
  simpa only [index] using bitSetB_and left right index

@[simp] private theorem bitSetB_zero_pair (first second : Vertex) :
    bitSetB 0 (varIndex first second) = false := by
  let index : Fin 64 := ⟨varIndex first second, varIndex_lt first second⟩
  simpa only [index] using bitSetB_zero index

private theorem bitSetB_foldPairBits
    (row : UInt64) (pairs : List (Vertex × Vertex))
    (result : UInt64) (index : Fin 64) :
    bitSetB (pairs.foldl (addPairBit row) result) index.val =
      (bitSetB result index.val ||
        pairs.any fun pair =>
          pairSelectedB row pair &&
            decide (index.val = varIndex pair.1 pair.2)) := by
  induction pairs generalizing result with
  | nil => simp
  | cons pair pairs induction =>
      rw [List.foldl_cons, induction]
      simp only [List.any_cons]
      unfold addPairBit
      by_cases hselected : pairSelectedB row pair = true
      · simp [hselected, Bool.or_assoc]
      · have hselectedFalse := Bool.eq_false_of_not_eq_true hselected
        simp [hselectedFalse]

private theorem varIndex_injective
    {first second first' second' : Vertex}
    (hequal : varIndex first second = varIndex first' second') :
    first = first' ∧ second = second' := by
  unfold varIndex at hequal
  apply And.intro <;> apply Fin.ext <;> omega

private theorem rowPairMask_bit
    (row : UInt64) (first second : Vertex)
    (hpair : (first, second) ∈ vertexPairTuples) :
    bitSetB (rowPairMask row) (varIndex first second) =
      pairSelectedB row (first, second) := by
  let index : Fin 64 := ⟨varIndex first second, varIndex_lt first second⟩
  have hfold := bitSetB_foldPairBits row vertexPairTuples 0 index
  simp only [index, bitSetB_zero_pair, Bool.false_or] at hfold
  change bitSetB (vertexPairTuples.foldl (addPairBit row) 0)
    (varIndex first second) = pairSelectedB row (first, second)
  rw [hfold]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hany
    obtain ⟨pair, _hmember, hselected⟩ := List.any_eq_true.mp hany
    have hparts : pairSelectedB row pair = true ∧
        decide (varIndex first second = varIndex pair.1 pair.2) = true := by
      simpa only [Bool.and_eq_true] using hselected
    rcases pair with ⟨first', second'⟩
    have hequal := of_decide_eq_true hparts.2
    obtain ⟨hfirst, hsecond⟩ := varIndex_injective hequal.symm
    change first' = first at hfirst
    change second' = second at hsecond
    subst first'
    subst second'
    exact hparts.1
  · intro hselected
    exact List.any_eq_true.mpr
      ⟨(first, second), hpair, by simp [hselected]⟩

private theorem rowPairMask_support
    (row : UInt64) (index : Fin 64)
    (hbit : bitSetB (rowPairMask row) index.val = true) :
    ∃ first second, (first, second) ∈ vertexPairTuples ∧
      index.val = varIndex first second := by
  have hfold := bitSetB_foldPairBits row vertexPairTuples 0 index
  simp only [bitSetB_zero, Bool.false_or] at hfold
  change bitSetB (vertexPairTuples.foldl (addPairBit row) 0) index.val = true at hbit
  rw [hfold] at hbit
  obtain ⟨pair, hmember, hselected⟩ := List.any_eq_true.mp hbit
  have hparts : pairSelectedB row pair = true ∧
      decide (index.val = varIndex pair.1 pair.2) = true := by
    simpa only [Bool.and_eq_true] using hselected
  exact ⟨pair.1, pair.2, hmember, of_decide_eq_true hparts.2⟩

/-- A packed pair state exactly records whether each vertex pair has occurred once or twice. -/
def PairState.Exact
    (state : PairState) (assignments : List RowAssignment) : Prop :=
  ∀ first second, (first, second) ∈ vertexPairTuples →
    bitSetB state.seenOnce (varIndex first second) =
        decide (1 ≤ pairCount assignments first second) ∧
      bitSetB state.seenTwice (varIndex first second) =
        decide (2 ≤ pairCount assignments first second)

private theorem pairCount_cons
    (assignments : List RowAssignment) (centre first second : Vertex)
    (row : UInt64) :
    pairCount ((centre, row) :: assignments) first second =
      if pairSelectedB row (first, second) then
        pairCount assignments first second + 1
      else pairCount assignments first second := by
  unfold pairCount pairSelectedB
  cases hfirst : bitSetB row first.val <;>
    cases hsecond : bitSetB row second.val <;>
    simp [hfirst, hsecond]

/-- The empty packed pair state exactly represents the empty assignment list. -/
theorem PairState.empty_exact : PairState.empty.Exact [] := by
  intro first second _hpair
  simp [PairState.empty, pairCount, bitSetB_zero_pair]

/-- Adding an audited row mask preserves exact packed pair counts. -/
theorem PairState.Exact.add
    {state : PairState} {assignments : List RowAssignment}
    (hexact : state.Exact assignments)
    (centre : Vertex) (row pairMask : UInt64)
    (hmask : pairMask = rowPairMask row) :
    (state.add pairMask).Exact ((centre, row) :: assignments) := by
  subst pairMask
  intro first second hpair
  have hold := hexact first second hpair
  have hrow := rowPairMask_bit row first second hpair
  simp only [PairState.add, bitSetB_or_pair, bitSetB_and_pair, hold.1, hold.2,
    hrow, pairCount_cons]
  cases hselected : pairSelectedB row (first, second) with
  | false => simp
  | true =>
      simp only [if_true, Bool.or_true]
      constructor
      · simp
      · apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
        omega

/-- Exact pair states are invariant under reordering the semantic assignment list. -/
theorem PairState.Exact.perm
    {state : PairState} {assignments assignments' : List RowAssignment}
    (hexact : state.Exact assignments) (hperm : assignments.Perm assignments') :
    state.Exact assignments' := by
  intro first second hpair
  have hcount : pairCount assignments first second =
      pairCount assignments' first second := by
    unfold pairCount
    have hfiltered := hperm.filter fun previous : RowAssignment =>
      bitSetB previous.2 first.val && bitSetB previous.2 second.val
    exact hfiltered.length_eq
  have hold := hexact first second hpair
  constructor
  · rw [hold.1, hcount]
  · rw [hold.2, hcount]

private theorem uint64_eq_zero_of_bits
    (value : UInt64)
    (hbits : ∀ index : Fin 64, bitSetB value index.val = false) :
    value = 0 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getElem_eq
  intro index hindex
  let indexFin : Fin 64 := ⟨index, hindex⟩
  rw [← BitVec.getLsbD_eq_getElem hindex,
    ← bitSetB_eq_getLsbD value indexFin, hbits indexFin]
  simp

private theorem vertexPairTuples_mem_vertexPairs
    {first second : Vertex} (hpair : (first, second) ∈ vertexPairTuples) :
    [first, second] ∈ vertexPairs := by
  revert first second
  decide

/-- Exact packed pair state makes its constant-time guard complete for a compatible row. -/
theorem PairState.compatible_of_exact
    {state : PairState} {assignments : List RowAssignment} {row pairMask : UInt64}
    (hexact : state.Exact assignments)
    (hmask : pairMask = rowPairMask row)
    (hcompatible : pairCompatibleB assignments row = true) :
    state.compatible pairMask = true := by
  subst pairMask
  have hzero : state.seenTwice &&& rowPairMask row = 0 := by
    apply uint64_eq_zero_of_bits
    intro index
    rw [bitSetB_and]
    by_cases hrowBit : bitSetB (rowPairMask row) index.val = true
    · obtain ⟨first, second, hpair, hindex⟩ :=
        rowPairMask_support row index hrowBit
      have hrowPair : pairSelectedB row (first, second) = true := by
        rw [← rowPairMask_bit row first second hpair, ← hindex]
        exact hrowBit
      have hguard := (List.all_eq_true.mp hcompatible) [first, second]
        (vertexPairTuples_mem_vertexPairs hpair)
      have hrowParts : bitSetB row first.val = true ∧
          bitSetB row second.val = true := by
        simpa only [pairSelectedB, Bool.and_eq_true] using hrowPair
      have hless : pairCount assignments first second < 2 := by
        simp [hrowParts.1, hrowParts.2] at hguard
        omega
      have htwice := (hexact first second hpair).2
      have hstateBit : bitSetB state.seenTwice index.val = false := by
        rw [hindex, htwice]
        simp [show ¬2 ≤ pairCount assignments first second by omega]
      simp [hstateBit, hrowBit]
    · have hrowFalse := Bool.eq_false_of_not_eq_true hrowBit
      simp [hrowFalse]
  simp [PairState.compatible, hzero]

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
