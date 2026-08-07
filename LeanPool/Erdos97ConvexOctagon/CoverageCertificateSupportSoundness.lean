/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateChecker
import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMaskSoundness
import LeanPool.Erdos97ConvexOctagon.PairStateExactness

/-! # Support lemmas for compact coverage certificates -/

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

/-- Bit testing reflects bitwise disjunction. -/
theorem bitSetB_or
    (left right : UInt64) (index : Fin 64) :
    bitSetB (left ||| right) index.val =
      (bitSetB left index.val || bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

/-- Bit testing reflects bitwise conjunction. -/
theorem bitSetB_and
    (left right : UInt64) (index : Fin 64) :
    bitSetB (left &&& right) index.val =
      (bitSetB left index.val && bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

private theorem bitSetB_zero (index : Fin 64) :
    bitSetB 0 index.val = false := by
  simp only [bitSetB_eq_getLsbD]
  simp

private theorem fiveBitIndices_spec (word : Fin 32) :
    fiveBitIndices.getD word.val [] =
      (List.range 5).filter fun index => word.val.testBit index := by
  fin_cases word <;> decide

private theorem rowWord_lt (rows : UInt64) (offset : Nat) :
    (((rows >>> UInt64.ofNat offset) &&& 31).toNat) < 32 := by
  calc
    (((rows >>> UInt64.ofNat offset) &&& 31).toNat) =
        (((rows >>> UInt64.ofNat offset) &&& 31).toBitVec).toNat := rfl
    _ = (rows >>> UInt64.ofNat offset).toBitVec.toNat &&& 31 := by
      rw [UInt64.toBitVec_and, BitVec.toNat_and]
      rfl
    _ ≤ 31 := Nat.and_le_right
    _ < 32 := by omega

private theorem rowWord_testBit
    (rows : UInt64) (offset : Nat) (hoffset : offset + 5 ≤ 64)
    (index : Fin 5) :
    (((rows >>> UInt64.ofNat offset) &&& 31).toNat).testBit index.val =
      bitSetB rows (offset + index.val) := by
  let observed : Fin 64 := ⟨offset + index.val, by omega⟩
  change (((rows >>> UInt64.ofNat offset) &&& 31).toBitVec.toNat).testBit
      index.val = bitSetB rows observed.val
  rw [BitVec.testBit_toNat, bitSetB_eq_getLsbD]
  simp only [UInt64.toBitVec_and, BitVec.getLsbD_and,
    UInt64.toBitVec_shiftRight]
  change ((rows.toBitVec >>>
      ((UInt64.ofNat offset).toBitVec % 64).toNat).getLsbD index.val &&
        (31 : UInt64).toBitVec.getLsbD index.val) =
      rows.toBitVec.getLsbD observed.val
  have hshift : ((UInt64.ofNat offset).toBitVec % 64).toNat = offset := by
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : offset < 64)]
  rw [hshift, BitVec.getLsbD_ushiftRight]
  have hmask : (31 : UInt64).toBitVec.getLsbD index.val = true := by
    rw [UInt64.toBitVec_ofNat, BitVec.getLsbD_ofNat]
    change (decide (index.val < 64) &&
        Nat.testBit (2 ^ 5 - 1) index.val) = true
    rw [Nat.testBit_two_pow_sub_one]
    simp [index.isLt, show index.val < 64 by omega]
  rw [hmask, Bool.and_true]

/-- One compact five-bit word enumerates exactly its set row indices. -/
theorem rowIndexWord_eq_filter
    (rows : UInt64) (offset : Nat) (hoffset : offset + 5 ≤ 64) :
    rowIndexWord rows offset =
      ((List.range 5).filter fun index =>
        bitSetB rows (offset + index)).map fun index => offset + index := by
  let word : Fin 32 :=
    ⟨((rows >>> UInt64.ofNat offset) &&& 31).toNat, rowWord_lt rows offset⟩
  unfold rowIndexWord
  change (fiveBitIndices.getD word.val []).map (fun index => offset + index) = _
  rw [fiveBitIndices_spec]
  congr 1
  apply List.filter_congr
  intro index hindex
  have hindexBound : index < 5 := List.mem_range.mp hindex
  let boundedIndex : Fin 5 := ⟨index, hindexBound⟩
  simpa only [word, boundedIndex] using
    rowWord_testBit rows offset hoffset boundedIndex

/-- Every set legal-row bit occurs in its unique compact five-row word. -/
theorem rowIndex_mem_word_of_bit
    (rows : UInt64) (index : Fin 35)
    (hbit : bitSetB rows index.val = true) :
    index.val ∈ rowIndexWord rows (5 * (index.val / 5)) := by
  have hmod : index.val % 5 < 5 := Nat.mod_lt _ (by omega)
  have hdecompose : 5 * (index.val / 5) + index.val % 5 = index.val := by
    have := Nat.mod_add_div index.val 5
    omega
  rw [rowIndexWord_eq_filter _ _ (by omega)]
  apply List.mem_map.mpr
  refine ⟨index.val % 5, ?_, hdecompose⟩
  rw [List.mem_filter]
  exact ⟨List.mem_range.mpr hmod, by simpa [hdecompose] using hbit⟩

/-- The compact word containing a legal-row index is one of the seven checked words. -/
theorem rowIndex_wordIndex_mem_range (index : Fin 35) :
    index.val / 5 ∈ List.range 7 := by
  rw [List.mem_range]
  omega

/-- The low-35-bit legal-row mask contains every legal row index. -/
theorem legalRows_bit (index : Fin 35) :
    bitSetB 34359738367 index.val = true := by
  fin_cases index <;> decide

/-- A complete row partition puts every cover-compatible legal row in either
the active or semantically rejected mask. -/
theorem active_or_rejected_of_partition
    {active rejected incompatible : UInt64} (index : Fin 35)
    (hpartition : active ||| (rejected ||| incompatible) = 34359738367)
    (hcompatible : bitSetB incompatible index.val = false) :
    bitSetB active index.val = true ∨ bitSetB rejected index.val = true := by
  let boundedIndex : Fin 64 := ⟨index.val, by omega⟩
  have hbits := congrArg (fun rows => bitSetB rows boundedIndex.val) hpartition
  rw [bitSetB_or, bitSetB_or, legalRows_bit index, hcompatible] at hbits
  simpa only [Bool.or_false, Bool.or_eq_true] using hbits

/-- A conflict cover is sound when every rejected legal row contains one of
its required pair bits at its recorded centre. -/
def ConflictCover.Valid (cover : ConflictCover) : Prop :=
  ∃ hcentre : cover.centre < 8,
    ∀ rowIndex : Fin 35,
      bitSetB cover.incompatibleRows rowIndex.val = true →
        ((cover.requiredPairs &&&
          (searchRowChoiceAt ⟨cover.centre, hcentre⟩ rowIndex).pairMask) != 0) = true

private theorem foldPairMasks_bit_aux
    (masks : Array UInt64) (indices : List Nat) (rows : UInt64)
    (rowIndex : Fin 64) :
    bitSetB (indices.foldl (fun accumulated index =>
        accumulated ||| masks.getD index 0) rows) rowIndex.val = true →
      bitSetB rows rowIndex.val = true ∨
        ∃ index ∈ indices,
          bitSetB (masks.getD index 0) rowIndex.val = true := by
  induction indices generalizing rows with
  | nil => simp
  | cons index indices hinduction =>
      intro hbit
      have hresult := hinduction
        (rows := rows ||| masks.getD index 0) hbit
      rcases hresult with hcurrent | ⟨witness, hwitness, hset⟩
      · rw [bitSetB_or, Bool.or_eq_true] at hcurrent
        rcases hcurrent with hrows | hindex
        · exact Or.inl hrows
        · exact Or.inr ⟨index, by simp, hindex⟩
      · exact Or.inr ⟨witness, by simp [hwitness], hset⟩

private theorem foldPairMasks_bit
    (masks : Array UInt64) (indices : List Nat) (rowIndex : Fin 64)
    (hbit : bitSetB (indices.foldl (fun rows index =>
      rows ||| masks.getD index 0) 0) rowIndex.val = true) :
    ∃ index ∈ indices,
      bitSetB (masks.getD index 0) rowIndex.val = true := by
  rcases foldPairMasks_bit_aux masks indices 0 rowIndex hbit with
    hzero | hwitness
  · rw [bitSetB_zero] at hzero
    simp at hzero
  · exact hwitness

/-- The finite cover audit implies semantic cover validity. -/
theorem ConflictCover.valid_of_validB
    {cover : ConflictCover} (hvalid : cover.validB = true) :
    cover.Valid := by
  unfold ConflictCover.validB at hvalid
  split at hvalid
  next hcentre =>
    let masks := pairRowIndexMasks.getD cover.centre #[]
    have hparts :
        cover.pairIndices.all (fun index =>
            index < 64 && bitSetB cover.requiredPairs index) = true ∧
          cover.pairIndices.foldl (fun rows index =>
            rows ||| masks.getD index 0) 0 = cover.incompatibleRows := by
      simpa only [masks, Bool.and_eq_true, beq_iff_eq] using hvalid
    refine ⟨hcentre, fun rowIndex hrow => ?_⟩
    let boundedRow : Fin 64 := ⟨rowIndex.val, by omega⟩
    have hfoldBit : bitSetB (cover.pairIndices.foldl (fun rows index =>
        rows ||| masks.getD index 0) 0) boundedRow.val = true := by
      rw [hparts.2]
      exact hrow
    obtain ⟨pairIndex, hpairMember, hmaskBit⟩ :=
      foldPairMasks_bit masks cover.pairIndices boundedRow hfoldBit
    have hpairAudit := (List.all_eq_true.mp hparts.1) pairIndex hpairMember
    have hpairParts : pairIndex < 64 ∧
        bitSetB cover.requiredPairs pairIndex = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hpairAudit
    let boundedPair : Fin 64 := ⟨pairIndex, hpairParts.1⟩
    have hrowPair : bitSetB
        (searchRowChoiceAt ⟨cover.centre, hcentre⟩ rowIndex).pairMask
        boundedPair.val = true := by
      rw [← pairRowIndexMasks_bit ⟨cover.centre, hcentre⟩ boundedPair rowIndex]
      exact hmaskBit
    apply bne_iff_ne.mpr
    intro hintersection
    have hzero := congrArg (fun bits => bitSetB bits boundedPair.val) hintersection
    rw [bitSetB_and, hpairParts.2, hrowPair, bitSetB_zero] at hzero
    simp at hzero
  next => simp at hvalid

/-- A table-wide audit makes every successful canonical cover lookup valid. -/
theorem conflictCoverAt?_valid_of_audit
    {identifier : Nat} {cover : ConflictCover}
    (haudit : ∀ group ∈ conflictCoverGroups, ∀ entry ∈ group,
      entry.validB = true)
    (hlookup : conflictCoverAt? identifier = some cover) : cover.Valid := by
  unfold conflictCoverAt? at hlookup
  generalize hgroupLookup : conflictCoverGroups[identifier / 64]? = groupOption
    at hlookup
  cases groupOption with
  | none => simp at hlookup
  | some group =>
      have hgroupMember : group ∈ conflictCoverGroups :=
        Array.mem_of_getElem? hgroupLookup
      have hcoverMember : cover ∈ group := Array.mem_of_getElem? hlookup
      exact ConflictCover.valid_of_validB
        (haudit group hgroupMember cover hcoverMember)

/-- A required-pair submask is disjoint from every row accepted by the packed
pair-state guard. -/
theorem requiredPairs_disjoint
    {state : PairState} {requiredPairs rowPairs : UInt64}
    (hrequired : requiredPairs &&& state.seenTwice = requiredPairs)
    (hcompatible : state.compatible rowPairs = true) :
    requiredPairs &&& rowPairs = 0 := by
  have hstateDisjoint : state.seenTwice &&& rowPairs = 0 := by
    simpa only [PairState.compatible, beq_iff_eq] using hcompatible
  calc
    requiredPairs &&& rowPairs =
        (requiredPairs &&& state.seenTwice) &&& rowPairs := by rw [hrequired]
    _ = requiredPairs &&& (state.seenTwice &&& rowPairs) :=
      UInt64.and_assoc _ _ _
    _ = 0 := by rw [hstateDisjoint]; simp

/-- A submask of the repeated pairs in an exact state is disjoint from every
semantically compatible audited row. -/
theorem requiredPairs_disjoint_of_pairState_exact
    {state : PairState} {assignments : List RowAssignment}
    (hexact : state.Exact assignments) (centre : Vertex) (rowIndex : Fin 35)
    (requiredPairs : UInt64)
    (hrequired : requiredPairs &&& state.seenTwice = requiredPairs)
    (hcompatible : pairCompatibleB assignments
      (searchRowChoiceAt centre rowIndex).rowMask = true) :
    requiredPairs &&& (searchRowChoiceAt centre rowIndex).pairMask = 0 := by
  apply requiredPairs_disjoint hrequired
  exact state.compatible_of_exact hexact
    (searchRowChoiceAt_pairMask centre rowIndex) hcompatible

/-- An audited cover cannot mask a row accepted by the packed pair-state guard
when its required pairs passed the subset gate. -/
theorem ConflictCover.compatible_row_not_incompatible
    {cover : ConflictCover} (hvalid : cover.Valid) {state : PairState}
    (centre : Vertex) (rowIndex : Fin 35)
    (hcentre : cover.centre = centre.val)
    (hrequired : cover.requiredPairs &&& state.seenTwice = cover.requiredPairs)
    (hcompatible : state.compatible
      (searchRowChoiceAt centre rowIndex).pairMask = true) :
    bitSetB cover.incompatibleRows rowIndex.val = false := by
  obtain ⟨hcoverCentre, hcoverSound⟩ := hvalid
  let coverCentre : Vertex := ⟨cover.centre, hcoverCentre⟩
  have hcentreEqual : coverCentre = centre := Fin.ext hcentre
  subst centre
  have hdisjoint := requiredPairs_disjoint hrequired hcompatible
  apply Bool.eq_false_of_not_eq_true
  intro hrow
  have hintersection := hcoverSound rowIndex hrow
  rw [hdisjoint] at hintersection
  simp at hintersection

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
