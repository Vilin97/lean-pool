/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateChecker
import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoiceSoundness
import LeanPool.Erdos97ConvexOctagon.PairStateExactness

/-! # Support lemmas for compact coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- A conflict cover is sound when every rejected legal row contains one of
its required pair bits at its recorded centre. -/
def ConflictCover.Valid (cover : ConflictCover) : Prop :=
  ∃ hcentre : cover.centre < 8,
    ∀ rowIndex : Fin 35,
      bitSetB cover.incompatibleRows rowIndex.val = true →
        ((cover.requiredPairs &&&
          (searchRowChoiceAt ⟨cover.centre, hcentre⟩ rowIndex).pairMask) != 0) = true

/-- Decidable audit that every row masked by a cover contains a required pair. -/
def ConflictCover.validB (cover : ConflictCover) : Bool :=
  if _hcentre : cover.centre < 8 then
    (List.range 35).all fun rowIndex =>
      !bitSetB cover.incompatibleRows rowIndex ||
        ((cover.requiredPairs &&&
          ((searchRowChoices.getD cover.centre #[]).getD rowIndex
            ⟨0, 0⟩).pairMask) != 0)
  else false

/-- The finite cover audit implies semantic cover validity. -/
theorem ConflictCover.valid_of_validB
    {cover : ConflictCover} (hvalid : cover.validB = true) :
    cover.Valid := by
  unfold ConflictCover.validB at hvalid
  split at hvalid
  next hcentre =>
    refine ⟨hcentre, fun rowIndex hrow => ?_⟩
    have haudit := (List.all_eq_true.mp hvalid) rowIndex.val
      (List.mem_range.mpr rowIndex.isLt)
    rw [hrow] at haudit
    simpa only [Bool.not_true, Bool.false_or, searchRowChoiceAt] using haudit
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
