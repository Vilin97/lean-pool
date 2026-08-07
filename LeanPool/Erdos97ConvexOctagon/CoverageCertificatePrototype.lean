/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryValidity
import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoices
import LeanPool.Erdos97ConvexOctagon.StaticDirectCoverage

/-! # Prototype proof-carrying direct coverage checker -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- A compact DFS witness: exact hard leaf, or one directive for a nonleaf state. -/
inductive SearchWitness where
  /-- The generated hard-summary origin for a completed table. -/
  | leaf (hardOrigin : Nat)
  /-- Pattern-stop row bits, their origins, and recursive children in row order. -/
  | node (patternRows : UInt64) (patternOrigins : List Nat)
      (children : List SearchWitness)

/-- How a fixed canonical branch is discharged. -/
inductive BranchWitness where
  /-- A pattern already covers the first two rows. -/
  | prefixTwo (patternOrigin : Nat)
  /-- A pattern covers the first three rows. -/
  | prefixThree (patternOrigin : Nat)
  /-- The remaining five rows are checked by a compact DFS witness. -/
  | search (witness : SearchWitness)

/-- Retrieve the generated pattern summary having one source origin. -/
def patternSummaryForOrigin? (origin : Nat) : Option PatternSummary :=
  let group := patternSummaryBucketGroups.getD (origin % 256 / 8) #[]
  (group.getD (origin % 8) []).find? fun summary => summary.origin == origin

/-- Retrieve the generated hard summary having one source origin. -/
def hardSummaryForOrigin? (origin : Nat) : Option HardSummary :=
  let group := hardSummaryBucketGroups.getD (origin % 256 / 8) #[]
  (group.getD (origin % 8) []).find? fun summary => summary.origin == origin

/-- Every pattern returned by the canonical origin lookup is globally audited. -/
theorem patternSummaryForOrigin?_valid
    {origin : Nat} {summary : PatternSummary}
    (hlookup : patternSummaryForOrigin? origin = some summary) : summary.Valid := by
  let groupIndex := origin % 256 / 8
  have hgroupIndex : groupIndex < patternSummaryBucketGroups.size := by
    change origin % 256 / 8 < 32
    omega
  let group := patternSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ patternSummaryBucketGroups.toList :=
    Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : patternSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dif_pos hgroupIndex, Array.getInternal_eq_getElem,
      group]
  rw [patternSummaryForOrigin?, hgroupGetD] at hlookup
  by_cases hbucketIndex : origin % 8 < group.size
  · let bucket := group[origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList :=
      Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (origin % 8) [] = bucket := by
      simp only [Array.getD, dif_pos hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hlookup
    apply PatternSummary.valid_of_data
    exact ⟨group, hgroup, bucket, hbucket,
      List.mem_of_find?_eq_some hlookup⟩
  · simp [Array.getD, hbucketIndex] at hlookup

/-- Every exact summary returned by the canonical origin lookup is globally audited. -/
theorem hardSummaryForOrigin?_valid
    {origin : Nat} {summary : HardSummary}
    (hlookup : hardSummaryForOrigin? origin = some summary) : summary.Valid := by
  let groupIndex := origin % 256 / 8
  have hgroupIndex : groupIndex < hardSummaryBucketGroups.size := by
    change origin % 256 / 8 < 32
    omega
  let group := hardSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ hardSummaryBucketGroups.toList :=
    Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : hardSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dif_pos hgroupIndex, Array.getInternal_eq_getElem,
      group]
  rw [hardSummaryForOrigin?, hgroupGetD] at hlookup
  by_cases hbucketIndex : origin % 8 < group.size
  · let bucket := group[origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList :=
      Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (origin % 8) [] = bucket := by
      simp only [Array.getD, dif_pos hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hlookup
    apply HardSummary.valid_of_data
    exact ⟨group, hgroup, bucket, hbucket,
      List.mem_of_find?_eq_some hlookup⟩
  · simp [Array.getD, hbucketIndex] at hlookup

/-- Fail-closed validation of a pattern-origin witness at one partial table. -/
def patternOriginMatchesB
    (origin : Nat) (code : UInt64) (assignments : List RowAssignment) : Bool :=
  match patternSummaryForOrigin? origin with
  | none => false
  | some summary =>
      ((summary.mask &&& code) == summary.mask) &&
        patternExtendsAssignmentsB assignments summary

/-- Fail-closed validation of a hard-origin witness at one completed table. -/
def hardOriginMatchesB
    (origin : Nat) (code : UInt64) (assignments : List RowAssignment) : Bool :=
  match hardSummaryForOrigin? origin with
  | none => false
  | some summary =>
      (summary.code == code) &&
        hardEqualsAssignmentsB assignments summary

private structure WitnessCursor where
  ok : Bool
  patternOrigins : List Nat
  children : List SearchWitness

/-- Verify a compact witness while reconstructing every trusted packed DFS state. -/
def verifySearch :
    List Vertex → List RowAssignment → UInt64 → PairState → ColumnState →
      SearchWitness → Bool
  | [], assignments, code, _pairState, _columnState, .leaf origin =>
      hardOriginMatchesB origin code assignments
  | [], _assignments, _code, _pairState, _columnState, .node _ _ _ => false
  | _centre :: _remaining, _assignments, _code, _pairState, _columnState,
      .leaf _origin => false
  | centre :: remaining, assignments, code, pairState, columnState,
      .node patternRows patternOrigins children =>
      let choices := searchRowChoices.getD centre.val #[]
      let incompatible := incompatibleRowIndexMask centre pairState.seenTwice
      if (patternRows &&& 34359738367) != patternRows ||
          (patternRows &&& incompatible) != 0 then false
      else
        let initial : WitnessCursor := ⟨true, patternOrigins, children⟩
        let result := (compatibleRowIndices incompatible).foldl (fun cursor index =>
          if !cursor.ok then cursor
          else
            let choice := choices.getD index ⟨0, 0⟩
            let row := choice.rowMask
            let nextAssignments := (centre, row) :: assignments
            let nextCode := addRowCode code row centre
            let nextPairState := pairState.add choice.pairMask
            let nextColumnState := columnState.add row
            if nextColumnState.feasible remaining then
              if bitSetB patternRows index then
                match cursor.patternOrigins with
                | [] => ⟨false, [], cursor.children⟩
                | origin :: origins =>
                    ⟨patternOriginMatchesB origin nextCode nextAssignments,
                      origins, cursor.children⟩
              else
                match cursor.children with
                | [] => ⟨false, cursor.patternOrigins, []⟩
                | child :: rest =>
                    ⟨verifySearch remaining nextAssignments nextCode nextPairState
                        nextColumnState child,
                      cursor.patternOrigins, rest⟩
            else if bitSetB patternRows index then
              ⟨false, cursor.patternOrigins, cursor.children⟩
            else cursor) initial
        result.ok && result.patternOrigins.isEmpty && result.children.isEmpty

/-- Verify one canonical fixed-row branch against a deterministic witness. -/
def verifyBranch
    (orbit : Fin 7) (rowTwo : Fin 35) (witness : BranchWitness) : Bool :=
  let assignments := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  match witness with
  | .prefixTwo origin => patternOriginMatchesB origin code assignments
  | .prefixThree origin =>
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
      let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
      let row := rowTwoMask rowTwo
      let choice2 := searchChoiceForRow 2 row
      if pairState.compatible choice2.pairMask then
        let nextAssignments := (2, row) :: assignments
        let nextCode := addRowCode code row 2
        let nextColumnState := columnState.add row
        if nextColumnState.feasible searchCentres then
          patternOriginMatchesB origin nextCode nextAssignments
        else false
      else false
  | .search searchWitness =>
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
      let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
      let row := rowTwoMask rowTwo
      let choice2 := searchChoiceForRow 2 row
      if pairState.compatible choice2.pairMask then
        let nextAssignments := (2, row) :: assignments
        let nextCode := addRowCode code row 2
        let nextPairState := pairState.add choice2.pairMask
        let nextColumnState := columnState.add row
        if nextColumnState.feasible searchCentres then
          verifySearch searchCentres nextAssignments nextCode nextPairState
            nextColumnState searchWitness
        else false
      else false

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
