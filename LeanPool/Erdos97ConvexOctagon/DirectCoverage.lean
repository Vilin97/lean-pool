/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.PairCompatibility

/-! # Direct finite coverage checker -/

namespace Erdos97Octagon.RawIncidence

private abbrev CandidateBuckets (α : Type) := List (List (List α))
private abbrev PatternCandidates := CandidateBuckets PatternEntry
private abbrev HardCandidates := CandidateBuckets HardEntry
private abbrev RowAssignment := Vertex × UInt64

private def CandidateMember (entry : α) (candidates : CandidateBuckets α) : Prop :=
  ∃ group ∈ candidates, ∃ bucket ∈ group, entry ∈ bucket

private def patternCandidates : PatternCandidates :=
  patternBucketGroups.toList.map Array.toList

private def hardCandidates : HardCandidates :=
  hardBucketGroups.toList.map Array.toList

/-- The 35 four-element rows avoiding each possible centre, as eight-bit masks. -/
def rowMaskOptions : Vertex → List UInt64 := ![
  [30, 46, 78, 142, 54, 86, 150, 102, 166, 198, 58, 90, 154, 106, 170, 202, 114, 178,
    210, 226, 60, 92, 156, 108, 172, 204, 116, 180, 212, 228, 120, 184, 216, 232, 240],
  [29, 45, 77, 141, 53, 85, 149, 101, 165, 197, 57, 89, 153, 105, 169, 201, 113, 177,
    209, 225, 60, 92, 156, 108, 172, 204, 116, 180, 212, 228, 120, 184, 216, 232, 240],
  [27, 43, 75, 139, 51, 83, 147, 99, 163, 195, 57, 89, 153, 105, 169, 201, 113, 177,
    209, 225, 58, 90, 154, 106, 170, 202, 114, 178, 210, 226, 120, 184, 216, 232, 240],
  [23, 39, 71, 135, 51, 83, 147, 99, 163, 195, 53, 85, 149, 101, 165, 197, 113, 177,
    209, 225, 54, 86, 150, 102, 166, 198, 114, 178, 210, 226, 116, 180, 212, 228, 240],
  [15, 39, 71, 135, 43, 75, 139, 99, 163, 195, 45, 77, 141, 101, 165, 197, 105, 169,
    201, 225, 46, 78, 142, 102, 166, 198, 106, 170, 202, 226, 108, 172, 204, 228, 232],
  [15, 23, 71, 135, 27, 75, 139, 83, 147, 195, 29, 77, 141, 85, 149, 197, 89, 153,
    201, 209, 30, 78, 142, 86, 150, 198, 90, 154, 202, 210, 92, 156, 204, 212, 216],
  [15, 23, 39, 135, 27, 43, 139, 51, 147, 163, 29, 45, 141, 53, 149, 165, 57, 153,
    169, 177, 30, 46, 142, 54, 150, 166, 58, 154, 170, 178, 60, 156, 172, 180, 184],
  [15, 23, 39, 71, 27, 43, 75, 51, 83, 99, 29, 45, 77, 53, 85, 101, 57, 89, 105, 113,
    30, 46, 78, 54, 86, 102, 58, 90, 106, 114, 60, 92, 108, 116, 120]
]

private theorem rowMaskOptions_complete (centre : Vertex) :
    (rowOptions centre).reverse = (rowMaskOptions centre).map packedRow := by
  fin_cases centre <;> decide

private theorem exists_rowMask (Q : OctagonIncidence) (centre : Vertex) :
    ∃ row ∈ rowMaskOptions centre, Q.targets centre = packedRow row := by
  have hrow : Q.targets centre ∈ (rowOptions centre).reverse := by
    simpa using target_row_mem_rowOptions Q centre
  rw [rowMaskOptions_complete, List.mem_map] at hrow
  obtain ⟨row, hmember, hrow⟩ := hrow
  exact ⟨row, hmember, hrow.symm⟩

private def patternMatchesRowB
    (centre : Vertex) (row : UInt64) (entry : PatternEntry) : Bool :=
  (List.finRange 8).all fun target =>
    !bitSetB entry.mask (varIndex centre target) || bitSetB row target.val

private def hardMatchesRowB
    (centre : Vertex) (row : UInt64) (entry : HardEntry) : Bool :=
  (List.finRange 8).all fun target =>
    bitSetB entry.code (varIndex centre target) == bitSetB row target.val

private def filterPatterns
    (patterns : PatternCandidates) (centre : Vertex) (row : UInt64) :
    PatternCandidates :=
  patterns.map fun group => group.map fun bucket =>
    bucket.filter (patternMatchesRowB centre row)

private def filterHardEntries
    (hardEntries : HardCandidates) (centre : Vertex) (row : UInt64) :
    HardCandidates :=
  hardEntries.map fun group => group.map fun bucket =>
    bucket.filter (hardMatchesRowB centre row)

private theorem patternMatchesRowB_sound
    {centre : Vertex} {row : UInt64} {entry : PatternEntry}
    (hmatch : patternMatchesRowB centre row entry = true) :
    packedIncidence entry.mask centre ⊆ packedRow row := by
  intro target htarget
  rw [mem_packedIncidence] at htarget
  rw [mem_packedRow]
  have hbit := (List.all_eq_true.mp hmatch) target (List.mem_finRange target)
  simp only [Bool.or_eq_true] at hbit
  rcases hbit with hnot | hselected
  · have hselectedMask :
        bitSetB entry.mask (varIndex centre target) = true := by
      simpa only [packedSelectsB] using htarget
    simp [hselectedMask] at hnot
  · exact hselected

private theorem hardMatchesRowB_sound
    {centre : Vertex} {row : UInt64} {entry : HardEntry}
    (hmatch : hardMatchesRowB centre row entry = true) :
    packedIncidence entry.code centre = packedRow row := by
  ext target
  rw [mem_packedIncidence, mem_packedRow]
  have hbit := (List.all_eq_true.mp hmatch) target (List.mem_finRange target)
  simpa [packedSelectsB] using hbit

private theorem candidateMember_filterPatterns
    {entry : PatternEntry} {patterns : PatternCandidates}
    {centre : Vertex} {row : UInt64}
    (hmember : CandidateMember entry (filterPatterns patterns centre row)) :
    CandidateMember entry patterns ∧ patternMatchesRowB centre row entry = true := by
  rcases hmember with ⟨group', hgroup', bucket', hbucket', hentry⟩
  rw [filterPatterns, List.mem_map] at hgroup'
  obtain ⟨group, hgroup, rfl⟩ := hgroup'
  rw [List.mem_map] at hbucket'
  obtain ⟨bucket, hbucket, rfl⟩ := hbucket'
  have hparts := List.mem_filter.mp hentry
  exact ⟨⟨group, hgroup, bucket, hbucket, hparts.1⟩, hparts.2⟩

private theorem candidateMember_filterHardEntries
    {entry : HardEntry} {hardEntries : HardCandidates}
    {centre : Vertex} {row : UInt64}
    (hmember : CandidateMember entry (filterHardEntries hardEntries centre row)) :
    CandidateMember entry hardEntries ∧ hardMatchesRowB centre row entry = true := by
  rcases hmember with ⟨group', hgroup', bucket', hbucket', hentry⟩
  rw [filterHardEntries, List.mem_map] at hgroup'
  obtain ⟨group, hgroup, rfl⟩ := hgroup'
  rw [List.mem_map] at hbucket'
  obtain ⟨bucket, hbucket, rfl⟩ := hbucket'
  have hparts := List.mem_filter.mp hentry
  exact ⟨⟨group, hgroup, bucket, hbucket, hparts.1⟩, hparts.2⟩

private def patternFinishedB
    (remaining : List Vertex) (entry : PatternEntry) : Bool :=
  entry.validB && remaining.all fun centre =>
    (List.finRange 8).all fun target =>
      !bitSetB entry.mask (varIndex centre target)

private theorem patternFinishedB_sound
    {remaining : List Vertex} {entry : PatternEntry}
    (hfinished : patternFinishedB remaining entry = true) :
    entry.validB = true ∧ ∀ centre ∈ remaining,
      packedIncidence entry.mask centre = ∅ := by
  simp only [patternFinishedB, Bool.and_eq_true] at hfinished
  refine ⟨hfinished.1, ?_⟩
  intro centre hcentre
  ext target
  rw [mem_packedIncidence]
  have hcentreBits := (List.all_eq_true.mp hfinished.2) centre hcentre
  have htargetBit := (List.all_eq_true.mp hcentreBits) target (List.mem_finRange target)
  simp only [Finset.notMem_empty, iff_false]
  simpa [packedSelectsB] using htargetBit

private def somePatternFinishedB
    (remaining : List Vertex) (patterns : PatternCandidates) : Bool :=
  patterns.any fun group => group.any fun bucket =>
    bucket.any (patternFinishedB remaining)

private theorem somePatternFinishedB_sound
    {remaining : List Vertex} {patterns : PatternCandidates}
    (hfinished : somePatternFinishedB remaining patterns = true) :
    ∃ entry, CandidateMember entry patterns ∧ entry.validB = true ∧
      ∀ centre ∈ remaining, packedIncidence entry.mask centre = ∅ := by
  simp only [somePatternFinishedB, List.any_eq_true] at hfinished
  rcases hfinished with ⟨group, hgroup, bucket, hbucket, entry, hentry, hfinished⟩
  have hsound := patternFinishedB_sound hfinished
  exact ⟨entry, ⟨group, hgroup, bucket, hbucket, hentry⟩, hsound⟩

private def someValidHardEntryB (hardEntries : HardCandidates) : Bool :=
  hardEntries.any fun group => group.any fun bucket =>
    bucket.any fun entry => entry.validB

private theorem someValidHardEntryB_sound
    {hardEntries : HardCandidates} (hvalid : someValidHardEntryB hardEntries = true) :
    ∃ entry, CandidateMember entry hardEntries ∧ entry.validB = true := by
  simp only [someValidHardEntryB, List.any_eq_true] at hvalid
  rcases hvalid with ⟨group, hgroup, bucket, hbucket, entry, hentry, hvalid⟩
  exact ⟨entry, ⟨group, hgroup, bucket, hbucket, hentry⟩, hvalid⟩

private def AssignmentsMatch
    (Q : OctagonIncidence) (assignments : List RowAssignment) : Prop :=
  ∀ centre row, (centre, row) ∈ assignments → Q.targets centre = packedRow row

private def PatternCandidatesMatch
    (assignments : List RowAssignment) (patterns : PatternCandidates) : Prop :=
  ∀ entry, CandidateMember entry patterns → ∀ centre row,
    (centre, row) ∈ assignments →
      packedIncidence entry.mask centre ⊆ packedRow row

private def HardCandidatesMatch
    (assignments : List RowAssignment) (hardEntries : HardCandidates) : Prop :=
  ∀ entry, CandidateMember entry hardEntries → ∀ centre row,
    (centre, row) ∈ assignments →
      packedIncidence entry.code centre = packedRow row

private theorem PatternCandidatesMatch.filter
    {assignments : List RowAssignment} {patterns : PatternCandidates}
    (hmatch : PatternCandidatesMatch assignments patterns)
    (centre : Vertex) (row : UInt64) :
    PatternCandidatesMatch (assignments ++ [(centre, row)])
      (filterPatterns patterns centre row) := by
  intro entry hentry centre' row' hassignment
  have hparts := candidateMember_filterPatterns hentry
  rw [List.mem_append] at hassignment
  rcases hassignment with hprevious | hnew
  · exact hmatch entry hparts.1 centre' row' hprevious
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact patternMatchesRowB_sound hparts.2

private theorem HardCandidatesMatch.filter
    {assignments : List RowAssignment} {hardEntries : HardCandidates}
    (hmatch : HardCandidatesMatch assignments hardEntries)
    (centre : Vertex) (row : UInt64) :
    HardCandidatesMatch (assignments ++ [(centre, row)])
      (filterHardEntries hardEntries centre row) := by
  intro entry hentry centre' row' hassignment
  have hparts := candidateMember_filterHardEntries hentry
  rw [List.mem_append] at hassignment
  rcases hassignment with hprevious | hnew
  · exact hmatch entry hparts.1 centre' row' hprevious
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact hardMatchesRowB_sound hparts.2

private theorem AssignmentsMatch.append
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hmatch : AssignmentsMatch Q assignments)
    (centre : Vertex) (row : UInt64)
    (hrow : Q.targets centre = packedRow row) :
    AssignmentsMatch Q (assignments ++ [(centre, row)]) := by
  intro centre' row' hassignment
  rw [List.mem_append] at hassignment
  rcases hassignment with hprevious | hnew
  · exact hmatch centre' row' hprevious
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact hrow

private theorem impossible_of_finished_pattern
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {remaining : List Vertex} {assignments : List RowAssignment}
    {patterns : PatternCandidates}
    (hcentres : assignments.map Prod.fst ++ remaining = List.finRange 8)
    (hassignments : AssignmentsMatch Q assignments)
    (hpatterns : PatternCandidatesMatch assignments patterns)
    (hfinished : somePatternFinishedB remaining patterns = true) : False := by
  obtain ⟨entry, hentry, hvalidB, hempty⟩ := somePatternFinishedB_sound hfinished
  have hvalid := PatternEntry.valid_of_validB hvalidB
  have hextends : Extends (packedIncidence entry.mask) Q.targets := by
    intro centre target hselected
    have hcentre : centre ∈ assignments.map Prod.fst ++ remaining := by
      rw [hcentres]
      exact List.mem_finRange centre
    rw [List.mem_append] at hcentre
    rcases hcentre with hassigned | hremaining
    · rw [List.mem_map] at hassigned
      obtain ⟨assignment, hassignment, hcentre⟩ := hassigned
      rcases assignment with ⟨centre', row⟩
      simp only at hcentre
      subst centre'
      rw [hassignments centre row hassignment]
      exact hpatterns entry hentry centre row hassignment hselected
    · rw [hempty centre hremaining] at hselected
      simp at hselected
  exact Certificate.not_convex_realises entry.certificate.toCertificate
    (entry.certificate.valid_mono hextends hvalid) hC hR

private theorem impossible_of_valid_hard_entry
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {assignments : List RowAssignment} {hardEntries : HardCandidates}
    (hcentres : assignments.map Prod.fst = List.finRange 8)
    (hassignments : AssignmentsMatch Q assignments)
    (hhardEntries : HardCandidatesMatch assignments hardEntries)
    (hvalid : someValidHardEntryB hardEntries = true) : False := by
  obtain ⟨entry, hentry, hvalidB⟩ := someValidHardEntryB_sound hvalid
  have htargets : Q.targets = packedIncidence entry.code := by
    funext centre
    have hcentre : centre ∈ assignments.map Prod.fst := by
      rw [hcentres]
      exact List.mem_finRange centre
    rw [List.mem_map] at hcentre
    obtain ⟨assignment, hassignment, hcentre⟩ := hcentre
    rcases assignment with ⟨centre', row⟩
    simp only at hcentre
    subst centre'
    rw [hassignments centre row hassignment]
    exact (hhardEntries entry hentry centre row hassignment).symm
  have hcertificate : entry.certificate.Valid Q.targets := by
    rw [htargets]
    exact HardEntry.valid_of_validB hvalidB
  exact Certificate.not_convex_realises entry.certificate hcertificate hC hR

private theorem pairCompatibleB_sound
    (Q : OctagonIncidence) (hSparse : Q.PairSparse)
    {assignments : List RowAssignment} {centre : Vertex} {remaining : List Vertex}
    {row : UInt64}
    (hcentres : assignments.map Prod.fst ++ centre :: remaining = List.finRange 8)
    (hassignments : AssignmentsMatch Q assignments)
    (hrow : Q.targets centre = packedRow row) :
    pairCompatibleB assignments row = true :=
  pairCompatibleB_of_pairSparse_prefix Q hSparse assignments centre remaining row
    hcentres hassignments hrow

private def directSearch :
    List Vertex → List RowAssignment → PatternCandidates → HardCandidates → Bool
  | [], _assignments, patterns, hardEntries =>
      somePatternFinishedB [] patterns || someValidHardEntryB hardEntries
  | centre :: remaining, assignments, patterns, hardEntries =>
      somePatternFinishedB (centre :: remaining) patterns ||
        (rowMaskOptions centre).all fun row =>
          if pairCompatibleB assignments row then
            directSearch remaining (assignments ++ [(centre, row)])
              (filterPatterns patterns centre row)
              (filterHardEntries hardEntries centre row)
          else true

private theorem directSearch_sound
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q) (hSparse : Q.PairSparse)
    {remaining : List Vertex} {assignments : List RowAssignment}
    {patterns : PatternCandidates} {hardEntries : HardCandidates}
    (hcentres : assignments.map Prod.fst ++ remaining = List.finRange 8)
    (hassignments : AssignmentsMatch Q assignments)
    (hpatterns : PatternCandidatesMatch assignments patterns)
    (hhardEntries : HardCandidatesMatch assignments hardEntries)
    (haudit : directSearch remaining assignments patterns hardEntries = true) : False := by
  induction remaining generalizing assignments patterns hardEntries with
  | nil =>
      have hauditParts :
          somePatternFinishedB [] patterns = true ∨
            someValidHardEntryB hardEntries = true := by
        simpa only [directSearch, Bool.or_eq_true] using haudit
      rcases hauditParts with hfinished | hvalid
      · exact impossible_of_finished_pattern hC hR hcentres
          hassignments hpatterns hfinished
      · apply impossible_of_valid_hard_entry hC hR
        · simpa using hcentres
        · exact hassignments
        · exact hhardEntries
        · exact hvalid
  | cons centre remaining ih =>
      have hauditParts :
          somePatternFinishedB (centre :: remaining) patterns = true ∨
            (rowMaskOptions centre).all (fun row =>
              if pairCompatibleB assignments row then
                directSearch remaining (assignments ++ [(centre, row)])
                  (filterPatterns patterns centre row)
                  (filterHardEntries hardEntries centre row)
              else true) = true := by
        simpa only [directSearch, Bool.or_eq_true] using haudit
      rcases hauditParts with hfinished | hall
      · exact impossible_of_finished_pattern hC hR hcentres
          hassignments hpatterns hfinished
      · obtain ⟨row, hrowMember, hrow⟩ := exists_rowMask Q centre
        have hbranch := (List.all_eq_true.mp hall) row hrowMember
        have hcompatible := pairCompatibleB_sound Q hSparse hcentres hassignments hrow
        simp only [hcompatible, if_true] at hbranch
        have hnewCentres :
            (assignments ++ [(centre, row)]).map Prod.fst ++ remaining =
              List.finRange 8 := by
          simpa only [List.map_append, List.map_singleton, Prod.fst,
            List.append_assoc, List.singleton_append] using hcentres
        exact ih hnewCentres (hassignments.append centre row hrow)
          (hpatterns.filter centre row) (hhardEntries.filter centre row) hbranch

private def initialPatterns (orbit : Fin 7) : PatternCandidates :=
  filterPatterns (filterPatterns patternCandidates 0 30)
    1 (canonicalRowMask orbit)

private def initialHardEntries (orbit : Fin 7) : HardCandidates :=
  filterHardEntries (filterHardEntries hardCandidates 0 30)
    1 (canonicalRowMask orbit)

/-- Direct exhaustive audit of one canonical normalized incidence-table orbit. -/
def directCoverageOrbitB (orbit : Fin 7) : Bool :=
  directSearch [2, 3, 4, 5, 6, 7]
    [(0, 30), (1, canonicalRowMask orbit)]
    (initialPatterns orbit) (initialHardEntries orbit)

/-- Direct audit after fixing row two; used to split kernel computations. -/
def directCoverageBranchB (orbit : Fin 7) (rowTwo : Fin 35) : Bool :=
  let row := rowTwoMask rowTwo
  if pairCompatibleB [(0, 30), (1, canonicalRowMask orbit)] row then
    directSearch [3, 4, 5, 6, 7]
      [(0, 30), (1, canonicalRowMask orbit), (2, row)]
      (filterPatterns (initialPatterns orbit) 2 row)
      (filterHardEntries (initialHardEntries orbit) 2 row)
  else true

private theorem standardTargets_eq_packedRow :
    standardTargets = packedRow 30 := by
  ext target
  fin_cases target <;> decide

/-- Soundness of the split direct audit for a canonical normalized branch. -/
theorem canonicalBranch_impossible_of_directCoverage
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse)
    (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (haudit : ∀ rowTwo : Fin 35, directCoverageBranchB orbit rowTwo = true) : False := by
  obtain ⟨rowTwo, hrowTwo⟩ := exists_rowTwoIndex Q
  let row := rowTwoMask rowTwo
  have hrowZero : Q.targets 0 = packedRow 30 := by
    exact hN.trans standardTargets_eq_packedRow
  have hassignmentsZero : AssignmentsMatch Q [] := by
    intro centre mask hmember
    simp at hmember
  have hassignmentsOne :
      AssignmentsMatch Q [(0, 30), (1, canonicalRowMask orbit)] := by
    simpa using (hassignmentsZero.append 0 30 hrowZero).append
      1 (canonicalRowMask orbit) hrowOne
  have hcentresOne :
      [(0, 30), (1, canonicalRowMask orbit)].map Prod.fst ++
          2 :: [3, 4, 5, 6, 7] = List.finRange 8 := by
    rfl
  have hcompatible :
      pairCompatibleB [(0, 30), (1, canonicalRowMask orbit)] row = true :=
    pairCompatibleB_sound Q hSparse hcentresOne hassignmentsOne hrowTwo
  have hbranch : directSearch [3, 4, 5, 6, 7]
      [(0, 30), (1, canonicalRowMask orbit), (2, row)]
      (filterPatterns (initialPatterns orbit) 2 row)
      (filterHardEntries (initialHardEntries orbit) 2 row) = true := by
    simpa only [directCoverageBranchB, row, hcompatible, if_true] using haudit rowTwo
  have hassignments : AssignmentsMatch Q
      [(0, 30), (1, canonicalRowMask orbit), (2, row)] := by
    simpa using hassignmentsOne.append 2 row hrowTwo
  have hpatternStart : PatternCandidatesMatch [] patternCandidates := by
    intro entry hentry centre mask hmember
    simp at hmember
  have hpatterns : PatternCandidatesMatch
      [(0, 30), (1, canonicalRowMask orbit), (2, row)]
      (filterPatterns (initialPatterns orbit) 2 row) := by
    simpa [initialPatterns] using
      (((hpatternStart.filter 0 30).filter 1 (canonicalRowMask orbit)).filter 2 row)
  have hhardStart : HardCandidatesMatch [] hardCandidates := by
    intro entry hentry centre mask hmember
    simp at hmember
  have hhardEntries : HardCandidatesMatch
      [(0, 30), (1, canonicalRowMask orbit), (2, row)]
      (filterHardEntries (initialHardEntries orbit) 2 row) := by
    simpa [initialHardEntries] using
      (((hhardStart.filter 0 30).filter 1 (canonicalRowMask orbit)).filter 2 row)
  have hcentres :
      [(0, 30), (1, canonicalRowMask orbit), (2, row)].map Prod.fst ++
          [3, 4, 5, 6, 7] = List.finRange 8 := by
    rfl
  exact directSearch_sound hC hR hSparse hcentres hassignments hpatterns
    hhardEntries hbranch

end Erdos97Octagon.RawIncidence
