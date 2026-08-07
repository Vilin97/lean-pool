/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoiceValidity
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryValidity
import LeanPool.Erdos97ConvexOctagon.StaticDirectCoverage

/-! # Soundness of the static direct coverage audit -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private def CandidateMember (candidate : α) (buckets : List (List α)) : Prop :=
  ∃ bucket ∈ buckets, candidate ∈ bucket

private def AssignmentsMatch
    (Q : OctagonIncidence) (assignments : List RowAssignment) : Prop :=
  ∀ centre row, (centre, row) ∈ assignments →
    Q.targets centre = packedRow row

private def PatternBucketsValid (patterns : PatternSummaryBuckets) : Prop :=
  ∀ summary, CandidateMember summary patterns → summary.Valid

private def HardBucketsValid (hardEntries : HardSummaryBuckets) : Prop :=
  ∀ summary, CandidateMember summary hardEntries → summary.Valid

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

private theorem pairCompatibleB_of_pairSparse_perm
    (Q : OctagonIncidence) (hSparse : Q.PairSparse)
    {assignments : List RowAssignment} {centre : Vertex}
    {remaining : List Vertex} {row : UInt64}
    (hcentres : (assignments.map Prod.fst ++ centre :: remaining).Perm
      (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hrow : Q.targets centre = packedRow row) :
    pairCompatibleB assignments row = true := by
  have hallCentres : (assignments.map Prod.fst ++ centre :: remaining).Nodup :=
    (List.Perm.nodup_iff hcentres).mpr (List.nodup_finRange 8)
  have hprocessed : (assignments.map Prod.fst).Nodup :=
    hallCentres.of_append_left
  have hcentreFresh : centre ∉ assignments.map Prod.fst := by
    intro hmember
    exact hallCentres.disjoint hmember (by simp)
  exact pairCompatibleB_of_pairSparse Q hSparse assignments centre row
    (List.nodup_cons.mpr ⟨hcentreFresh, hprocessed⟩) hassignments hrow

private theorem patternBucketsValid_of_audit
    {patterns : PatternSummaryBuckets}
    (haudit : patterns.all (fun bucket =>
      bucket.all PatternSummary.memberB) = true) : PatternBucketsValid patterns := by
  intro summary hmember
  obtain ⟨bucket, hbucket, hsummary⟩ := hmember
  have hbucketAudit := (List.all_eq_true.mp haudit) bucket hbucket
  exact PatternSummary.valid_of_memberB
    ((List.all_eq_true.mp hbucketAudit) summary hsummary)

private theorem hardBucketsValid_of_audit
    {hardEntries : HardSummaryBuckets}
    (haudit : hardEntries.all (fun bucket =>
      bucket.all HardSummary.memberB) = true) : HardBucketsValid hardEntries := by
  intro summary hmember
  obtain ⟨bucket, hbucket, hsummary⟩ := hmember
  have hbucketAudit := (List.all_eq_true.mp haudit) bucket hbucket
  exact HardSummary.valid_of_memberB
    ((List.all_eq_true.mp hbucketAudit) summary hsummary)

private theorem patternBucketsValid_of_choice
    {centre : Vertex} {choice : SummaryRowChoice}
    (hchoice : choice ∈ patternSummaryChoices.getD centre.val []) :
    PatternBucketsValid choice.patterns := by
  have hchoiceAudit :=
    (List.all_eq_true.mp (patternSummaryChoices_valid centre)) choice hchoice
  simp only [Bool.and_eq_true] at hchoiceAudit
  exact patternBucketsValid_of_audit hchoiceAudit.1

private theorem hardSummaries_valid (orbit : Fin 7) (rowTwo : Fin 35) :
    HardBucketsValid (hardSummaries orbit rowTwo) := by
  let choices := hardSummaryChoices.getD orbit.val #[]
  have hchoicesSize : choices.size = 35 := by
    fin_cases orbit <;> rfl
  have hindex : rowTwo.val < choices.size := by
    rw [hchoicesSize]
    exact rowTwo.isLt
  have hchoiceMember : choices[rowTwo.val] ∈ choices.toList :=
    Array.getElem_mem_toList hindex
  have hchoiceAudit :=
    (List.all_eq_true.mp (hardSummaryChoices_valid orbit))
      choices[rowTwo.val] hchoiceMember
  have hsummaries : hardSummaries orbit rowTwo = choices[rowTwo.val] := by
    change choices.getD rowTwo.val [] = choices[rowTwo.val]
    simp only [Array.getD, dif_pos hindex, Array.getInternal_eq_getElem]
  rw [hsummaries]
  exact hardBucketsValid_of_audit hchoiceAudit

private def rowChoiceAt (centre : Vertex) (index : Fin 35) : SummaryRowChoice :=
  (patternSummaryChoices.getD centre.val []).getD index.val ⟨0, 0, []⟩

private theorem patternSummaryChoices_length (centre : Vertex) :
    (patternSummaryChoices.getD centre.val []).length = 35 := by
  fin_cases centre <;> rfl

private theorem rowChoiceAt_mem (centre : Vertex) (index : Fin 35) :
    rowChoiceAt centre index ∈ patternSummaryChoices.getD centre.val [] := by
  have hindex : index.val < (patternSummaryChoices.getD centre.val []).length := by
    rw [patternSummaryChoices_length]
    exact index.isLt
  have hequal : rowChoiceAt centre index =
      (patternSummaryChoices.getD centre.val [])[index.val] := by
    simp only [rowChoiceAt, List.getD, List.getElem?_eq_getElem hindex,
      Option.getD_some]
  rw [hequal]
  exact List.getElem_mem hindex

private theorem rowChoices_complete (centre : Vertex) :
    (rowOptions centre).reverse =
      List.ofFn (fun index : Fin 35 =>
        packedRow (rowChoiceAt centre index).rowMask) := by
  fin_cases centre <;> decide

private theorem exists_rowChoiceIndex (Q : OctagonIncidence) (centre : Vertex) :
    ∃ index : Fin 35,
      Q.targets centre = packedRow (rowChoiceAt centre index).rowMask := by
  have hrow : Q.targets centre ∈ (rowOptions centre).reverse := by
    simpa using target_row_mem_rowOptions Q centre
  rw [rowChoices_complete, List.mem_ofFn] at hrow
  obtain ⟨index, hrow⟩ := hrow
  exact ⟨index, hrow.symm⟩

private theorem rowChoiceAt_two_mask (index : Fin 35) :
    (rowChoiceAt 2 index).rowMask = rowTwoMask index := by
  fin_cases index <;> rfl

private theorem findChoice_spec
    (choices : List SummaryRowChoice) (row : UInt64)
    (hexists : ∃ choice ∈ choices, choice.rowMask = row) :
    let choice := (choices.find? (fun candidate => candidate.rowMask == row)).getD
      ⟨0, 0, []⟩
    choice ∈ choices ∧ choice.rowMask = row := by
  generalize hfind : choices.find?
      (fun candidate => candidate.rowMask == row) = found
  cases found with
  | none =>
      obtain ⟨choice, hchoice, hrow⟩ := hexists
      have hnone := (List.find?_eq_none.mp hfind) choice hchoice
      simp [hrow] at hnone
  | some choice =>
      have hchoice := List.mem_of_find?_eq_some hfind
      have hrow : choice.rowMask = row := by
        simpa only [beq_iff_eq] using List.find?_some hfind
      simpa only [Option.getD_some] using And.intro hchoice hrow

private theorem choiceForRow_spec
    (centre : Vertex) (row : UInt64)
    (hexists : ∃ choice ∈ patternSummaryChoices.getD centre.val [],
      choice.rowMask = row) :
    choiceForRow centre row ∈ patternSummaryChoices.getD centre.val [] ∧
      (choiceForRow centre row).rowMask = row := by
  exact findChoice_spec _ _ hexists

private theorem initialChoiceZero_spec :
    choiceForRow 0 30 ∈ patternSummaryChoices.getD 0 [] ∧
      (choiceForRow 0 30).rowMask = 30 := by
  apply choiceForRow_spec
  exact ⟨rowChoiceAt 0 0, rowChoiceAt_mem 0 0, rfl⟩

private def canonicalChoiceIndex : Fin 7 → Fin 35 :=
  ![0, 1, 7, 19, 20, 23, 29]

private theorem initialChoiceOne_spec (orbit : Fin 7) :
    choiceForRow 1 (canonicalRowMask orbit) ∈
        patternSummaryChoices.getD 1 [] ∧
      (choiceForRow 1 (canonicalRowMask orbit)).rowMask = canonicalRowMask orbit := by
  apply choiceForRow_spec
  let index := canonicalChoiceIndex orbit
  refine ⟨rowChoiceAt 1 index, rowChoiceAt_mem 1 index, ?_⟩
  fin_cases orbit <;> rfl

private theorem rowTwoChoice_spec (index : Fin 35) :
    choiceForRow 2 (rowTwoMask index) ∈ patternSummaryChoices.getD 2 [] ∧
      (choiceForRow 2 (rowTwoMask index)).rowMask = rowTwoMask index := by
  apply choiceForRow_spec
  exact ⟨rowChoiceAt 2 index, rowChoiceAt_mem 2 index, rowChoiceAt_two_mask index⟩

private theorem selectedByAssignmentsB_sound
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments)
    {centre target : Vertex}
    (hselected : selectedByAssignmentsB assignments centre target = true) :
    target ∈ Q.targets centre := by
  simp only [selectedByAssignmentsB, List.any_eq_true] at hselected
  obtain ⟨assignment, hassignment, hselected⟩ := hselected
  have hparts : assignment.1 = centre ∧
      bitSetB assignment.2 target.val = true := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hselected
  rcases assignment with ⟨centre', row⟩
  simp only at hparts
  rw [← hparts.1, hassignments centre' row hassignment, mem_packedRow]
  exact hparts.2

private theorem selectedByAssignmentsB_complete
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hcentres : (assignments.map Prod.fst).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    {centre target : Vertex} (hselected : target ∈ Q.targets centre) :
    selectedByAssignmentsB assignments centre target = true := by
  have hcentre : centre ∈ assignments.map Prod.fst := by
    exact hcentres.mem_iff.mpr (List.mem_finRange centre)
  rw [List.mem_map] at hcentre
  obtain ⟨assignment, hassignment, hcentre⟩ := hcentre
  rcases assignment with ⟨centre', row⟩
  simp only at hcentre
  subst centre'
  have hbit : bitSetB row target.val = true := by
    rw [← mem_packedRow, ← hassignments centre row hassignment]
    exact hselected
  simp only [selectedByAssignmentsB, List.any_eq_true]
  exact ⟨(centre, row), hassignment, by simp [hbit]⟩

private theorem patternExtendsAssignmentsB_sound
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments) {summary : PatternSummary}
    (hmatch : patternExtendsAssignmentsB assignments summary = true) :
    Extends (packedIncidence summary.mask) Q.targets := by
  intro centre target htarget
  have hcentre := (List.all_eq_true.mp hmatch) centre (List.mem_finRange centre)
  have htargetCheck :=
    (List.all_eq_true.mp hcentre) target (List.mem_finRange target)
  have hbit : bitSetB summary.mask (varIndex centre target) = true := by
    rw [mem_packedIncidence] at htarget
    simpa only [packedSelectsB] using htarget
  simp only [Bool.or_eq_true] at htargetCheck
  rcases htargetCheck with hnot | hselected
  · simp [hbit] at hnot
  · exact selectedByAssignmentsB_sound hassignments hselected

private theorem hasPatternB_sound
    {code : UInt64} {assignments : List RowAssignment}
    {patterns : PatternSummaryBuckets}
    (hmatch : hasPatternB code assignments patterns = true) :
    ∃ summary, CandidateMember summary patterns ∧
      patternExtendsAssignmentsB assignments summary = true := by
  simp only [hasPatternB, List.any_eq_true] at hmatch
  obtain ⟨bucket, hbucket, summary, hsummary, hmatch⟩ := hmatch
  have hparts : ((summary.mask &&& code) == summary.mask) = true ∧
      patternExtendsAssignmentsB assignments summary = true := by
    simpa only [patternSummaryMatchesB, Bool.and_eq_true] using hmatch
  exact ⟨summary, ⟨bucket, hbucket, hsummary⟩, hparts.2⟩

private theorem impossible_of_pattern
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {code : UInt64} {assignments : List RowAssignment}
    {patterns : PatternSummaryBuckets}
    (hassignments : AssignmentsMatch Q assignments)
    (hpatterns : PatternBucketsValid patterns)
    (hmatch : hasPatternB code assignments patterns = true) : False := by
  obtain ⟨summary, hsummary, hmatch⟩ := hasPatternB_sound hmatch
  obtain ⟨entry, _horigin, hmask, hvalidB⟩ := hpatterns summary hsummary
  have hextendsSummary := patternExtendsAssignmentsB_sound hassignments hmatch
  have hextends : Extends (packedIncidence entry.mask) Q.targets := by
    simpa only [hmask] using hextendsSummary
  have hvalid := PatternEntry.valid_of_validB hvalidB
  exact Certificate.not_convex_realises entry.certificate.toCertificate
    (entry.certificate.valid_mono hextends hvalid) hC hR

private theorem hasHardB_sound
    {code : UInt64} {assignments : List RowAssignment}
    {hardEntries : HardSummaryBuckets}
    (hmatch : hasHardB code assignments hardEntries = true) :
    ∃ summary, CandidateMember summary hardEntries ∧
      hardEqualsAssignmentsB assignments summary = true := by
  simp only [hasHardB, List.any_eq_true] at hmatch
  obtain ⟨bucket, hbucket, summary, hsummary, hmatch⟩ := hmatch
  have hparts : (summary.code == code) = true ∧
      hardEqualsAssignmentsB assignments summary = true := by
    simpa only [hardSummaryMatchesB, Bool.and_eq_true] using hmatch
  exact ⟨summary, ⟨bucket, hbucket, hsummary⟩, hparts.2⟩

private theorem impossible_of_hard
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {code : UInt64} {assignments : List RowAssignment}
    {hardEntries : HardSummaryBuckets}
    (hcentres : (assignments.map Prod.fst).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hhardEntries : HardBucketsValid hardEntries)
    (hmatch : hasHardB code assignments hardEntries = true) : False := by
  obtain ⟨summary, hsummary, hmatch⟩ := hasHardB_sound hmatch
  obtain ⟨entry, _horigin, hcode, hvalidB⟩ := hhardEntries summary hsummary
  have htargetsSummary : Q.targets = packedIncidence summary.code := by
    funext centre
    ext target
    rw [mem_packedIncidence]
    change (target ∈ Q.targets centre) ↔
      bitSetB summary.code (varIndex centre target) = true
    have hcentre := (List.all_eq_true.mp hmatch) centre (List.mem_finRange centre)
    have htarget := (List.all_eq_true.mp hcentre) target (List.mem_finRange target)
    have hequal : bitSetB summary.code (varIndex centre target) =
        selectedByAssignmentsB assignments centre target := by
      simpa only [beq_iff_eq] using htarget
    constructor
    · intro htargetQ
      have hselected := selectedByAssignmentsB_complete hcentres hassignments htargetQ
      rw [hequal]
      exact hselected
    · intro htargetBit
      apply selectedByAssignmentsB_sound hassignments
      rw [← hequal]
      exact htargetBit
  have htargets : Q.targets = packedIncidence entry.code := by
    simpa only [hcode] using htargetsSummary
  have hcertificate : entry.certificate.Valid Q.targets := by
    rw [htargets]
    exact HardEntry.valid_of_validB hvalidB
  exact Certificate.not_convex_realises entry.certificate hcertificate hC hR

private theorem directSearch_sound
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q) (hSparse : Q.PairSparse)
    {remaining : List Vertex} {assignments : List RowAssignment}
    {code : UInt64} {pairState : PairState} {hardEntries : HardSummaryBuckets}
    (hcentres : (assignments.map Prod.fst ++ remaining).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hhardEntries : HardBucketsValid hardEntries)
    (haudit : directSearch remaining assignments code pairState hardEntries = true) : False := by
  induction remaining generalizing assignments code pairState with
  | nil =>
      apply impossible_of_hard hC hR
      · simpa using hcentres
      · exact hassignments
      · exact hhardEntries
      · simpa only [directSearch] using haudit
  | cons centre remaining induction =>
      obtain ⟨index, hrow⟩ := exists_rowChoiceIndex Q centre
      let choice := rowChoiceAt centre index
      have hchoice : choice ∈ patternSummaryChoices.getD centre.val [] :=
        rowChoiceAt_mem centre index
      have hbranch := (List.all_eq_true.mp (by simpa only [directSearch] using haudit))
        choice hchoice
      have hpatterns := patternBucketsValid_of_choice hchoice
      have hcompatible := pairCompatibleB_of_pairSparse_perm Q hSparse hcentres
        hassignments hrow
      by_cases hfast : pairState.compatible choice.pairMask = true
      · simp only [hfast, if_true, Bool.or_eq_true] at hbranch
        rcases hbranch with hpattern | hrecursive
        · exact impossible_of_pattern hC hR
            (hassignments.append centre choice.rowMask hrow) hpatterns hpattern
        · have hnewCentres :
              ((assignments ++ [(centre, choice.rowMask)]).map Prod.fst ++
                remaining).Perm (List.finRange 8) := by
            simpa only [List.map_append, List.map_singleton, Prod.fst,
              List.append_assoc, List.singleton_append] using hcentres
          exact induction hnewCentres
            (hassignments.append centre choice.rowMask hrow) hrecursive
      · have hcompatibleChoice : pairCompatibleB assignments choice.rowMask = true :=
          hcompatible
        have hfastFalse := Bool.eq_false_of_not_eq_true hfast
        simp [hfastFalse, hcompatibleChoice] at hbranch

private theorem standardTargets_eq_packedRow :
    standardTargets = packedRow 30 := by
  ext target
  fin_cases target <;> decide

private theorem initialAssignmentsMatch
    {Q : OctagonIncidence} (hN : Q.Normalized) (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit)) :
    AssignmentsMatch Q [(0, 30), (1, canonicalRowMask orbit)] := by
  have hempty : AssignmentsMatch Q [] := by
    intro centre row hmember
    simp at hmember
  have hrowZero : Q.targets 0 = packedRow 30 :=
    hN.trans standardTargets_eq_packedRow
  simpa using (hempty.append 0 30 hrowZero).append
    1 (canonicalRowMask orbit) hrowOne

private theorem branch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse)
    (orbit : Fin 7) (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (rowTwo : Fin 35) (hrowTwo : Q.targets 2 = packedRow (rowTwoMask rowTwo))
    (haudit : directCoverageBranchB orbit rowTwo = true) : False := by
  let assignments : List RowAssignment := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  have hassignments : AssignmentsMatch Q assignments := by
    simpa only [assignments] using initialAssignmentsMatch hN orbit hrowOne
  have hchoice1 : choice1 ∈ patternSummaryChoices.getD 1 [] ∧
      choice1.rowMask = canonicalRowMask orbit := by
    simpa only [choice1] using initialChoiceOne_spec orbit
  have hpatterns1 : PatternBucketsValid choice1.patterns :=
    patternBucketsValid_of_choice (centre := 1) hchoice1.1
  by_cases hpattern1 : hasPatternB code assignments choice1.patterns = true
  · exact impossible_of_pattern hC hR hassignments hpatterns1 hpattern1
  · let row := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row
    have hchoice2 : choice2 ∈ patternSummaryChoices.getD 2 [] := by
      exact (rowTwoChoice_spec rowTwo).1
    have hpatterns2 : PatternBucketsValid choice2.patterns :=
      patternBucketsValid_of_choice (centre := 2) hchoice2
    have hcentresOne : (assignments.map Prod.fst ++
        2 :: [3, 4, 5, 6, 7]).Perm (List.finRange 8) := by
      change (List.finRange 8).Perm (List.finRange 8)
      exact List.Perm.refl _
    have hcompatible := pairCompatibleB_of_pairSparse_perm Q hSparse hcentresOne
      hassignments hrowTwo
    let choice0 := choiceForRow 0 30
    let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
    have hpattern1False := Bool.eq_false_of_not_eq_true hpattern1
    by_cases hfast : pairState.compatible choice2.pairMask = true
    · have hauditParts : hasPatternB (addRowCode code row 2)
            (assignments ++ [(2, row)]) choice2.patterns = true ∨
          directSearch [3, 4, 5, 6, 7] (assignments ++ [(2, row)])
            (addRowCode code row 2) (pairState.add choice2.pairMask)
            (hardSummaries orbit rowTwo) = true := by
          simpa [directCoverageBranchB, assignments, code, choice0, choice1,
            choice2, row, pairState, hpattern1False, hfast, Bool.or_eq_true]
            using haudit
      have hassignments2 := hassignments.append 2 row hrowTwo
      rcases hauditParts with hpattern2 | hrecursive
      · exact impossible_of_pattern hC hR hassignments2 hpatterns2 hpattern2
      · have hcentres :
            ((assignments ++ [(2, row)]).map Prod.fst ++
              [3, 4, 5, 6, 7]).Perm (List.finRange 8) := by
          change (List.finRange 8).Perm (List.finRange 8)
          exact List.Perm.refl _
        exact directSearch_sound hC hR hSparse hcentres hassignments2
          (hardSummaries_valid orbit rowTwo) hrecursive
    · have hfastFalse := Bool.eq_false_of_not_eq_true hfast
      have hpairFalse : pairCompatibleB assignments row = false := by
        simpa [directCoverageBranchB, assignments, code, choice0, choice1,
          choice2, row, pairState, hpattern1False, hfastFalse] using haudit
      rw [hcompatible] at hpairFalse
      contradiction

private theorem subbranch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse)
    (orbit : Fin 7) (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (rowTwo rowThree : Fin 35)
    (hrowTwo : Q.targets 2 = packedRow (rowTwoMask rowTwo))
    (hrowThree : Q.targets 3 = packedRow (rowChoiceAt 3 rowThree).rowMask)
    (haudit : directCoverageSubbranchB orbit rowTwo rowThree = true) : False := by
  let assignments : List RowAssignment := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
  have hassignments : AssignmentsMatch Q assignments := by
    simpa only [assignments] using initialAssignmentsMatch hN orbit hrowOne
  have hchoice1 : choice1 ∈ patternSummaryChoices.getD 1 [] ∧
      choice1.rowMask = canonicalRowMask orbit := by
    simpa only [choice1] using initialChoiceOne_spec orbit
  have hpatterns1 : PatternBucketsValid choice1.patterns :=
    patternBucketsValid_of_choice (centre := 1) hchoice1.1
  by_cases hpattern1 : hasPatternB code assignments choice1.patterns = true
  · exact impossible_of_pattern hC hR hassignments hpatterns1 hpattern1
  · let row2 := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row2
    have hchoice2 : choice2 ∈ patternSummaryChoices.getD 2 [] :=
      (rowTwoChoice_spec rowTwo).1
    have hpatterns2 : PatternBucketsValid choice2.patterns :=
      patternBucketsValid_of_choice (centre := 2) hchoice2
    have hcentresOne : (assignments.map Prod.fst ++
        2 :: [3, 4, 5, 6, 7]).Perm (List.finRange 8) := by
      change (List.finRange 8).Perm (List.finRange 8)
      exact List.Perm.refl _
    have hcompatible2 := pairCompatibleB_of_pairSparse_perm Q hSparse hcentresOne
      hassignments hrowTwo
    by_cases hfast2 : pairState.compatible choice2.pairMask = true
    · let assignments2 := assignments ++ [(2, row2)]
      let code2 := addRowCode code row2 2
      let pairState2 := pairState.add choice2.pairMask
      have hassignments2 : AssignmentsMatch Q assignments2 :=
        hassignments.append 2 row2 hrowTwo
      by_cases hpattern2 : hasPatternB code2 assignments2 choice2.patterns = true
      · exact impossible_of_pattern hC hR hassignments2 hpatterns2 hpattern2
      · let choice3 := patternSummaryChoices3.getD rowThree.val ⟨0, 0, []⟩
        have hchoice3Equal : choice3 = rowChoiceAt 3 rowThree := by
          rfl
        have hchoice3 : choice3 ∈ patternSummaryChoices.getD 3 [] := by
          rw [hchoice3Equal]
          exact rowChoiceAt_mem 3 rowThree
        have hpatterns3 : PatternBucketsValid choice3.patterns :=
          patternBucketsValid_of_choice (centre := 3) hchoice3
        have hcentresTwo : (assignments2.map Prod.fst ++
            3 :: [4, 5, 6, 7]).Perm (List.finRange 8) := by
          change (List.finRange 8).Perm (List.finRange 8)
          exact List.Perm.refl _
        have hrowThreeChoice : Q.targets 3 = packedRow choice3.rowMask := by
          rw [hchoice3Equal]
          exact hrowThree
        have hcompatible3 := pairCompatibleB_of_pairSparse_perm Q hSparse
          hcentresTwo hassignments2 hrowThreeChoice
        have hpattern1False := Bool.eq_false_of_not_eq_true hpattern1
        simp [directCoverageSubbranchB, assignments, code, choice0, choice1,
          pairState, row2, choice2, assignments2, code2, pairState2,
          hpattern1False, hfast2] at haudit
        have hnotCorePattern : ¬ hasPatternB
            (addRowCode (addRowCode (addRowCode 0 30 0)
              (canonicalRowMask orbit) 1) (rowTwoMask rowTwo) 2)
            [(0, 30), (1, canonicalRowMask orbit), (2, rowTwoMask rowTwo)]
            (choiceForRow 2 (rowTwoMask rowTwo)).patterns = true := by
          simpa [code2, code, assignments2, assignments, choice2, row2] using hpattern2
        have hauditTail := Or.resolve_left haudit hnotCorePattern
        change (if pairState2.compatible choice3.pairMask = true then
            hasPatternB (addRowCode code2 choice3.rowMask 3)
                (assignments2 ++ [(3, choice3.rowMask)]) choice3.patterns = true ∨
              directSearch [4, 5, 6, 7]
                (assignments2 ++ [(3, choice3.rowMask)])
                (addRowCode code2 choice3.rowMask 3)
                (pairState2.add choice3.pairMask) (hardSummaries orbit rowTwo) = true
          else pairCompatibleB assignments2 choice3.rowMask = false) at hauditTail
        by_cases hfast3 : pairState2.compatible choice3.pairMask = true
        · have hauditParts : hasPatternB (addRowCode code2 choice3.rowMask 3)
                (assignments2 ++ [(3, choice3.rowMask)]) choice3.patterns = true ∨
              directSearch [4, 5, 6, 7]
                (assignments2 ++ [(3, choice3.rowMask)])
                (addRowCode code2 choice3.rowMask 3)
                (pairState2.add choice3.pairMask)
                (hardSummaries orbit rowTwo) = true := by
              simpa only [hfast3, if_true] using hauditTail
          have hassignments3 := hassignments2.append 3 choice3.rowMask hrowThree
          rcases hauditParts with hpattern3 | hrecursive
          · exact impossible_of_pattern hC hR hassignments3 hpatterns3 hpattern3
          · have hcentres :
                ((assignments2 ++ [(3, choice3.rowMask)]).map Prod.fst ++
                  [4, 5, 6, 7]).Perm (List.finRange 8) := by
              change (List.finRange 8).Perm (List.finRange 8)
              exact List.Perm.refl _
            exact directSearch_sound hC hR hSparse hcentres hassignments3
              (hardSummaries_valid orbit rowTwo) hrecursive
        · have hfast3False := Bool.eq_false_of_not_eq_true hfast3
          have hpairFalse : pairCompatibleB assignments2 choice3.rowMask = false := by
            simpa [hfast3False] using hauditTail
          rw [hcompatible3] at hpairFalse
          contradiction
    · have hfast2False := Bool.eq_false_of_not_eq_true hfast2
      have hpattern1False := Bool.eq_false_of_not_eq_true hpattern1
      have hpairFalse : pairCompatibleB assignments row2 = false := by
        simpa [directCoverageSubbranchB, assignments, code, choice0, choice1,
          pairState, row2, choice2, hpattern1False, hfast2False] using haudit
      rw [hcompatible2] at hpairFalse
      contradiction

/-- Soundness of adaptive static audits for a canonical normalized branch. -/
theorem canonicalBranch_impossible_of_staticCoverage
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse)
    (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (haudit : ∀ rowTwo : Fin 35, BranchAudit orbit rowTwo) : False := by
  obtain ⟨rowTwo, hrowTwo⟩ := exists_rowTwoIndex Q
  rcases haudit rowTwo with hbranch | hsubbranches
  · exact branch_impossible hC hR hN hSparse orbit hrowOne rowTwo hrowTwo hbranch
  · obtain ⟨rowThree, hrowThree⟩ := exists_rowChoiceIndex Q 3
    exact subbranch_impossible hC hR hN hSparse orbit hrowOne rowTwo rowThree
      hrowTwo hrowThree (hsubbranches rowThree)

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
