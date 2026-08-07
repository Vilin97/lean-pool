/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoiceValidity
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryValidity
import LeanPool.Erdos97ConvexOctagon.PairStateExactness
import LeanPool.Erdos97ConvexOctagon.RowSymmetry

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

private theorem AssignmentsMatch.cons
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hmatch : AssignmentsMatch Q assignments)
    (centre : Vertex) (row : UInt64)
    (hrow : Q.targets centre = packedRow row) :
    AssignmentsMatch Q ((centre, row) :: assignments) := by
  intro centre' row' hassignment
  rcases List.mem_cons.mp hassignment with hnew | hprevious
  · simp only [Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact hrow
  · exact hmatch centre' row' hprevious

private theorem assignmentColumnCount_eq_filter_length
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments) (target : Vertex) :
    assignmentColumnCount assignments target =
      ((assignments.map Prod.fst).filter fun centre =>
        target ∈ Q.targets centre).length := by
  induction assignments with
  | nil => rfl
  | cons assignment assignments induction =>
      rcases assignment with ⟨centre, row⟩
      have hrow := hassignments centre row (by simp)
      have htail : AssignmentsMatch Q assignments := by
        intro centre' row' hmember
        exact hassignments centre' row' (by simp [hmember])
      have hinduction := induction htail
      by_cases hbit : bitSetB row target.val = true
      · have htarget : target ∈ Q.targets centre := by
          rw [hrow, mem_packedRow]
          exact hbit
        simpa [assignmentColumnCount, hbit, htarget] using
          congrArg Nat.succ hinduction
      · have htarget : target ∉ Q.targets centre := by
          intro htarget
          apply hbit
          rw [← mem_packedRow, ← hrow]
          exact htarget
        simpa [assignmentColumnCount, hbit, htarget] using hinduction

private theorem finRange_filter_length_eq_indegree
    (Q : OctagonIncidence) (target : Vertex) :
    ((List.finRange 8).filter fun centre =>
      target ∈ Q.targets centre).length = Q.indegree target := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 8).filter _)]
  simp only [List.toFinset_filter, List.toFinset_finRange]
  unfold OctagonIncidence.indegree
  rw [Finset.sum_boole]
  norm_num

private theorem remaining_selected_le_capacity
    (Q : OctagonIncidence) (remaining : List Vertex) (target : Vertex) :
    ((remaining.filter fun centre => target ∈ Q.targets centre).length ≤
      (remaining.filter (· ≠ target)).length) := by
  induction remaining with
  | nil => simp
  | cons centre remaining induction =>
      by_cases hselected : target ∈ Q.targets centre
      · have hne : centre ≠ target := by
          intro hequal
          subst centre
          exact Q.centre_not_mem target hselected
        have hselectedB := decide_eq_true hselected
        have hneB := decide_eq_true hne
        simp only [List.filter_cons, hselectedB, hneB, if_true,
          List.length_cons]
        exact Nat.succ_le_succ induction
      · by_cases hne : centre ≠ target
        · have hselectedB := decide_eq_false hselected
          have hneB := decide_eq_true hne
          simp only [List.filter_cons, hselectedB, hneB, if_true,
            List.length_cons]
          exact Nat.le_succ_of_le induction
        · have hselectedB := decide_eq_false hselected
          have hneB := decide_eq_false hne
          simp only [List.filter_cons, hselectedB, hneB]
          exact induction

private theorem assignmentColumnBounds
    (Q : OctagonIncidence) (hBalanced : Q.Balanced)
    {assignments : List RowAssignment} {remaining : List Vertex}
    (hcentres : (assignments.map Prod.fst ++ remaining).Perm
      (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments) (target : Vertex) :
    assignmentColumnCount assignments target ≤ 4 ∧
      4 ≤ assignmentColumnCount assignments target +
        remainingColumnCapacity remaining target := by
  have hfiltered := hcentres.filter (fun centre => target ∈ Q.targets centre)
  have hdecomposition :
      ((assignments.map Prod.fst).filter fun centre =>
          target ∈ Q.targets centre).length +
        (remaining.filter fun centre => target ∈ Q.targets centre).length =
        ((List.finRange 8).filter fun centre =>
          target ∈ Q.targets centre).length := by
    simpa only [List.filter_append, List.length_append] using hfiltered.length_eq
  have hsum : assignmentColumnCount assignments target +
      (remaining.filter fun centre => target ∈ Q.targets centre).length = 4 := by
    rw [assignmentColumnCount_eq_filter_length hassignments]
    calc
      _ = ((List.finRange 8).filter fun centre =>
          target ∈ Q.targets centre).length := hdecomposition
      _ = Q.indegree target := finRange_filter_length_eq_indegree Q target
      _ = 4 := hBalanced target
  have hremaining := remaining_selected_le_capacity Q remaining target
  constructor
  · omega
  · unfold remainingColumnCapacity
    omega

private theorem columnFeasibleB_of_balanced
    (Q : OctagonIncidence) (hBalanced : Q.Balanced)
    {assignments : List RowAssignment} {remaining : List Vertex}
    (hcentres : (assignments.map Prod.fst ++ remaining).Perm
      (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments) :
    columnFeasibleB assignments remaining = true := by
  apply List.all_eq_true.mpr
  intro target _htarget
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact assignmentColumnBounds Q hBalanced hcentres hassignments target

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

private theorem columnConflictHintB_eq_false_of_feasible
    {assignments : List RowAssignment} {remaining : List Vertex}
    {state : ColumnState}
    (hfeasible : columnFeasibleB assignments remaining = true) :
    columnConflictHintB assignments remaining state = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hhint
  unfold columnConflictHintB at hhint
  generalize hfind : (List.finRange 8).find? (fun target =>
    let count := state.count target
    !(decide (count ≤ 4) &&
      decide (4 ≤ count + remainingColumnCapacity remaining target))) = found at hhint
  cases found with
  | none =>
      simp at hhint
  | some target =>
      simp only at hhint
      have htarget := (List.all_eq_true.mp hfeasible) target
        (List.mem_finRange target)
      rw [htarget] at hhint
      simp at hhint

private theorem withPairPruningB_eq_of_exact
    {assignments : List RowAssignment} {row : UInt64}
    {state : PairState} {pairMask : UInt64} {continueSearch : Unit → Bool}
    (hexact : state.Exact assignments)
    (hmask : pairMask = rowPairMask row)
    (hcompatible : pairCompatibleB assignments row = true) :
    withPairPruningB assignments row state pairMask continueSearch =
      continueSearch () := by
  have hfast := state.compatible_of_exact hexact hmask hcompatible
  simp [withPairPruningB, hfast]

private theorem withColumnPruningB_eq_of_feasible
    {assignments : List RowAssignment} {remaining : List Vertex}
    {state : ColumnState} {continueSearch : Unit → Bool}
    (hfeasible : columnFeasibleB assignments remaining = true) :
    withColumnPruningB assignments remaining state continueSearch =
      continueSearch () := by
  have hhint := columnConflictHintB_eq_false_of_feasible
    (state := state) hfeasible
  by_cases hfast : state.feasible remaining = true
  · simp [withColumnPruningB, hfast]
  · have hfastFalse := Bool.eq_false_of_not_eq_true hfast
    simp [withColumnPruningB, hfastFalse, hhint]

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

private theorem pairMask_eq_rowPairMask_of_choice
    {centre : Vertex} {choice : SummaryRowChoice}
    (hchoice : choice ∈ patternSummaryChoices.getD centre.val []) :
    choice.pairMask = rowPairMask choice.rowMask := by
  have hchoiceAudit :=
    (List.all_eq_true.mp (patternSummaryChoices_valid centre)) choice hchoice
  simp only [Bool.and_eq_true] at hchoiceAudit
  exact beq_iff_eq.mp hchoiceAudit.2

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
    {code : UInt64} {pairState : PairState} {columnState : ColumnState}
    {hardEntries : HardSummaryBuckets}
    (hcentres : (assignments.map Prod.fst ++ remaining).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hpairState : pairState.Exact assignments)
    (hhardEntries : HardBucketsValid hardEntries)
    (haudit : directSearch remaining assignments code pairState columnState
      hardEntries = true) : False := by
  induction remaining generalizing assignments code pairState columnState with
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
      have hmask := pairMask_eq_rowPairMask_of_choice (centre := centre) hchoice
      have hcompatible := pairCompatibleB_of_pairSparse_perm Q hSparse hcentres
        hassignments hrow
      have hnewAssignments := hassignments.cons centre choice.rowMask hrow
      have hnewPairState :=
        hpairState.add centre choice.rowMask choice.pairMask hmask
      have hnewCentres :
          (((centre, choice.rowMask) :: assignments).map Prod.fst ++
            remaining).Perm (List.finRange 8) := by
        simpa only [List.map_cons, Prod.fst, List.cons_append] using
          (List.perm_middle.symm.trans hcentres)
      rw [withPairPruningB_eq_of_exact hpairState hmask hcompatible] at hbranch
      have hsemantic := columnFeasibleB_of_balanced Q
        (Q.balanced_of_pairSparse hSparse) hnewCentres hnewAssignments
      rw [withColumnPruningB_eq_of_feasible hsemantic] at hbranch
      simp only [Bool.or_eq_true] at hbranch
      rcases hbranch with hpattern | hrecursive
      · exact impossible_of_pattern hC hR hnewAssignments hpatterns hpattern
      · exact induction hnewCentres hnewAssignments hnewPairState hrecursive

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

private theorem initialPairState_exact (orbit : Fin 7) :
    let choice0 := choiceForRow 0 30
    let choice1 := choiceForRow 1 (canonicalRowMask orbit)
    ((PairState.empty.add choice0.pairMask).add choice1.pairMask).Exact
      [(0, 30), (1, canonicalRowMask orbit)] := by
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  have hchoice0 : choice0 ∈ patternSummaryChoices.getD 0 [] ∧
      choice0.rowMask = 30 := by
    simpa only [choice0] using initialChoiceZero_spec
  have hchoice1 : choice1 ∈ patternSummaryChoices.getD 1 [] ∧
      choice1.rowMask = canonicalRowMask orbit := by
    simpa only [choice1] using initialChoiceOne_spec orbit
  have hmask0 := pairMask_eq_rowPairMask_of_choice (centre := 0) hchoice0.1
  have hmask1 := pairMask_eq_rowPairMask_of_choice (centre := 1) hchoice1.1
  rw [hchoice0.2] at hmask0
  rw [hchoice1.2] at hmask1
  have hexact0 :=
    PairState.empty_exact.add 0 30 choice0.pairMask hmask0
  have hexact1 :=
    hexact0.add 1 (canonicalRowMask orbit) choice1.pairMask hmask1
  exact hexact1.perm (List.Perm.swap _ _ [])

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
    have hchoice2Spec : choice2 ∈ patternSummaryChoices.getD 2 [] ∧
        choice2.rowMask = row := by
      simpa only [choice2, row] using rowTwoChoice_spec rowTwo
    have hchoice2 := hchoice2Spec.1
    have hpatterns2 : PatternBucketsValid choice2.patterns :=
      patternBucketsValid_of_choice (centre := 2) hchoice2
    have hmask2 := pairMask_eq_rowPairMask_of_choice (centre := 2) hchoice2
    rw [hchoice2Spec.2] at hmask2
    have hcentresOne : (assignments.map Prod.fst ++
        2 :: searchCentres).Perm (List.finRange 8) := by
      change ([0, 1, 2] ++ searchCentres : List Vertex).Perm (List.finRange 8)
      decide
    have hcompatible := pairCompatibleB_of_pairSparse_perm Q hSparse hcentresOne
      hassignments hrowTwo
    let choice0 := choiceForRow 0 30
    let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
    have hpairState : pairState.Exact assignments := by
      simpa only [pairState, assignments, choice0, choice1] using
        initialPairState_exact orbit
    let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
    have hpattern1False := Bool.eq_false_of_not_eq_true hpattern1
    let assignments2 := (2, row) :: assignments
    let code2 := addRowCode code row 2
    let pairState2 := pairState.add choice2.pairMask
    let columnState2 := columnState.add row
    have hassignments2 : AssignmentsMatch Q assignments2 :=
      hassignments.cons 2 row hrowTwo
    have hpairState2 : pairState2.Exact assignments2 := by
      exact hpairState.add 2 row choice2.pairMask hmask2
    have hcentres : (assignments2.map Prod.fst ++ searchCentres).Perm
        (List.finRange 8) := by
      change ([2, 0, 1] ++ searchCentres : List Vertex).Perm (List.finRange 8)
      decide
    have hwrapped : withPairPruningB assignments row pairState choice2.pairMask
        (fun _ => withColumnPruningB assignments2 searchCentres columnState2 fun _ =>
          hasPatternB code2 assignments2 choice2.patterns ||
            directSearch searchCentres assignments2 code2 pairState2 columnState2
              (hardSummaries orbit rowTwo)) = true := by
      simpa [directCoverageBranchB, assignments, code, choice0, choice1,
        choice2, row, pairState, columnState, assignments2, code2,
        pairState2, columnState2, hpattern1False] using haudit
    rw [withPairPruningB_eq_of_exact hpairState hmask2 hcompatible] at hwrapped
    have hsemantic := columnFeasibleB_of_balanced Q
      (Q.balanced_of_pairSparse hSparse) hcentres hassignments2
    rw [withColumnPruningB_eq_of_feasible hsemantic] at hwrapped
    have hauditParts : hasPatternB code2 assignments2 choice2.patterns = true ∨
          directSearch searchCentres assignments2 code2 pairState2 columnState2
            (hardSummaries orbit rowTwo) = true := by
      simpa only [Bool.or_eq_true] using hwrapped
    rcases hauditParts with hpattern2 | hrecursive
    · exact impossible_of_pattern hC hR hassignments2 hpatterns2 hpattern2
    · exact directSearch_sound hC hR hSparse hcentres hassignments2 hpairState2
        (hardSummaries_valid orbit rowTwo) hrecursive

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
  let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
  have hassignments : AssignmentsMatch Q assignments := by
    simpa only [assignments] using initialAssignmentsMatch hN orbit hrowOne
  have hpairState : pairState.Exact assignments := by
    simpa only [pairState, assignments, choice0, choice1] using
      initialPairState_exact orbit
  have hchoice1 : choice1 ∈ patternSummaryChoices.getD 1 [] ∧
      choice1.rowMask = canonicalRowMask orbit := by
    simpa only [choice1] using initialChoiceOne_spec orbit
  have hpatterns1 : PatternBucketsValid choice1.patterns :=
    patternBucketsValid_of_choice (centre := 1) hchoice1.1
  by_cases hpattern1 : hasPatternB code assignments choice1.patterns = true
  · exact impossible_of_pattern hC hR hassignments hpatterns1 hpattern1
  · let row2 := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row2
    have hchoice2Spec : choice2 ∈ patternSummaryChoices.getD 2 [] ∧
        choice2.rowMask = row2 := by
      simpa only [choice2, row2] using rowTwoChoice_spec rowTwo
    have hchoice2 := hchoice2Spec.1
    have hpatterns2 : PatternBucketsValid choice2.patterns :=
      patternBucketsValid_of_choice (centre := 2) hchoice2
    have hmask2 := pairMask_eq_rowPairMask_of_choice (centre := 2) hchoice2
    rw [hchoice2Spec.2] at hmask2
    have hcentresOne : (assignments.map Prod.fst ++
        2 :: searchCentres).Perm (List.finRange 8) := by
      change ([0, 1, 2] ++ searchCentres : List Vertex).Perm (List.finRange 8)
      decide
    have hcompatible2 := pairCompatibleB_of_pairSparse_perm Q hSparse hcentresOne
      hassignments hrowTwo
    let assignments2 := (2, row2) :: assignments
    let code2 := addRowCode code row2 2
    let pairState2 := pairState.add choice2.pairMask
    let columnState2 := columnState.add row2
    have hassignments2 : AssignmentsMatch Q assignments2 :=
      hassignments.cons 2 row2 hrowTwo
    have hpairState2 : pairState2.Exact assignments2 := by
      exact hpairState.add 2 row2 choice2.pairMask hmask2
    have hcentres2 : (assignments2.map Prod.fst ++ searchCentres).Perm
        (List.finRange 8) := by
      change ([2, 0, 1] ++ searchCentres : List Vertex).Perm (List.finRange 8)
      decide
    have hsemantic2 := columnFeasibleB_of_balanced Q
      (Q.balanced_of_pairSparse hSparse) hcentres2 hassignments2
    let choice3 := patternSummaryChoices3.getD rowThree.val ⟨0, 0, []⟩
    have hchoice3Equal : choice3 = rowChoiceAt 3 rowThree := by rfl
    have hchoice3 : choice3 ∈ patternSummaryChoices.getD 3 [] := by
      rw [hchoice3Equal]
      exact rowChoiceAt_mem 3 rowThree
    have hpatterns3 : PatternBucketsValid choice3.patterns :=
      patternBucketsValid_of_choice (centre := 3) hchoice3
    have hmask3 := pairMask_eq_rowPairMask_of_choice (centre := 3) hchoice3
    have hcentresTwo : (assignments2.map Prod.fst ++
        3 :: searchCentres.tail).Perm (List.finRange 8) := by
      simpa only [searchCentres, List.tail_cons] using hcentres2
    have hrowThreeChoice : Q.targets 3 = packedRow choice3.rowMask := by
      rw [hchoice3Equal]
      exact hrowThree
    have hcompatible3 := pairCompatibleB_of_pairSparse_perm Q hSparse
      hcentresTwo hassignments2 hrowThreeChoice
    let assignments3 := (3, choice3.rowMask) :: assignments2
    let code3 := addRowCode code2 choice3.rowMask 3
    let pairState3 := pairState2.add choice3.pairMask
    let columnState3 := columnState2.add choice3.rowMask
    have hassignments3 : AssignmentsMatch Q assignments3 :=
      hassignments2.cons 3 choice3.rowMask hrowThreeChoice
    have hpairState3 : pairState3.Exact assignments3 := by
      exact hpairState2.add 3 choice3.rowMask choice3.pairMask hmask3
    have hcentres3 : (assignments3.map Prod.fst ++ searchCentres.tail).Perm
        (List.finRange 8) := by
      simpa only [assignments3, List.map_cons, Prod.fst, List.cons_append] using
        (List.perm_middle.symm.trans hcentresTwo)
    have hsemantic3 := columnFeasibleB_of_balanced Q
      (Q.balanced_of_pairSparse hSparse) hcentres3 hassignments3
    have hpattern1False := Bool.eq_false_of_not_eq_true hpattern1
    have hwrapped : withPairPruningB assignments row2 pairState choice2.pairMask
        (fun _ => withColumnPruningB assignments2 searchCentres columnState2 fun _ =>
          if hasPatternB code2 assignments2 choice2.patterns then true
          else withPairPruningB assignments2 choice3.rowMask pairState2
            choice3.pairMask (fun _ => withColumnPruningB assignments3
              searchCentres.tail columnState3 fun _ =>
                hasPatternB code3 assignments3 choice3.patterns ||
                  directSearch searchCentres.tail assignments3 code3 pairState3
                    columnState3 (hardSummaries orbit rowTwo))) = true := by
      simpa [directCoverageSubbranchB, assignments, code, choice0, choice1,
        pairState, columnState, row2, choice2, assignments2, code2,
        pairState2, columnState2, choice3, assignments3, code3,
        pairState3, columnState3, hpattern1False] using haudit
    rw [withPairPruningB_eq_of_exact hpairState hmask2 hcompatible2] at hwrapped
    rw [withColumnPruningB_eq_of_feasible hsemantic2] at hwrapped
    by_cases hpattern2 : hasPatternB code2 assignments2 choice2.patterns = true
    · exact impossible_of_pattern hC hR hassignments2 hpatterns2 hpattern2
    · have hpattern2False := Bool.eq_false_of_not_eq_true hpattern2
      simp only [hpattern2False] at hwrapped
      rw [withPairPruningB_eq_of_exact hpairState2 hmask3 hcompatible3] at hwrapped
      rw [withColumnPruningB_eq_of_feasible hsemantic3] at hwrapped
      by_cases hpattern3 : hasPatternB code3 assignments3 choice3.patterns = true
      · exact impossible_of_pattern hC hR hassignments3 hpatterns3 hpattern3
      · have hpattern3False := Bool.eq_false_of_not_eq_true hpattern3
        have hrecursive : directSearch searchCentres.tail assignments3 code3
            pairState3 columnState3 (hardSummaries orbit rowTwo) = true := by
          simpa [hpattern3False] using hwrapped
        exact directSearch_sound hC hR hSparse hcentres3 hassignments3 hpairState3
          (hardSummaries_valid orbit rowTwo) hrecursive

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
