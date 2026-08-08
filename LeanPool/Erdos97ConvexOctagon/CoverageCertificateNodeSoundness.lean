/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCoverSoundness
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryValidity
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSemanticSoundness

/-! # Soundness of flat postorder coverage-certificate nodes -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Semantic validity accessors needed by the generic certificate proof. -/
structure CertificateAudits where
  /-- Every successful conflict-cover lookup is sound. -/
  coverValid : ∀ {identifier cover},
    conflictCoverAt? identifier = some cover → cover.Valid
  /-- Every successful dense pattern lookup is sound. -/
  patternValid : ∀ {identifier summary},
    densePatternSummaryAt? identifier = some summary → summary.Valid
  /-- Every successful dense exact lookup is sound. -/
  hardValid : ∀ {identifier summary},
    denseHardSummaryAt? identifier = some summary → summary.Valid

/-- A matching valid dense pattern identifier contradicts a realised convex table. -/
theorem impossible_of_patternIdentifier
    (audits : CertificateAudits)
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {assignments : List RowAssignment} {code : UInt64}
    (hassignments : AssignmentsMatch Q assignments)
    (hcode : CodeMatches code assignments)
    {identifier : Nat}
    (hidentifier : patternIdentifierPackedMatchesB identifier code = true) :
    False := by
  unfold patternIdentifierPackedMatchesB at hidentifier
  generalize hlookup : densePatternSummaryAt? identifier = found at hidentifier
  cases found with
  | none => simp at hidentifier
  | some summary =>
      exact impossible_of_patternSummary hC hR hassignments hcode
        (audits.patternValid hlookup) hidentifier

private theorem impossible_of_hardIdentifier
    (audits : CertificateAudits)
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {assignments : List RowAssignment} {code : UInt64}
    (hcentres : (assignments.map Prod.fst).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hcode : CodeMatches code assignments)
    {identifier : Nat}
    (hidentifier : hardIdentifierPackedMatchesB identifier code = true) :
    False := by
  unfold hardIdentifierPackedMatchesB at hidentifier
  generalize hlookup : denseHardSummaryAt? identifier = found at hidentifier
  cases found with
  | none => simp at hidentifier
  | some summary =>
      exact impossible_of_hardSummary hC hR hcentres hassignments hcode
        (audits.hardValid hlookup) hidentifier

private theorem nodePruningFacts_of_valid
    {claims : BranchClaims} {identifier : Nat}
    (hidentifier : identifier < claims.nodeCount)
    (hvalid : nodePruningValidB claims identifier = true) :
    let claim := claims.nodeAt identifier
    ∃ cover,
      claim.depth < searchCentres.length ∧
      conflictCoverAt? claim.conflictCoverId = some cover ∧
      cover.centre = (searchCentres.getD claim.depth 0).val ∧
      cover.requiredPairs &&& claim.pairTwice = cover.requiredPairs ∧
      claim.activeRows ||| (claim.rejectedRows ||| cover.incompatibleRows) =
        34359738367 ∧
      ∀ wordIndex ∈ List.range 7,
        rejectedWordValidB claim (searchCentres.getD claim.depth 0)
          (searchCentres.drop (claim.depth + 1))
          (rowIndexWord claim.rejectedRows (5 * wordIndex))
          (claim.rejectionTargetGroups.getD wordIndex []) = true := by
  unfold nodePruningValidB at hvalid
  rw [if_pos hidentifier] at hvalid
  let claim := claims.nodeAt identifier
  change (if claim.depth < searchCentres.length then _ else false) = true at hvalid
  by_cases hdepth : claim.depth < searchCentres.length
  · rw [if_pos hdepth] at hvalid
    let centre := searchCentres.getD claim.depth 0
    let remaining := searchCentres.drop (claim.depth + 1)
    generalize hlookup : conflictCoverAt? claim.conflictCoverId = found at hvalid
    cases found with
    | none => simp at hvalid
    | some cover =>
        have hclean :
            (((((cover.centre = centre.val ∧
                  cover.requiredPairs &&& claim.pairTwice = cover.requiredPairs) ∧
                claim.patternRows &&& claim.activeRows = claim.patternRows) ∧
              claim.rejectedRows &&& cover.incompatibleRows = 0) ∧
            claim.activeRows &&&
                (claim.rejectedRows ||| cover.incompatibleRows) = 0) ∧
            claim.activeRows ||| (claim.rejectedRows ||| cover.incompatibleRows) =
              34359738367) ∧
            ∀ wordIndex, wordIndex < 7 →
              rejectedWordValidB claim centre remaining
                (rowIndexWord claim.rejectedRows (5 * wordIndex))
                (claim.rejectionTargetGroups.getD wordIndex []) = true := by
          simpa [claim, centre, remaining] using hvalid
        rcases hclean with
          ⟨⟨⟨⟨⟨⟨hcentre, hrequired⟩, _hpattern⟩, _hrejected⟩,
            _hactive⟩, hpartition⟩, hwords⟩
        refine ⟨cover, hdepth, hlookup, hcentre, hrequired, hpartition, ?_⟩
        intro wordIndex hwordIndex
        exact hwords wordIndex (List.mem_range.mp hwordIndex)
  · rw [if_neg hdepth] at hvalid
    simp at hvalid

private theorem nodeTransitionWords_of_valid
    {claims : BranchClaims} {identifier : Nat}
    (hidentifier : identifier < claims.nodeCount)
    (hvalid : nodeTransitionsValidB claims identifier = true) :
    let claim := claims.nodeAt identifier
    claim.depth < searchCentres.length ∧
      ∀ wordIndex ∈ List.range 7,
        nodeWordValidB claims identifier claim
          (searchCentres.getD claim.depth 0)
          (searchCentres.drop (claim.depth + 1))
          ⟨claim.pairOnce, claim.pairTwice⟩ wordIndex = true := by
  unfold nodeTransitionsValidB at hvalid
  rw [if_pos hidentifier] at hvalid
  let claim := claims.nodeAt identifier
  change (if claim.depth < searchCentres.length then _ else false) = true at hvalid
  by_cases hdepth : claim.depth < searchCentres.length
  · rw [if_pos hdepth] at hvalid
    refine ⟨hdepth, ?_⟩
    intro wordIndex hwordIndex
    exact (List.all_eq_true.mp hvalid) wordIndex hwordIndex
  · rw [if_neg hdepth] at hvalid
    simp at hvalid

private theorem impossible_of_rejectedRow
    {Q : OctagonIncidence} (hBalanced : Q.Balanced)
    {assignments : List RowAssignment} {claim : NodeClaim}
    {centre : Vertex} {remaining : List Vertex} {rowIndex : Fin 35}
    (hdepth : claim.depth < searchCentres.length)
    (hcentres : (assignments.map Prod.fst).Perm
      (assignedCentres claim.depth))
    (hassignments : AssignmentsMatch Q assignments)
    (hcode : CodeMatches claim.code assignments)
    (hcentre : centre = searchCentres.getD claim.depth 0)
    (hrow : Q.targets centre =
      packedRow (searchRowChoiceAt centre rowIndex).rowMask)
    (hrejected : RejectedRowValid claim centre remaining rowIndex.val)
    (hremaining : remaining = searchCentres.drop (claim.depth + 1)) : False := by
  obtain ⟨target, htarget⟩ := hrejected
  unfold rejectedRowValidB at htarget
  split at htarget
  next htargetBound =>
    let targetVertex : Vertex := ⟨target, htargetBound⟩
    let choice := (searchRowChoices.getD centre.val #[]).getD rowIndex.val
      ⟨0, 0⟩
    let reconstructed :=
      (centre, choice.rowMask) :: assignmentsFromCode claim.code claim.depth
    have hreconstructed : AssignmentsMatch Q reconstructed := by
      apply (assignmentsFromCode_match hcentres hassignments hcode).cons
      simpa only [choice, searchRowChoiceAt] using hrow
    have hpermutation : (reconstructed.map Prod.fst ++ remaining).Perm
        (List.finRange 8) := by
      rw [hremaining]
      simpa [reconstructed, choice, hcentre] using
        reconstructedCentres_perm claim.code choice.rowMask claim.depth hdepth
    have hbounds := assignmentColumnBounds Q hBalanced hpermutation
      hreconstructed targetVertex
    have hconflict :
        4 < assignmentColumnCount reconstructed targetVertex ∨
          assignmentColumnCount reconstructed targetVertex +
            remainingColumnCapacity remaining targetVertex < 4 := by
      simpa only [reconstructed, choice, targetVertex, Bool.or_eq_true,
        decide_eq_true_eq] using htarget
    omega
  next => simp at htarget

/-- A locally valid postorder node contradicts every matching semantic search prefix. -/
theorem BranchClaims.node_impossible
    (audits : CertificateAudits)
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (claims : BranchClaims) (hlocally : claims.LocallyValid) :
    ∀ identifier, identifier < claims.nodeCount →
      ∀ assignments : List RowAssignment,
        (assignments.map Prod.fst).Perm
            (assignedCentres (claims.nodeAt identifier).depth) →
        AssignmentsMatch Q assignments →
        CodeMatches (claims.nodeAt identifier).code assignments →
        (PairState.mk (claims.nodeAt identifier).pairOnce
          (claims.nodeAt identifier).pairTwice).Exact assignments → False := by
  intro identifier
  induction identifier using Nat.strong_induction_on with
  | h identifier hinduction =>
      intro hidentifier assignments hcentres hassignments hcode hpair
      let claim := claims.nodeAt identifier
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      let pairState : PairState := ⟨claim.pairOnce, claim.pairTwice⟩
      have hlocal := hlocally identifier hidentifier
      have hlocalParts : nodePruningValidB claims identifier = true ∧
          nodeTransitionsValidB claims identifier = true := by
        simpa only [nodeLocalValidB, Bool.and_eq_true] using hlocal
      obtain ⟨cover, hdepth, hcoverLookup, hcoverCentre, hrequired,
          hpartition, hrejectedWords⟩ :=
        nodePruningFacts_of_valid hidentifier hlocalParts.1
      obtain ⟨_htransitionDepth, htransitionWords⟩ :=
        nodeTransitionWords_of_valid hidentifier hlocalParts.2
      change (assignments.map Prod.fst).Perm (assignedCentres claim.depth) at hcentres
      change CodeMatches claim.code assignments at hcode
      change pairState.Exact assignments at hpair
      obtain ⟨rowIndex, hrow⟩ := exists_searchRowChoiceIndex Q centre
      let choice := searchRowChoiceAt centre rowIndex
      have hallCentres :
          (assignments.map Prod.fst ++ centre :: remaining).Perm
            (List.finRange 8) := by
        have hsuffix := assignedCentres_remaining_perm claim.depth
          (Nat.le_of_lt hdepth)
        rw [searchCentres_drop_eq_cons claim.depth hdepth] at hsuffix
        exact (hcentres.append_right (centre :: remaining)).trans hsuffix
      have hsemanticCompatible :
          pairCompatibleB assignments choice.rowMask = true :=
        pairCompatibleB_of_pairSparse_perm Q hSparse hallCentres hassignments
          (by simpa only [choice] using hrow)
      have hpackedCompatible : pairState.compatible choice.pairMask = true :=
        pairState.compatible_of_exact hpair
          (by simpa only [choice] using searchRowChoiceAt_pairMask centre rowIndex)
          hsemanticCompatible
      have hcompatibleRow : bitSetB cover.incompatibleRows rowIndex.val = false :=
        ConflictCover.compatible_row_not_incompatible
          (audits.coverValid hcoverLookup) (state := pairState) centre rowIndex
          hcoverCentre hrequired hpackedCompatible
      rcases active_or_rejected_of_partition rowIndex hpartition hcompatibleRow with
        hactive | hrejected
      · have hwordIndex := rowIndex_wordIndex_mem_range rowIndex
        have hword := htransitionWords (rowIndex.val / 5) hwordIndex
        have hrowMember := rowIndex_mem_word_of_bit claim.activeRows rowIndex hactive
        have houtcome := nodeRowValid_of_word claims identifier claim centre remaining
          pairState (rowIndex.val / 5) rowIndex.val hword hrowMember
        let nextAssignments := (centre, choice.rowMask) :: assignments
        let nextCode := addRowCode claim.code choice.rowMask centre
        let nextPairState := pairState.add choice.pairMask
        have hnextAssignments : AssignmentsMatch Q nextAssignments :=
          hassignments.cons centre choice.rowMask
            (by simpa only [choice] using hrow)
        have hnextCode : CodeMatches nextCode nextAssignments := by
          exact hcode.add centre choice.rowMask
        have hnextPair : nextPairState.Exact nextAssignments := by
          exact hpair.add centre choice.rowMask choice.pairMask
            (by simpa only [choice] using searchRowChoiceAt_pairMask centre rowIndex)
        have hnextCentres : (nextAssignments.map Prod.fst).Perm
            (assignedCentres (claim.depth + 1)) := by
          change (centre :: assignments.map Prod.fst).Perm _
          exact (hcentres.cons centre).trans
            (nextAssignedCentres_perm claim.depth hdepth)
        change (if bitSetB claim.patternRows rowIndex.val = true then
            ∃ patternIdentifier,
              patternIdentifierPackedMatchesB patternIdentifier nextCode = true
          else if remaining.isEmpty = true then
            ∃ hardIdentifier,
              hardIdentifierPackedMatchesB hardIdentifier nextCode = true
          else
            ∃ childId,
              let child := claims.nodeAt childId
              (decide (childId < identifier) &&
                decide (childId < claims.nodeCount) &&
                (child.depth == claim.depth + 1) &&
                (child.code == nextCode) &&
                (child.pairOnce == nextPairState.seenOnce) &&
                (child.pairTwice == nextPairState.seenTwice)) = true) at houtcome
        by_cases hpattern : bitSetB claim.patternRows rowIndex.val = true
        · rw [if_pos hpattern] at houtcome
          obtain ⟨patternIdentifier, hpatternMatch⟩ := houtcome
          exact impossible_of_patternIdentifier audits hC hR hnextAssignments
            hnextCode hpatternMatch
        · rw [if_neg hpattern] at houtcome
          by_cases hleaf : remaining.isEmpty = true
          · rw [if_pos hleaf] at houtcome
            obtain ⟨hardIdentifier, hhardMatch⟩ := houtcome
            have hnextAll : (nextAssignments.map Prod.fst ++ remaining).Perm
                (List.finRange 8) := by
              have hdepthNext : claim.depth + 1 ≤ searchCentres.length :=
                Nat.succ_le_iff.mpr hdepth
              have htotal := assignedCentres_remaining_perm (claim.depth + 1)
                hdepthNext
              exact (hnextCentres.append_right remaining).trans
                (by simpa only [remaining] using htotal)
            have hremainingEmpty : remaining = [] := by
              simpa using hleaf
            have hfull : (nextAssignments.map Prod.fst).Perm
                (List.finRange 8) := by
              simpa only [hremainingEmpty, List.append_nil] using hnextAll
            exact impossible_of_hardIdentifier audits hC hR hfull
              hnextAssignments hnextCode hhardMatch
          · rw [if_neg hleaf] at houtcome
            obtain ⟨childId, hchildValid⟩ := houtcome
            let child := claims.nodeAt childId
            have hchildParts : (((((childId < identifier ∧
                childId < claims.nodeCount) ∧
                child.depth = claim.depth + 1) ∧ child.code = nextCode) ∧
                child.pairOnce = nextPairState.seenOnce) ∧
                child.pairTwice = nextPairState.seenTwice) := by
              simpa only [child, Bool.and_eq_true, decide_eq_true_eq,
                beq_iff_eq] using hchildValid
            rcases hchildParts with
              ⟨⟨⟨⟨⟨hchildEarlier, hchildBound⟩, hchildDepth⟩,
                hchildCode⟩, hchildOnce⟩, hchildTwice⟩
            apply hinduction childId hchildEarlier hchildBound nextAssignments
            · change (nextAssignments.map Prod.fst).Perm
                (assignedCentres child.depth)
              rw [hchildDepth]
              exact hnextCentres
            · exact hnextAssignments
            · change CodeMatches child.code nextAssignments
              rw [hchildCode]
              exact hnextCode
            · change (PairState.mk child.pairOnce child.pairTwice).Exact
                nextAssignments
              simpa [hchildOnce, hchildTwice, nextPairState] using hnextPair
      · have hwordIndex := rowIndex_wordIndex_mem_range rowIndex
        have hword := hrejectedWords (rowIndex.val / 5) hwordIndex
        have hrowMember := rowIndex_mem_word_of_bit claim.rejectedRows rowIndex
          hrejected
        have hrejectedOutcome := rejectedRowValid_of_word claim centre remaining
          (rowIndexWord claim.rejectedRows (5 * (rowIndex.val / 5)))
          (claim.rejectionTargetGroups.getD (rowIndex.val / 5) []) rowIndex.val
          hword hrowMember
        exact impossible_of_rejectedRow hBalanced hdepth hcentres hassignments
          hcode rfl hrow hrejectedOutcome rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
