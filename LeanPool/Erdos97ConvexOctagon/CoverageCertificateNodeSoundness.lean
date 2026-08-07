/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness
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

private theorem impossible_of_patternIdentifier
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

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
