/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateNodeSoundness
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateValidity
import LeanPool.Erdos97ConvexOctagon.RowSymmetry

/-! # Soundness of the exhaustive coverage-certificate manifest -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private theorem coverageBranchClaim_search_locallyValid_orbit0
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 0 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim

private theorem coverageBranchClaim_search_locallyValid_orbit1
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 1 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_1_04
  · cases hclaim
    exact coverageBranchLocallyValid_1_05
  · cases hclaim
    exact coverageBranchLocallyValid_1_06
  · cases hclaim
    exact coverageBranchLocallyValid_1_07
  · cases hclaim
    exact coverageBranchLocallyValid_1_08
  · cases hclaim
    exact coverageBranchLocallyValid_1_09
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_1_16
  · cases hclaim
    exact coverageBranchLocallyValid_1_17
  · cases hclaim
    exact coverageBranchLocallyValid_1_18
  · cases hclaim
    exact coverageBranchLocallyValid_1_19
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_1_26
  · cases hclaim
    exact coverageBranchLocallyValid_1_27
  · cases hclaim
    exact coverageBranchLocallyValid_1_28
  · cases hclaim
    exact coverageBranchLocallyValid_1_29
  · cases hclaim
    exact coverageBranchLocallyValid_1_30
  · cases hclaim
    exact coverageBranchLocallyValid_1_31
  · cases hclaim
    exact coverageBranchLocallyValid_1_32
  · cases hclaim
    exact coverageBranchLocallyValid_1_33
  · cases hclaim
    exact coverageBranchLocallyValid_1_34

private theorem coverageBranchClaim_search_locallyValid_orbit2
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 2 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_2_01
  · cases hclaim
    exact coverageBranchLocallyValid_2_02
  · cases hclaim
    exact coverageBranchLocallyValid_2_03
  · cases hclaim
    exact coverageBranchLocallyValid_2_04
  · cases hclaim
    exact coverageBranchLocallyValid_2_05
  · cases hclaim
    exact coverageBranchLocallyValid_2_06
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_2_08
  · cases hclaim
    exact coverageBranchLocallyValid_2_09
  · cases hclaim
    exact coverageBranchLocallyValid_2_10
  · cases hclaim
    exact coverageBranchLocallyValid_2_11
  · cases hclaim
    exact coverageBranchLocallyValid_2_12
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_2_14
  · cases hclaim
    exact coverageBranchLocallyValid_2_15
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_2_17
  · cases hclaim
    exact coverageBranchLocallyValid_2_18
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_2_23
  · cases hclaim
    exact coverageBranchLocallyValid_2_24
  · cases hclaim
    exact coverageBranchLocallyValid_2_25
  · cases hclaim
    exact coverageBranchLocallyValid_2_26
  · cases hclaim
    exact coverageBranchLocallyValid_2_27
  · cases hclaim
    exact coverageBranchLocallyValid_2_28
  · cases hclaim
    exact coverageBranchLocallyValid_2_29
  · cases hclaim
    exact coverageBranchLocallyValid_2_30
  · cases hclaim
    exact coverageBranchLocallyValid_2_31
  · cases hclaim
    exact coverageBranchLocallyValid_2_32
  · cases hclaim
    exact coverageBranchLocallyValid_2_33
  · cases hclaim
    exact coverageBranchLocallyValid_2_34

private theorem coverageBranchClaim_search_locallyValid_orbit3
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 3 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_3_01
  · cases hclaim
    exact coverageBranchLocallyValid_3_02
  · cases hclaim
    exact coverageBranchLocallyValid_3_03
  · cases hclaim
    exact coverageBranchLocallyValid_3_04
  · cases hclaim
    exact coverageBranchLocallyValid_3_05
  · cases hclaim
    exact coverageBranchLocallyValid_3_06
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_3_10
  · cases hclaim
    exact coverageBranchLocallyValid_3_11
  · cases hclaim
    exact coverageBranchLocallyValid_3_12
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_3_23
  · cases hclaim
    exact coverageBranchLocallyValid_3_24
  · cases hclaim
    exact coverageBranchLocallyValid_3_25
  · cases hclaim
    exact coverageBranchLocallyValid_3_26
  · cases hclaim
    exact coverageBranchLocallyValid_3_27
  · cases hclaim
    exact coverageBranchLocallyValid_3_28
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_3_30
  · cases hclaim
    exact coverageBranchLocallyValid_3_31
  · cases hclaim
    exact coverageBranchLocallyValid_3_32
  · cases hclaim
  · cases hclaim

private theorem coverageBranchClaim_search_locallyValid_orbit4
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 4 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim

private theorem coverageBranchClaim_search_locallyValid_orbit5
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 5 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_5_04
  · cases hclaim
    exact coverageBranchLocallyValid_5_05
  · cases hclaim
    exact coverageBranchLocallyValid_5_06
  · cases hclaim
    exact coverageBranchLocallyValid_5_07
  · cases hclaim
    exact coverageBranchLocallyValid_5_08
  · cases hclaim
    exact coverageBranchLocallyValid_5_09
  · cases hclaim
    exact coverageBranchLocallyValid_5_10
  · cases hclaim
    exact coverageBranchLocallyValid_5_11
  · cases hclaim
    exact coverageBranchLocallyValid_5_12
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_5_14
  · cases hclaim
    exact coverageBranchLocallyValid_5_15
  · cases hclaim
    exact coverageBranchLocallyValid_5_16
  · cases hclaim
    exact coverageBranchLocallyValid_5_17
  · cases hclaim
    exact coverageBranchLocallyValid_5_18
  · cases hclaim
    exact coverageBranchLocallyValid_5_19
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_5_24
  · cases hclaim
    exact coverageBranchLocallyValid_5_25
  · cases hclaim
    exact coverageBranchLocallyValid_5_26
  · cases hclaim
    exact coverageBranchLocallyValid_5_27
  · cases hclaim
    exact coverageBranchLocallyValid_5_28
  · cases hclaim
    exact coverageBranchLocallyValid_5_29
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_5_31
  · cases hclaim
    exact coverageBranchLocallyValid_5_32
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_5_34

private theorem coverageBranchClaim_search_locallyValid_orbit6
    (rowTwo : Fin 35) {claims : BranchClaims}
    (hclaim : coverageBranchClaim 6 rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases rowTwo
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_6_01
  · cases hclaim
    exact coverageBranchLocallyValid_6_02
  · cases hclaim
    exact coverageBranchLocallyValid_6_03
  · cases hclaim
    exact coverageBranchLocallyValid_6_04
  · cases hclaim
    exact coverageBranchLocallyValid_6_05
  · cases hclaim
    exact coverageBranchLocallyValid_6_06
  · cases hclaim
    exact coverageBranchLocallyValid_6_07
  · cases hclaim
    exact coverageBranchLocallyValid_6_08
  · cases hclaim
    exact coverageBranchLocallyValid_6_09
  · cases hclaim
    exact coverageBranchLocallyValid_6_10
  · cases hclaim
    exact coverageBranchLocallyValid_6_11
  · cases hclaim
    exact coverageBranchLocallyValid_6_12
  · cases hclaim
    exact coverageBranchLocallyValid_6_13
  · cases hclaim
    exact coverageBranchLocallyValid_6_14
  · cases hclaim
    exact coverageBranchLocallyValid_6_15
  · cases hclaim
    exact coverageBranchLocallyValid_6_16
  · cases hclaim
    exact coverageBranchLocallyValid_6_17
  · cases hclaim
    exact coverageBranchLocallyValid_6_18
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_6_23
  · cases hclaim
    exact coverageBranchLocallyValid_6_24
  · cases hclaim
    exact coverageBranchLocallyValid_6_25
  · cases hclaim
    exact coverageBranchLocallyValid_6_26
  · cases hclaim
    exact coverageBranchLocallyValid_6_27
  · cases hclaim
    exact coverageBranchLocallyValid_6_28
  · cases hclaim
  · cases hclaim
    exact coverageBranchLocallyValid_6_30
  · cases hclaim
    exact coverageBranchLocallyValid_6_31
  · cases hclaim
    exact coverageBranchLocallyValid_6_32
  · cases hclaim
  · cases hclaim

/-- Every search claim selected by the complete manifest has all local node audits. -/
theorem coverageBranchClaim_search_locallyValid
    {orbit : Fin 7} {rowTwo : Fin 35} {claims : BranchClaims}
    (hclaim : coverageBranchClaim orbit rowTwo = .search claims) :
    claims.LocallyValid := by
  fin_cases orbit
  · exact coverageBranchClaim_search_locallyValid_orbit0 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit1 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit2 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit3 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit4 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit5 rowTwo hclaim
  · exact coverageBranchClaim_search_locallyValid_orbit6 rowTwo hclaim

/-- Semantic validity accessors for every generated certificate table. -/
theorem coverageCertificateAudits : CertificateAudits where
  coverValid := conflictCoverAt?_valid
  patternValid := densePatternSummaryAt?_valid
  hardValid := denseHardSummaryAt?_valid

private theorem searchBranchRootFacts_of_valid
    (orbit : Fin 7) (rowTwo : Fin 35) (claims : BranchClaims)
    (hvalid : searchBranchRootValidB orbit rowTwo claims = true) :
    claims.rootId < claims.nodeCount ∧
      let root := claims.nodeAt claims.rootId
      let expected := addRowCode
        (addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1)
        (rowTwoMask rowTwo) 2
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let choice2 := searchChoiceForRow 2 (rowTwoMask rowTwo)
      let pairState := ((PairState.empty.add choice0.pairMask).add
        choice1.pairMask).add choice2.pairMask
      (((root.depth = 0 ∧ root.code = expected) ∧
        root.pairOnce = pairState.seenOnce) ∧
        root.pairTwice = pairState.seenTwice) := by
  unfold searchBranchRootValidB at hvalid
  split at hvalid
  next hrootBound =>
    refine ⟨hrootBound, ?_⟩
    simpa only [Bool.and_eq_true, beq_iff_eq] using hvalid
  next => simp at hvalid

/-- A root-audited branch claim and its local search audits contradict the
corresponding realised fixed-row branch. -/
theorem branchClaim_impossible
    (audits : CertificateAudits)
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (rowTwo : Fin 35)
    (hrowTwo : Q.targets 2 = packedRow (rowTwoMask rowTwo))
    (claim : BranchClaim)
    (hroot : branchClaimRootValidB orbit rowTwo claim = true)
    (hlocally : ∀ claims, claim = .search claims → claims.LocallyValid) : False := by
  let codeTwo := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  cases claim with
  | patternTwo patternIdentifier =>
      change patternIdentifierPackedMatchesB patternIdentifier codeTwo = true at hroot
      exact impossible_of_patternIdentifier audits hC hR
        (initialAssignmentsMatch hN orbit hrowOne)
        (initialCodeMatches orbit) hroot
  | patternThree patternIdentifier =>
      let codeThree := addRowCode codeTwo (rowTwoMask rowTwo) 2
      have hpattern :
          patternIdentifierPackedMatchesB patternIdentifier codeThree = true := by
        change (_ && _ &&
          patternIdentifierPackedMatchesB patternIdentifier codeThree) = true at hroot
        rw [Bool.and_eq_true, Bool.and_eq_true] at hroot
        exact hroot.2
      exact impossible_of_patternIdentifier audits hC hR
        (initialAssignmentsMatchThree hN orbit hrowOne rowTwo hrowTwo)
        (initialCodeMatchesThree orbit rowTwo) hpattern
  | search claims =>
      have hsearchRoot : searchBranchRootValidB orbit rowTwo claims = true := by
        change (_ && _ && searchBranchRootValidB orbit rowTwo claims) = true at hroot
        rw [Bool.and_eq_true, Bool.and_eq_true] at hroot
        exact hroot.2
      obtain ⟨hrootBound, hrootFields⟩ :=
        searchBranchRootFacts_of_valid orbit rowTwo claims hsearchRoot
      let root := claims.nodeAt claims.rootId
      let expected := addRowCode
        (addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1)
        (rowTwoMask rowTwo) 2
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let choice2 := searchChoiceForRow 2 (rowTwoMask rowTwo)
      let pairState := ((PairState.empty.add choice0.pairMask).add
        choice1.pairMask).add choice2.pairMask
      change (((root.depth = 0 ∧ root.code = expected) ∧
        root.pairOnce = pairState.seenOnce) ∧
        root.pairTwice = pairState.seenTwice) at hrootFields
      rcases hrootFields with
        ⟨⟨⟨hrootDepth, hrootCode⟩, hrootOnce⟩, hrootTwice⟩
      let assignments : List RowAssignment :=
        [(2, rowTwoMask rowTwo), (1, canonicalRowMask orbit), (0, 30)]
      apply BranchClaims.node_impossible audits hC hR hSparse hBalanced claims
        (hlocally claims rfl) claims.rootId hrootBound assignments
      · change (assignments.map Prod.fst).Perm (assignedCentres root.depth)
        rw [hrootDepth]
        simpa [assignments, assignedCentres] using
          (by decide : ([2, 1, 0] : List Vertex).Perm [0, 1, 2])
      · exact initialAssignmentsMatchThree hN orbit hrowOne rowTwo hrowTwo
      · change CodeMatches root.code assignments
        rw [hrootCode]
        exact initialCodeMatchesThree orbit rowTwo
      · change (PairState.mk root.pairOnce root.pairTwice).Exact assignments
        simpa [hrootOnce, hrootTwice, pairState, choice0, choice1, choice2]
          using initialPairStateExactThree orbit rowTwo

/-- The generated claim for one fixed canonical branch is semantically impossible. -/
theorem coverageBranchClaim_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (rowTwo : Fin 35)
    (hrowTwo : Q.targets 2 = packedRow (rowTwoMask rowTwo)) : False := by
  apply branchClaim_impossible coverageCertificateAudits hC hR hN hSparse
    hBalanced orbit hrowOne rowTwo hrowTwo (coverageBranchClaim orbit rowTwo)
    (coverageBranchClaim_root_valid orbit rowTwo)
  intro claims hclaim
  exact coverageBranchClaim_search_locallyValid hclaim

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

namespace Erdos97Octagon.RawIncidence

/-- The exhaustive flat certificate excludes every normalized branch with a
canonical first row. -/
theorem coverageCanonicalBranch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (rowOneIndex : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask rowOneIndex)) : False := by
  obtain ⟨rowTwo, hrowTwo⟩ := exists_rowTwoIndex Q
  exact StaticDirectCoverage.coverageBranchClaim_impossible hC hR hN hSparse
    hBalanced rowOneIndex hrowOne rowTwo hrowTwo

end Erdos97Octagon.RawIncidence
