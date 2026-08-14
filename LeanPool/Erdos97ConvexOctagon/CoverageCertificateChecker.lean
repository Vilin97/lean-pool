/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSummaries
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers
import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoices
import LeanPool.Erdos97ConvexOctagon.CoverageSearchCore
import LeanPool.Erdos97ConvexOctagon.RowMasks

/-! # Flat local checker for coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Witness streams for one nonempty five-row word of a node claim. -/
structure NodeWordClaim where
  /-- Index of the consecutive five-row word. -/
  wordIndex : Nat
  /-- One semantic column-conflict target for every rejected row. -/
  rejectionTargets : List Nat
  /-- Pattern origins for active rows covered by patterns. -/
  patternOrigins : List Nat
  /-- Recursive child identifiers for active rows that continue the search. -/
  childIds : List Nat
  /-- Exact hard origins for active rows at the final depth. -/
  hardOrigins : List Nat

/-- One postorder DFS node; child identifiers must point to earlier nodes. -/
structure NodeClaim where
  /-- Number of noncanonical search rows already assigned. -/
  depth : Nat
  /-- Packed partial incidence table at this node. -/
  code : UInt64
  /-- Pairs selected by at least one assigned row. -/
  pairOnce : UInt64
  /-- Pairs selected by at least two assigned rows. -/
  pairTwice : UInt64
  /-- Dense identifier of a globally audited repeated-pair row-mask cover. -/
  conflictCoverId : Nat
  /-- Row indices whose pair and column guards both survive. -/
  activeRows : UInt64
  /-- Pair-compatible row indices rejected by the semantic column guard. -/
  rejectedRows : UInt64
  /-- Legal-row indices stopped by pattern origins. -/
  patternRows : UInt64
  /-- Nonempty witness streams, grouped by consecutive five-row words. -/
  wordClaims : Array NodeWordClaim

/-- Flat postorder claims for one fixed branch. -/
structure BranchClaims where
  /-- Every locally checked node in shallow 64-entry groups, children before parents. -/
  nodeGroups : Array (Array NodeClaim)
  /-- Total number of nodes across all groups. -/
  nodeCount : Nat
  /-- Identifier of the branch root. -/
  rootId : Nat

/-- A fixed branch closes immediately by a pattern, or by a flat search certificate. -/
inductive BranchClaim where
  /-- A pattern covers the first two fixed rows. -/
  | patternTwo (patternIdentifier : Nat)
  /-- A pattern covers all three fixed rows. -/
  | patternThree (patternIdentifier : Nat)
  /-- The five remaining rows are covered by postorder local claims. -/
  | search (claims : BranchClaims)

private def defaultNodeClaim : NodeClaim :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, #[]⟩

private def emptyNodeWordClaim (wordIndex : Nat) : NodeWordClaim :=
  ⟨wordIndex, [], [], [], []⟩

private def nodeWordClaimAtAux
  (wordClaims : Array NodeWordClaim) (wordIndex position : Nat) :
    Nat → NodeWordClaim
  | 0 => emptyNodeWordClaim wordIndex
  | fuel + 1 =>
      match wordClaims[position]? with
      | none => emptyNodeWordClaim wordIndex
      | some wordClaim =>
          if wordClaim.wordIndex = wordIndex then wordClaim
          else nodeWordClaimAtAux wordClaims wordIndex (position + 1) fuel

/-- Retrieve one of at most seven sparse word claims, defaulting to empty streams. -/
def NodeClaim.wordAt (claim : NodeClaim) (wordIndex : Nat) : NodeWordClaim :=
  nodeWordClaimAtAux claim.wordClaims wordIndex 0 7

/-- Retrieve one node without unfolding an entire large flat array literal. -/
def BranchClaims.nodeAt (claims : BranchClaims) (identifier : Nat) : NodeClaim :=
  (claims.nodeGroups.getD (identifier / 64) #[]).getD (identifier % 64)
    defaultNodeClaim

/-- Read one row byte from a packed incidence-table code. -/
def rowFromCode (code : UInt64) (centre : Vertex) : UInt64 :=
  (code >>> UInt64.ofNat (8 * centre.val)) &&& 255

/-- Assigned centres at one search depth. -/
def assignedCentres (depth : Nat) : List Vertex :=
  [0, 1, 2] ++ searchCentres.take depth

/-- Reconstruct the semantic assignment prefix from a code and search depth. -/
def assignmentsFromCode (code : UInt64) (depth : Nat) : List RowAssignment :=
  (assignedCentres depth).map fun centre => (centre, rowFromCode code centre)

/-- Reconstruct the packed pair state from the semantic assignment prefix. -/
def pairStateFromAssignments (assignments : List RowAssignment) : PairState :=
  assignments.foldl (fun state assignment =>
    state.add (searchChoiceForRow assignment.1 assignment.2).pairMask) PairState.empty

/-- Reconstruct the packed column state from the semantic assignment prefix. -/
def columnStateFromAssignments (assignments : List RowAssignment) : ColumnState :=
  assignments.foldl (fun state assignment => state.add assignment.2) ColumnState.empty

private structure LocalCursor where
  ok : Bool
  patternOrigins : List Nat
  childIds : List Nat
  hardOrigins : List Nat

private structure RejectionCursor where
  ok : Bool
  targets : List Nat

private theorem foldl_fixed_of_false
    {State Item : Type} (step : State → Item → State) (ok : State → Bool)
    (hsticky : ∀ state item, ok state = false → step state item = state)
    (items : List Item) {state : State} (hfalse : ok state = false) :
    items.foldl step state = state := by
  induction items generalizing state with
  | nil => rfl
  | cons item items induction =>
      rw [List.foldl_cons, hsticky state item hfalse]
      exact induction hfalse

private theorem foldl_good_of_final
    {State Item : Type} (step : State → Item → State) (ok : State → Bool)
    (Good : Item → Prop)
    (hsticky : ∀ state item, ok state = false → step state item = state)
    (hgood : ∀ state item, ok (step state item) = true → Good item)
    {items : List Item} {initial : State}
    (hfinal : ok (items.foldl step initial) = true)
    {item : Item} (hitem : item ∈ items) : Good item := by
  induction items generalizing initial with
  | nil => simp at hitem
  | cons head tail induction =>
      rw [List.foldl_cons] at hfinal
      have hstep : ok (step initial head) = true := by
        cases hvalue : ok (step initial head) with
        | false =>
            have hfixed := foldl_fixed_of_false step ok hsticky tail hvalue
            rw [hfixed, hvalue] at hfinal
            contradiction
        | true => rfl
      rcases List.mem_cons.mp hitem with hhead | htail
      · subst item
        exact hgood initial head hstep
      · exact induction hfinal htail

/-- Constant-depth lookup of one compact pattern-summary identifier. -/
def densePatternSummaryLookup (identifier : Nat) : Option PatternSummary :=
  match densePatternSummaryGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

/-- Constant-depth lookup of one compact exact-summary identifier. -/
def denseHardSummaryLookup (identifier : Nat) : Option HardSummary :=
  match denseHardSummaryGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

/-- Packed-only pattern-summary validation for the first computation gate. -/
def patternIdentifierPackedMatchesB
    (identifier : Nat) (code : UInt64) : Bool :=
  match densePatternSummaryLookup identifier with
  | none => false
  | some summary => (summary.mask &&& code) == summary.mask

/-- Packed-only exact-summary validation for the first computation gate. -/
def hardIdentifierPackedMatchesB (identifier : Nat) (code : UInt64) : Bool :=
  match denseHardSummaryLookup identifier with
  | none => false
  | some summary => summary.code == code

/-- Selected row indices in one fixed five-index word. -/
def rowIndexWord (rows : UInt64) (offset : Nat) : List Nat :=
  let word := ((rows >>> UInt64.ofNat offset) &&& 31).toNat
  (fiveBitIndices.getD word []).map fun index => offset + index

/-- Retrieve one conflict cover without unfolding the full generated table. -/
def conflictCoverLookup (identifier : Nat) : Option ConflictCover :=
  match conflictCoverGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

private def processRow
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (cursor : LocalCursor) (index : Nat) : LocalCursor :=
  if !cursor.ok then cursor
  else
    let choice := (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩
    let nextCode := addRowCode claim.code choice.rowMask centre
    let nextPairState := pairState.add choice.pairMask
    if bitSetB claim.patternRows index then
      match cursor.patternOrigins with
      | [] => ⟨false, [], cursor.childIds, cursor.hardOrigins⟩
      | patternIdentifier :: patternIdentifiers =>
          ⟨patternIdentifierPackedMatchesB patternIdentifier nextCode,
            patternIdentifiers, cursor.childIds, cursor.hardOrigins⟩
    else if remaining.isEmpty then
      match cursor.hardOrigins with
      | [] => ⟨false, cursor.patternOrigins, cursor.childIds, []⟩
      | hardIdentifier :: hardIdentifiers =>
          ⟨hardIdentifierPackedMatchesB hardIdentifier nextCode,
            cursor.patternOrigins, cursor.childIds, hardIdentifiers⟩
    else
      match cursor.childIds with
      | [] => ⟨false, cursor.patternOrigins, [], cursor.hardOrigins⟩
      | childId :: childIds =>
          let child := claims.nodeAt childId
          let childValid := decide (childId < identifier) &&
            decide (childId < claims.nodeCount) &&
            (child.depth == claim.depth + 1) && (child.code == nextCode) &&
            (child.pairOnce == nextPairState.seenOnce) &&
            (child.pairTwice == nextPairState.seenTwice)
          ⟨childValid, cursor.patternOrigins, childIds, cursor.hardOrigins⟩

/-- Process at most five compatible rows while threading the local witness streams. -/
private def processFiveRows
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (indices : List Nat) (initial : LocalCursor) : LocalCursor :=
  indices.foldl
    (processRow claims identifier claim centre remaining pairState) initial

/-- Semantic consequence recorded for one active legal-row index. -/
def NodeRowValid
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (index : Nat) : Prop :=
  let choice := (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩
  let nextCode := addRowCode claim.code choice.rowMask centre
  let nextPairState := pairState.add choice.pairMask
  if bitSetB claim.patternRows index = true then
    ∃ patternIdentifier,
      patternIdentifierPackedMatchesB patternIdentifier nextCode = true
  else if remaining.isEmpty = true then
    ∃ hardIdentifier,
      hardIdentifierPackedMatchesB hardIdentifier nextCode = true
  else
    ∃ childId,
      let child := claims.nodeAt childId
      (decide (childId < identifier) && decide (childId < claims.nodeCount) &&
        (child.depth == claim.depth + 1) && (child.code == nextCode) &&
        (child.pairOnce == nextPairState.seenOnce) &&
        (child.pairTwice == nextPairState.seenTwice)) = true

private theorem nodeRowValid_of_processRow_ok
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (cursor : LocalCursor) (index : Nat)
    (hok : (processRow claims identifier claim centre remaining pairState
      cursor index).ok = true) :
    NodeRowValid claims identifier claim centre remaining pairState index := by
  by_cases hcursor : cursor.ok = true
  · by_cases hpattern : bitSetB claim.patternRows index = true
    · cases horigins : cursor.patternOrigins with
      | nil => simp [processRow, hcursor, hpattern, horigins] at hok
      | cons patternIdentifier patternIdentifiers =>
          simp only [NodeRowValid, hpattern, ite_eq_left]
          refine ⟨patternIdentifier, ?_⟩
          simpa [processRow, hcursor, hpattern, horigins] using hok
    · have hpatternFalse := Bool.eq_false_of_not_eq_true hpattern
      by_cases hremaining : remaining.isEmpty = true
      · cases horigins : cursor.hardOrigins with
        | nil =>
            simp [processRow, hcursor, hpatternFalse, hremaining, horigins] at hok
        | cons hardIdentifier hardIdentifiers =>
            simp only [NodeRowValid, hpatternFalse, hremaining, ite_eq_left]
            refine ⟨hardIdentifier, ?_⟩
            simpa [processRow, hcursor, hpatternFalse, hremaining,
              horigins] using hok
      · have hremainingFalse := Bool.eq_false_of_not_eq_true hremaining
        cases hchildren : cursor.childIds with
        | nil =>
            simp [processRow, hcursor, hpatternFalse, hremainingFalse,
              hchildren] at hok
        | cons childId childIds =>
            simp only [NodeRowValid, hpatternFalse, hremainingFalse]
            refine ⟨childId, ?_⟩
            simpa [processRow, hcursor, hpatternFalse,
              hremainingFalse, hchildren] using hok
  · have hcursorFalse := Bool.eq_false_of_not_eq_true hcursor
    simp [processRow, hcursorFalse] at hok

/-- Validate one of the seven disjoint five-row words of a node claim. -/
def nodeWordValidB
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (wordIndex : Nat) : Bool :=
  let wordClaim := claim.wordAt wordIndex
  let initial : LocalCursor :=
    ⟨true, wordClaim.patternOrigins, wordClaim.childIds,
      wordClaim.hardOrigins⟩
  let result := processFiveRows claims identifier claim centre remaining pairState
    (rowIndexWord claim.activeRows (5 * wordIndex)) initial
  result.ok && result.patternOrigins.isEmpty && result.childIds.isEmpty &&
    result.hardOrigins.isEmpty

/-- Every active index accepted by one compact word has its recorded outcome. -/
theorem nodeRowValid_of_word
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (wordIndex index : Nat)
    (hword : nodeWordValidB claims identifier claim centre remaining pairState
      wordIndex = true)
    (hindex : index ∈ rowIndexWord claim.activeRows (5 * wordIndex)) :
    NodeRowValid claims identifier claim centre remaining pairState index := by
  simp only [nodeWordValidB, Bool.and_eq_true] at hword
  apply foldl_good_of_final
    (processRow claims identifier claim centre remaining pairState)
    LocalCursor.ok
    (NodeRowValid claims identifier claim centre remaining pairState)
  · intro cursor item hcursor
    simp [processRow, hcursor]
  · exact nodeRowValid_of_processRow_ok claims identifier claim centre
      remaining pairState
  · exact hword.1.1.1
  · exact hindex

/-- Validate one semantically rejected row of a node claim. -/
def rejectedRowValidB
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (index target : Nat) : Bool :=
  if htarget : target < 8 then
    let targetVertex : Vertex := ⟨target, htarget⟩
    let choice := (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩
    let assignments :=
      (centre, choice.rowMask) :: assignmentsFromCode claim.code claim.depth
    let count := assignmentColumnCount assignments targetVertex
    decide (4 < count) ||
      decide (count + remainingColumnCapacity remaining targetVertex < 4)
  else false

private def processRejectedRow
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (cursor : RejectionCursor) (index : Nat) : RejectionCursor :=
  if !cursor.ok then cursor
  else
    match cursor.targets with
    | [] => ⟨false, []⟩
    | target :: remainingTargets =>
        ⟨rejectedRowValidB claim centre remaining index target,
          remainingTargets⟩

/-- Validate at most five rejected rows using one semantic conflict each. -/
def rejectedWordValidB
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (indices targets : List Nat) : Bool :=
  let initial : RejectionCursor := ⟨true, targets⟩
  let result := indices.foldl (processRejectedRow claim centre remaining) initial
  result.ok && result.targets.isEmpty

/-- Semantic column-conflict consequence recorded for one rejected row. -/
def RejectedRowValid
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (index : Nat) : Prop :=
  ∃ target, rejectedRowValidB claim centre remaining index target = true

private theorem rejectedRowValid_of_process_ok
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (cursor : RejectionCursor) (index : Nat)
    (hok : (processRejectedRow claim centre remaining cursor index).ok = true) :
    RejectedRowValid claim centre remaining index := by
  by_cases hcursor : cursor.ok = true
  · cases htargets : cursor.targets with
    | nil => simp [processRejectedRow, hcursor, htargets] at hok
    | cons target targets =>
        exact ⟨target, by simpa [processRejectedRow, hcursor, htargets] using hok⟩
  · have hcursorFalse := Bool.eq_false_of_not_eq_true hcursor
    simp [processRejectedRow, hcursorFalse] at hok

/-- Every rejected index accepted by one compact word has a semantic conflict. -/
theorem rejectedRowValid_of_word
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (indices targets : List Nat) (index : Nat)
    (hword : rejectedWordValidB claim centre remaining indices targets = true)
    (hindex : index ∈ indices) : RejectedRowValid claim centre remaining index := by
  simp only [rejectedWordValidB, Bool.and_eq_true] at hword
  apply foldl_good_of_final
    (processRejectedRow claim centre remaining)
    RejectionCursor.ok (RejectedRowValid claim centre remaining)
  · intro cursor item hcursor
    simp [processRejectedRow, hcursor]
  · exact rejectedRowValid_of_process_ok claim centre remaining
  · exact hword.1
  · exact hindex

/-- Validate the conservative pair/column row partition of one node. -/
def nodePruningValidB (claims : BranchClaims) (identifier : Nat) : Bool :=
  if identifier < claims.nodeCount then
    let claim := claims.nodeAt identifier
    if claim.depth < searchCentres.length then
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      match conflictCoverLookup claim.conflictCoverId with
      | none => false
      | some cover =>
          let incompatible := cover.incompatibleRows
          let inactive := claim.rejectedRows ||| incompatible
          let legalRows : UInt64 := 34359738367
          if cover.centre != centre.val ||
              (cover.requiredPairs &&& claim.pairTwice) != cover.requiredPairs ||
              (claim.patternRows &&& claim.activeRows) != claim.patternRows ||
              (claim.rejectedRows &&& incompatible) != 0 ||
              (claim.activeRows &&& inactive) != 0 ||
              (claim.activeRows ||| inactive) != legalRows then false
          else
            (List.range 7).all fun wordIndex =>
              let wordClaim := claim.wordAt wordIndex
              rejectedWordValidB claim centre remaining
                  (rowIndexWord claim.rejectedRows (5 * wordIndex))
                  wordClaim.rejectionTargets
    else false
  else false

/-- Validate the active row outcomes and child-state transitions of one node. -/
def nodeTransitionsValidB (claims : BranchClaims) (identifier : Nat) : Bool :=
  if identifier < claims.nodeCount then
    let claim := claims.nodeAt identifier
    if claim.depth < searchCentres.length then
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      let pairState : PairState := ⟨claim.pairOnce, claim.pairTwice⟩
      (List.range 7).all fun wordIndex =>
        nodeWordValidB claims identifier claim centre remaining pairState wordIndex
    else false
  else false

/-- Fail-closed local validation of one postorder node. -/
def nodeLocalValidB (claims : BranchClaims) (identifier : Nat) : Bool :=
  nodePruningValidB claims identifier && nodeTransitionsValidB claims identifier

/-- Validate a bounded consecutive chunk of postorder node identifiers. -/
def nodeClaimChunkValidB
    (claims : BranchClaims) (start count : Nat) : Bool :=
  (List.range count).all fun offset => nodeLocalValidB claims (start + offset)

/-- Every node in a flat branch passes its local checker. -/
def BranchClaims.LocallyValid (claims : BranchClaims) : Prop :=
  ∀ identifier, identifier < claims.nodeCount →
    nodeLocalValidB claims identifier = true

/-- Extract one local node fact from a bounded chunk audit. -/
theorem nodeLocalValid_of_chunk
    {claims : BranchClaims} {start count identifier : Nat}
    (haudit : nodeClaimChunkValidB claims start count = true)
    (hlower : start ≤ identifier) (hupper : identifier < start + count) :
    nodeLocalValidB claims identifier = true := by
  have hoffset : identifier - start < count := by omega
  have hmember : identifier - start ∈ List.range count :=
    List.mem_range.mpr hoffset
  have hvalid := (List.all_eq_true.mp haudit) (identifier - start) hmember
  simpa [Nat.add_sub_of_le hlower] using hvalid

/-- Validate only row-partition facts in a bounded node chunk. -/
def nodePruningChunkValidB
    (claims : BranchClaims) (start count : Nat) : Bool :=
  (List.range count).all fun offset => nodePruningValidB claims (start + offset)

/-- Validate only active transitions in a bounded node chunk. -/
def nodeTransitionsChunkValidB
    (claims : BranchClaims) (start count : Nat) : Bool :=
  (List.range count).all fun offset => nodeTransitionsValidB claims (start + offset)

/-- Validate all postorder claims in bounded 64-node blocks. -/
def allNodeClaimsValidB (claims : BranchClaims) : Bool :=
  let blockCount := (claims.nodeCount + 63) / 64
  (List.range blockCount).all fun blockIndex =>
    let start := 64 * blockIndex
    nodeClaimChunkValidB claims start (min 64 (claims.nodeCount - start))

/-- Validate the exact fixed-row root carried by one search claim array. -/
def searchBranchRootValidB
    (orbit : Fin 7) (rowTwo : Fin 35) (claims : BranchClaims) : Bool :=
  if claims.rootId < claims.nodeCount then
    let root := claims.nodeAt claims.rootId
    let expected := addRowCode
      (addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1)
      (rowTwoMask rowTwo) 2
    let choice0 := searchChoiceForRow 0 30
    let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
    let choice2 := searchChoiceForRow 2 (rowTwoMask rowTwo)
    let pairState := ((PairState.empty.add choice0.pairMask).add choice1.pairMask).add
      choice2.pairMask
    (root.depth == 0) && (root.code == expected) &&
      (root.pairOnce == pairState.seenOnce) &&
      (root.pairTwice == pairState.seenTwice)
  else false

/-- Validate the immediate pattern or exact fixed-row state of one branch claim. -/
def branchClaimRootValidB
    (orbit : Fin 7) (rowTwo : Fin 35) (claim : BranchClaim) : Bool :=
  let codeTwo := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  match claim with
  | .patternTwo patternIdentifier =>
      patternIdentifierPackedMatchesB patternIdentifier codeTwo
  | .patternThree patternIdentifier =>
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
      let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
      let row := rowTwoMask rowTwo
      let choice2 := searchChoiceForRow 2 row
      let codeThree := addRowCode codeTwo row 2
      pairState.compatible choice2.pairMask &&
        (columnState.add row).feasible searchCentres &&
        patternIdentifierPackedMatchesB patternIdentifier codeThree
  | .search claims =>
      let choice0 := searchChoiceForRow 0 30
      let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
      let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
      let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
      let row := rowTwoMask rowTwo
      let choice2 := searchChoiceForRow 2 row
      pairState.compatible choice2.pairMask &&
        (columnState.add row).feasible searchCentres &&
        searchBranchRootValidB orbit rowTwo claims

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
