/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaries
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers
import LeanPool.Erdos97ConvexOctagon.CoverageCertificatePrototype

/-! # Flat local checker for prototype coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

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
  /-- One semantic column-conflict target for every rejected row. -/
  rejectionTargetGroups : Array (List Nat)
  /-- Pattern origins grouped by consecutive five-row words. -/
  patternOriginGroups : Array (List Nat)
  /-- Recursive child identifiers grouped by consecutive five-row words. -/
  childIdGroups : Array (List Nat)
  /-- Exact hard origins grouped by consecutive five-row words. -/
  hardOriginGroups : Array (List Nat)

/-- Flat postorder claims for one fixed branch. -/
structure BranchClaims where
  /-- Every locally checked node in shallow 64-entry groups, children before parents. -/
  nodeGroups : Array (Array NodeClaim)
  /-- Total number of nodes across all groups. -/
  nodeCount : Nat
  /-- Identifier of the branch root. -/
  rootId : Nat

private def defaultNodeClaim : NodeClaim :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, #[], #[], #[], #[]⟩

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

/-- Constant-depth lookup of one compact pattern-summary identifier. -/
def densePatternSummaryAt? (identifier : Nat) : Option PatternSummary :=
  match densePatternSummaryGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

/-- Constant-depth lookup of one compact exact-summary identifier. -/
def denseHardSummaryAt? (identifier : Nat) : Option HardSummary :=
  match denseHardSummaryGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

/-- Packed-only pattern-summary validation for the first computation gate. -/
def patternIdentifierPackedMatchesB
    (identifier : Nat) (code : UInt64) : Bool :=
  match densePatternSummaryAt? identifier with
  | none => false
  | some summary => (summary.mask &&& code) == summary.mask

/-- Packed-only exact-summary validation for the first computation gate. -/
def hardIdentifierPackedMatchesB (identifier : Nat) (code : UInt64) : Bool :=
  match denseHardSummaryAt? identifier with
  | none => false
  | some summary => summary.code == code

/-- Selected row indices in one fixed five-index word. -/
def rowIndexWord (rows : UInt64) (offset : Nat) : List Nat :=
  let word := ((rows >>> UInt64.ofNat offset) &&& 31).toNat
  (fiveBitIndices.getD word []).map fun index => offset + index

/-- Retrieve one conflict cover without unfolding the full generated table. -/
def conflictCoverAt? (identifier : Nat) : Option ConflictCover :=
  match conflictCoverGroups[identifier / 64]? with
  | none => none
  | some group => group[identifier % 64]?

/-- Process at most five compatible rows while threading the local witness streams. -/
private def processFiveRows
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (indices : List Nat) (initial : LocalCursor) : LocalCursor :=
  indices.foldl (fun cursor index =>
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
            ⟨childValid, cursor.patternOrigins, childIds, cursor.hardOrigins⟩) initial

/-- Validate one of the seven disjoint five-row words of a node claim. -/
private def nodeWordValidB
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (wordIndex : Nat) : Bool :=
  let initial : LocalCursor :=
    ⟨true, claim.patternOriginGroups.getD wordIndex [],
      claim.childIdGroups.getD wordIndex [],
      claim.hardOriginGroups.getD wordIndex []⟩
  let result := processFiveRows claims identifier claim centre remaining pairState
    (rowIndexWord claim.activeRows (5 * wordIndex)) initial
  result.ok && result.patternOrigins.isEmpty && result.childIds.isEmpty &&
    result.hardOrigins.isEmpty

/-- Validate one semantically rejected row of a node claim. -/
private def rejectedRowValidB
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

/-- Validate at most five rejected rows using one semantic conflict each. -/
private def rejectedWordValidB
    (claim : NodeClaim) (centre : Vertex) (remaining : List Vertex)
    (indices targets : List Nat) : Bool :=
  let initial : RejectionCursor := ⟨true, targets⟩
  let result := indices.foldl (fun cursor index =>
    if !cursor.ok then cursor
    else
      match cursor.targets with
      | [] => ⟨false, []⟩
      | target :: remainingTargets =>
          ⟨rejectedRowValidB claim centre remaining index target,
            remainingTargets⟩) initial
  result.ok && result.targets.isEmpty

/-- Validate the conservative pair/column row partition of one node. -/
def nodePruningValidB (claims : BranchClaims) (identifier : Nat) : Bool :=
  if identifier < claims.nodeCount then
    let claim := claims.nodeAt identifier
    if claim.depth < searchCentres.length then
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      match conflictCoverAt? claim.conflictCoverId with
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
              rejectedWordValidB claim centre remaining
                  (rowIndexWord claim.rejectedRows (5 * wordIndex))
                  (claim.rejectionTargetGroups.getD wordIndex [])
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

/-- Validate the exact fixed-row root carried by one branch claim array. -/
def branchClaimRootValidB
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

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
