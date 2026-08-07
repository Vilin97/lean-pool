/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

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
  /-- Eight packed one-byte column counts. -/
  columnCounts : UInt64
  /-- Legal-row indices stopped by pattern origins. -/
  patternRows : UInt64
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

private def defaultNodeClaim : NodeClaim := ⟨0, 0, 0, 0, 0, 0, #[], #[], #[]⟩

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

/-- Packed-only pattern-origin validation for the first computation gate. -/
def patternOriginPackedMatchesB (origin : Nat) (code : UInt64) : Bool :=
  match patternSummaryForOrigin? origin with
  | none => false
  | some summary => (summary.mask &&& code) == summary.mask

/-- Packed-only hard-origin validation for the first computation gate. -/
def hardOriginPackedMatchesB (origin : Nat) (code : UInt64) : Bool :=
  match hardSummaryForOrigin? origin with
  | none => false
  | some summary => summary.code == code

/-- Compatible row indices in one fixed five-index word. -/
def compatibleRowIndexWord
    (incompatible : UInt64) (offset : Nat) : List Nat :=
  let compatible := incompatible ^^^ 34359738367
  let word := ((compatible >>> UInt64.ofNat offset) &&& 31).toNat
  (fiveBitIndices.getD word []).map fun index => offset + index

/-- Process at most five compatible rows while threading the local witness streams. -/
private def processFiveRows
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (columnState : ColumnState) (indices : List Nat)
    (initial : LocalCursor) : LocalCursor :=
  indices.foldl (fun cursor index =>
    if !cursor.ok then cursor
    else
      let choice := (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩
      let nextCode := addRowCode claim.code choice.rowMask centre
      let nextPairState := pairState.add choice.pairMask
      let nextColumnState := columnState.add choice.rowMask
      let nextAssignments :=
        (centre, choice.rowMask) :: assignmentsFromCode claim.code claim.depth
      let columnSurvives := nextColumnState.feasible remaining ||
        columnFeasibleB nextAssignments remaining
      if columnSurvives then
        if bitSetB claim.patternRows index then
          match cursor.patternOrigins with
          | [] => ⟨false, [], cursor.childIds, cursor.hardOrigins⟩
          | origin :: origins =>
              ⟨patternOriginPackedMatchesB origin nextCode,
                origins, cursor.childIds, cursor.hardOrigins⟩
        else if remaining.isEmpty then
          match cursor.hardOrigins with
          | [] => ⟨false, cursor.patternOrigins, cursor.childIds, []⟩
          | origin :: origins =>
              ⟨hardOriginPackedMatchesB origin nextCode,
                cursor.patternOrigins, cursor.childIds, origins⟩
        else
          match cursor.childIds with
          | [] => ⟨false, cursor.patternOrigins, [], cursor.hardOrigins⟩
          | childId :: childIds =>
              let child := claims.nodeAt childId
              let childValid := decide (childId < identifier) &&
                decide (childId < claims.nodeCount) &&
                (child.depth == claim.depth + 1) && (child.code == nextCode) &&
                (child.pairOnce == nextPairState.seenOnce) &&
                (child.pairTwice == nextPairState.seenTwice) &&
                (child.columnCounts == nextColumnState.counts)
              ⟨childValid, cursor.patternOrigins, childIds, cursor.hardOrigins⟩
      else if bitSetB claim.patternRows index then
        ⟨false, cursor.patternOrigins, cursor.childIds, cursor.hardOrigins⟩
      else cursor) initial

/-- Validate one of the seven disjoint five-row words of a node claim. -/
private def nodeWordValidB
    (claims : BranchClaims) (identifier : Nat) (claim : NodeClaim)
    (centre : Vertex) (remaining : List Vertex) (pairState : PairState)
    (columnState : ColumnState) (incompatible : UInt64) (wordIndex : Nat) : Bool :=
  let initial : LocalCursor :=
    ⟨true, claim.patternOriginGroups.getD wordIndex [],
      claim.childIdGroups.getD wordIndex [],
      claim.hardOriginGroups.getD wordIndex []⟩
  let result := processFiveRows claims identifier claim centre remaining pairState
    columnState (compatibleRowIndexWord incompatible (5 * wordIndex)) initial
  result.ok && result.patternOrigins.isEmpty && result.childIds.isEmpty &&
    result.hardOrigins.isEmpty

/-- Fail-closed local validation of one postorder node and its child transitions. -/
def nodeLocalValidB (claims : BranchClaims) (identifier : Nat) : Bool :=
  if identifier < claims.nodeCount then
    let claim := claims.nodeAt identifier
    if claim.depth < searchCentres.length then
      let centre := searchCentres.getD claim.depth 0
      let remaining := searchCentres.drop (claim.depth + 1)
      let pairState : PairState := ⟨claim.pairOnce, claim.pairTwice⟩
      let columnState : ColumnState := ⟨claim.columnCounts⟩
      let incompatible := incompatibleRowIndexMask centre pairState.seenTwice
      if (claim.patternRows &&& 34359738367) != claim.patternRows ||
          (claim.patternRows &&& incompatible) != 0 then false
      else
        (List.range 7).all fun wordIndex =>
          nodeWordValidB claims identifier claim centre remaining pairState
            columnState incompatible wordIndex
    else false
  else false

/-- Validate a bounded consecutive chunk of postorder node identifiers. -/
def nodeClaimChunkValidB
    (claims : BranchClaims) (start count : Nat) : Bool :=
  (List.range count).all fun offset => nodeLocalValidB claims (start + offset)

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
    let columnState := ((ColumnState.empty.add 30).add (canonicalRowMask orbit)).add
      (rowTwoMask rowTwo)
    (root.depth == 0) && (root.code == expected) &&
      (root.pairOnce == pairState.seenOnce) &&
      (root.pairTwice == pairState.seenTwice) &&
      (root.columnCounts == columnState.counts)
  else false

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
