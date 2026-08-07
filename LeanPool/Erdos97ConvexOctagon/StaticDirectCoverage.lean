/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoices
import LeanPool.Erdos97ConvexOctagon.PairCompatibility
import LeanPool.Erdos97ConvexOctagon.RowMasks

/-! # Direct finite coverage audit using statically bucketed summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- One assigned centre and its eight-bit target-row mask. -/
abbrev RowAssignment := Vertex × UInt64

/-- Packed state recording which unordered pairs have occurred once or twice. -/
structure PairState where
  /-- Pairs that have occurred in at least one assigned row. -/
  seenOnce : UInt64
  /-- Pairs that have occurred in at least two assigned rows. -/
  seenTwice : UInt64

/-- The empty pair-occurrence state. -/
def PairState.empty : PairState := ⟨0, 0⟩

/-- Whether adding a row preserves pair sparsity. -/
def PairState.compatible (state : PairState) (pairMask : UInt64) : Bool :=
  (state.seenTwice &&& pairMask) == 0

/-- Update pair occurrences after accepting one row. -/
def PairState.add (state : PairState) (pairMask : UInt64) : PairState :=
  ⟨state.seenOnce ||| pairMask,
    state.seenTwice ||| (state.seenOnce &&& pairMask)⟩

/-- Packed byte counters for the number of assigned rows selecting each target. -/
structure ColumnState where
  /-- Eight one-byte column counters. -/
  counts : UInt64

/-- The empty column-count state. -/
def ColumnState.empty : ColumnState := ⟨0⟩

/-- Packed increments contributed by one target-row mask. -/
def columnIncrements (row : UInt64) : UInt64 :=
  (List.finRange 8).foldl (fun result target =>
    if bitSetB row target.val then
      result + (1 <<< UInt64.ofNat (8 * target.val))
    else result) 0

/-- Update packed column counts after accepting one row. -/
def ColumnState.add (state : ColumnState) (row : UInt64) : ColumnState :=
  ⟨state.counts + columnIncrements row⟩

/-- Read one packed column counter. -/
def ColumnState.count (state : ColumnState) (target : Vertex) : Nat :=
  ((state.counts >>> UInt64.ofNat (8 * target.val)) &&& 255).toNat

/-- Number of remaining rows that can still select a target. -/
def remainingColumnCapacity (remaining : List Vertex) (target : Vertex) : Nat :=
  (remaining.filter (· ≠ target)).length

/-- Fast packed check that every column can still finish with exactly four entries. -/
def ColumnState.feasible (state : ColumnState) (remaining : List Vertex) : Bool :=
  (List.finRange 8).all fun target =>
    decide (state.count target ≤ 4) &&
      decide (4 ≤ state.count target + remainingColumnCapacity remaining target)

/-- Whether a target is selected by an assigned row. -/
def selectedByAssignmentsB
    (assignments : List RowAssignment) (centre target : Vertex) : Bool :=
  assignments.any fun assignment =>
    (assignment.1 == centre) && bitSetB assignment.2 target.val

/-- Number of assigned rows selecting one target, computed from the semantic prefix. -/
def assignmentColumnCount
    (assignments : List RowAssignment) (target : Vertex) : Nat :=
  (assignments.filter fun assignment => bitSetB assignment.2 target.val).length

/-- Semantic check that every column can still finish with exactly four entries. -/
def columnFeasibleB
    (assignments : List RowAssignment) (remaining : List Vertex) : Bool :=
  (List.finRange 8).all fun target =>
    decide (assignmentColumnCount assignments target ≤ 4) &&
      decide (4 ≤ assignmentColumnCount assignments target +
        remainingColumnCapacity remaining target)

/-- Validate one column-conflict hint selected from the packed column state. -/
def columnConflictHintB
    (assignments : List RowAssignment) (remaining : List Vertex)
    (state : ColumnState) : Bool :=
  match (List.finRange 8).find? (fun target =>
      let count := state.count target
      !(decide (count ≤ 4) &&
        decide (4 ≤ count + remainingColumnCapacity remaining target))) with
  | some target =>
      let count := assignmentColumnCount assignments target
      !(decide (count ≤ 4) &&
        decide (4 ≤ count + remainingColumnCapacity remaining target))
  | none => false

/-- Prune a row as soon as the exact packed pair state detects a third occurrence. -/
def withPairPruningB
    (_assignments : List RowAssignment) (_row : UInt64)
    (state : PairState) (pairMask : UInt64)
    (continueSearch : Unit → Bool) : Bool :=
  if state.compatible pairMask then continueSearch ()
  else true

/-- Use the packed column guard only when its suggested conflict validates semantically. -/
def withColumnPruningB
    (assignments : List RowAssignment) (remaining : List Vertex)
    (state : ColumnState) (continueSearch : Unit → Bool) : Bool :=
  if state.feasible remaining then continueSearch ()
  else columnConflictHintB assignments remaining state || continueSearch ()

/-- Full semantic check that a packed pattern extends the assigned partial table. -/
def patternExtendsAssignmentsB
    (assignments : List RowAssignment) (summary : PatternSummary) : Bool :=
  (List.finRange 8).all fun centre =>
    (List.finRange 8).all fun target =>
      !bitSetB summary.mask (varIndex centre target) ||
        selectedByAssignmentsB assignments centre target

/-- Check a statically selected pattern summary against the current prefix. -/
def patternSummaryMatchesB
    (code : UInt64) (_assignments : List RowAssignment)
    (summary : PatternSummary) : Bool :=
  (summary.mask &&& code) == summary.mask

/-- Check whether any shallow-bucketed pattern summary covers the prefix. -/
def hasPatternB
    (code : UInt64) (assignments : List RowAssignment)
    (summaries : PatternSummaryBuckets) : Bool :=
  summaries.any fun bucket =>
    bucket.any (patternSummaryMatchesB code assignments)

/-- Full semantic check that an exact-table code equals all assigned rows. -/
def hardEqualsAssignmentsB
    (assignments : List RowAssignment) (summary : HardSummary) : Bool :=
  (List.finRange 8).all fun centre =>
    (List.finRange 8).all fun target =>
      bitSetB summary.code (varIndex centre target) ==
        selectedByAssignmentsB assignments centre target

/-- Check a statically selected exact-table summary against a completed table. -/
def hardSummaryMatchesB
    (code : UInt64) (_assignments : List RowAssignment)
    (summary : HardSummary) : Bool :=
  summary.code == code

/-- Check whether any shallow-bucketed exact-table summary equals the table. -/
def hasHardB
    (code : UInt64) (assignments : List RowAssignment)
    (summaries : HardSummaryBuckets) : Bool :=
  summaries.any fun bucket =>
    bucket.any (hardSummaryMatchesB code assignments)

/-- Add one row to a packed 64-bit incidence-table prefix. -/
def addRowCode (code row : UInt64) (centre : Vertex) : UInt64 :=
  code ||| ((row &&& 255) <<< UInt64.ofNat (8 * centre.val))

/-- Retrieve the static choice associated with one centre and row mask. -/
def choiceForRow (centre : Vertex) (row : UInt64) : SummaryRowChoice :=
  ((patternSummaryChoices.getD centre.val []).find?
    (fun choice => choice.rowMask == row)).getD ⟨0, 0, []⟩

/-- Retrieve exact-table summaries for one canonical orbit and second row. -/
def hardSummaries (orbit : Fin 7) (rowTwo : Fin 35) : HardSummaryBuckets :=
  (hardSummaryChoices.getD orbit.val #[]).getD rowTwo.val []

/-- Exhaustively search the remaining rows using pair sparsity and summary buckets. -/
def directSearch :
    List Vertex → List RowAssignment → UInt64 → PairState → ColumnState →
      HardSummaryBuckets → Bool
  | [], assignments, code, _pairState, _columnState, hardEntries =>
      hasHardB code assignments hardEntries
  | centre :: remaining, assignments, code, pairState, columnState, hardEntries =>
      (patternSummaryChoices.getD centre.val []).all fun choice =>
        let row := choice.rowMask
        let continueAfterPair (_ : Unit) :=
          let nextAssignments := (centre, row) :: assignments
          let nextCode := addRowCode code row centre
          let nextPairState := pairState.add choice.pairMask
          let nextColumnState := columnState.add row
          withColumnPruningB nextAssignments remaining nextColumnState fun _ =>
            hasPatternB nextCode nextAssignments choice.patterns ||
              directSearch remaining nextAssignments nextCode nextPairState
                nextColumnState hardEntries
        withPairPruningB assignments row pairState choice.pairMask continueAfterPair

/-- Direct exhaustive audit of one fixed canonical orbit and second row. -/
def directCoverageBranchB (orbit : Fin 7) (rowTwo : Fin 35) : Bool :=
  let assignments := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
  let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
  if hasPatternB code assignments choice1.patterns then true
  else
    let row := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row
    let continueAfterPair (_ : Unit) :=
      let nextAssignments := (2, row) :: assignments
      let nextCode := addRowCode code row 2
      let nextPairState := pairState.add choice2.pairMask
      let nextColumnState := columnState.add row
      withColumnPruningB nextAssignments searchCentres nextColumnState fun _ =>
        hasPatternB nextCode nextAssignments choice2.patterns ||
          directSearch searchCentres nextAssignments nextCode nextPairState
            nextColumnState (hardSummaries orbit rowTwo)
    withPairPruningB assignments row pairState choice2.pairMask continueAfterPair

/-- Direct audit after fixing rows two and three, for adaptive kernel splitting. -/
def directCoverageSubbranchB
    (orbit : Fin 7) (rowTwo rowThree : Fin 35) : Bool :=
  let assignments := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
  let columnState := (ColumnState.empty.add 30).add (canonicalRowMask orbit)
  if hasPatternB code assignments choice1.patterns then true
  else
    let row2 := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row2
    let continueAfterPairTwo (_ : Unit) :=
      let assignments2 := (2, row2) :: assignments
      let code2 := addRowCode code row2 2
      let pairState2 := pairState.add choice2.pairMask
      let columnState2 := columnState.add row2
      withColumnPruningB assignments2 searchCentres columnState2 fun _ =>
        if hasPatternB code2 assignments2 choice2.patterns then true
        else
          let choice3 := patternSummaryChoices3.getD rowThree.val ⟨0, 0, []⟩
          let continueAfterPairThree (_ : Unit) :=
            let assignments3 := (3, choice3.rowMask) :: assignments2
            let code3 := addRowCode code2 choice3.rowMask 3
            let pairState3 := pairState2.add choice3.pairMask
            let columnState3 := columnState2.add choice3.rowMask
            withColumnPruningB assignments3 searchCentres.tail columnState3 fun _ =>
              hasPatternB code3 assignments3 choice3.patterns ||
                directSearch searchCentres.tail assignments3 code3 pairState3
                  columnState3 (hardSummaries orbit rowTwo)
          withPairPruningB assignments2 choice3.rowMask pairState2
            choice3.pairMask continueAfterPairThree
    withPairPruningB assignments row2 pairState choice2.pairMask continueAfterPairTwo

/-- Either a whole second-row branch or all of its third-row subbranches audit cleanly. -/
def BranchAudit (orbit : Fin 7) (rowTwo : Fin 35) : Prop :=
  directCoverageBranchB orbit rowTwo = true ∨
    ∀ rowThree : Fin 35, directCoverageSubbranchB orbit rowTwo rowThree = true

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
