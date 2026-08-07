/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoices
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData
import LeanPool.Erdos97ConvexOctagon.RowSymmetry

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

/-- Whether a target is selected by an assigned row. -/
def selectedByAssignmentsB
    (assignments : List RowAssignment) (centre target : Vertex) : Bool :=
  assignments.any fun assignment =>
    (assignment.1 == centre) && bitSetB assignment.2 target.val

/-- Full semantic check that a packed pattern extends the assigned partial table. -/
def patternExtendsAssignmentsB
    (assignments : List RowAssignment) (summary : PatternSummary) : Bool :=
  (List.finRange 8).all fun centre =>
    (List.finRange 8).all fun target =>
      !bitSetB summary.mask (varIndex centre target) ||
        selectedByAssignmentsB assignments centre target

/-- Check a statically selected pattern summary against the current prefix. -/
def patternSummaryMatchesB
    (code : UInt64) (assignments : List RowAssignment)
    (summary : PatternSummary) : Bool :=
  ((summary.mask &&& code) == summary.mask) &&
    patternExtendsAssignmentsB assignments summary

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
    (code : UInt64) (assignments : List RowAssignment)
    (summary : HardSummary) : Bool :=
  (summary.code == code) && hardEqualsAssignmentsB assignments summary

/-- Check whether any shallow-bucketed exact-table summary equals the table. -/
def hasHardB
    (code : UInt64) (assignments : List RowAssignment)
    (summaries : HardSummaryBuckets) : Bool :=
  summaries.any fun bucket =>
    bucket.any (hardSummaryMatchesB code assignments)

/-- Semantic pair-sparsity guard used to validate every fast pair-state rejection. -/
def pairCompatibleB (assignments : List RowAssignment) (row : UInt64) : Bool :=
  vertexPairs.all fun pair =>
    match pair with
    | [a, b] => !(bitSetB row a.val && bitSetB row b.val) ||
        decide ((assignments.filter fun previous =>
          bitSetB previous.2 a.val && bitSetB previous.2 b.val).length < 2)
    | _ => false

/-- Add one row to a packed 64-bit incidence-table prefix. -/
def addRowCode (code row : UInt64) (centre : Vertex) : UInt64 :=
  code ||| (row <<< UInt64.ofNat (8 * centre.val))

/-- Retrieve the static choice associated with one centre and row mask. -/
def choiceForRow (centre : Vertex) (row : UInt64) : SummaryRowChoice :=
  ((patternSummaryChoices.getD centre.val []).find?
    (fun choice => choice.rowMask == row)).getD ⟨0, 0, []⟩

/-- Retrieve exact-table summaries for one canonical orbit and second row. -/
def hardSummaries (orbit : Fin 7) (rowTwo : Fin 35) : HardSummaryBuckets :=
  (hardSummaryChoices.getD orbit.val #[]).getD rowTwo.val []

/-- Exhaustively search the remaining rows using pair sparsity and summary buckets. -/
def directSearch :
    List Vertex → List RowAssignment → UInt64 → PairState →
      HardSummaryBuckets → Bool
  | [], assignments, code, _pairState, hardEntries =>
      hasHardB code assignments hardEntries
  | centre :: remaining, assignments, code, pairState, hardEntries =>
      (patternSummaryChoices.getD centre.val []).all fun choice =>
        let row := choice.rowMask
        if pairState.compatible choice.pairMask then
          let nextAssignments := assignments ++ [(centre, row)]
          let nextCode := addRowCode code row centre
          let nextPairState := pairState.add choice.pairMask
          hasPatternB nextCode nextAssignments choice.patterns ||
            directSearch remaining nextAssignments nextCode nextPairState hardEntries
        else !pairCompatibleB assignments row

/-- Direct exhaustive audit of one fixed canonical orbit and second row. -/
def directCoverageBranchB (orbit : Fin 7) (rowTwo : Fin 35) : Bool :=
  let assignments := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
  if hasPatternB code assignments choice1.patterns then true
  else
    let row := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row
    if pairState.compatible choice2.pairMask then
      let nextAssignments := assignments ++ [(2, row)]
      let nextCode := addRowCode code row 2
      let nextPairState := pairState.add choice2.pairMask
      hasPatternB nextCode nextAssignments choice2.patterns ||
        directSearch [3, 4, 5, 6, 7] nextAssignments nextCode nextPairState
          (hardSummaries orbit rowTwo)
    else !pairCompatibleB assignments row

/-- Direct audit after fixing rows two and three, for adaptive kernel splitting. -/
def directCoverageSubbranchB
    (orbit : Fin 7) (rowTwo rowThree : Fin 35) : Bool :=
  let assignments := [(0, 30), (1, canonicalRowMask orbit)]
  let code := addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1
  let choice0 := choiceForRow 0 30
  let choice1 := choiceForRow 1 (canonicalRowMask orbit)
  let pairState := (PairState.empty.add choice0.pairMask).add choice1.pairMask
  if hasPatternB code assignments choice1.patterns then true
  else
    let row2 := rowTwoMask rowTwo
    let choice2 := choiceForRow 2 row2
    if pairState.compatible choice2.pairMask then
      let assignments2 := assignments ++ [(2, row2)]
      let code2 := addRowCode code row2 2
      let pairState2 := pairState.add choice2.pairMask
      if hasPatternB code2 assignments2 choice2.patterns then true
      else
        let choice3 := patternSummaryChoices3.getD rowThree.val ⟨0, 0, []⟩
        if pairState2.compatible choice3.pairMask then
          let assignments3 := assignments2 ++ [(3, choice3.rowMask)]
          let code3 := addRowCode code2 choice3.rowMask 3
          let pairState3 := pairState2.add choice3.pairMask
          hasPatternB code3 assignments3 choice3.patterns ||
            directSearch [4, 5, 6, 7] assignments3 code3 pairState3
              (hardSummaries orbit rowTwo)
        else !pairCompatibleB assignments2 choice3.rowMask
    else !pairCompatibleB assignments row2

/-- Either a whole second-row branch or all of its third-row subbranches audit cleanly. -/
def BranchAudit (orbit : Fin 7) (rowTwo : Fin 35) : Prop :=
  directCoverageBranchB orbit rowTwo = true ∨
    ∀ rowThree : Fin 35, directCoverageSubbranchB orbit rowTwo rowThree = true

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
