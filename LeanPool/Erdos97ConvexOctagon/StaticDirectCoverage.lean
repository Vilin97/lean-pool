/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoices
import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
import LeanPool.Erdos97ConvexOctagon.CoverageSearchCore
import LeanPool.Erdos97ConvexOctagon.PairCompatibility
import LeanPool.Erdos97ConvexOctagon.RowMasks

/-! # Direct finite coverage audit using statically bucketed summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Index of the least significant set bit, found by six fixed half-word tests. -/
def firstSetBitIndex (bits : UInt64) : Nat :=
  let shift32 : UInt64 := if (bits &&& 4294967295) == 0 then 32 else 0
  let bits := bits >>> shift32
  let shift16 : UInt64 := if (bits &&& 65535) == 0 then 16 else 0
  let bits := bits >>> shift16
  let shift8 : UInt64 := if (bits &&& 255) == 0 then 8 else 0
  let bits := bits >>> shift8
  let shift4 : UInt64 := if (bits &&& 15) == 0 then 4 else 0
  let bits := bits >>> shift4
  let shift2 : UInt64 := if (bits &&& 3) == 0 then 2 else 0
  let bits := bits >>> shift2
  let shift1 : UInt64 := if (bits &&& 1) == 0 then 1 else 0
  (shift32 + shift16 + shift8 + shift4 + shift2 + shift1).toNat

private def incompatibleRowIndexMaskAux
    (pairMasks : Array UInt64) : Nat → UInt64 → UInt64 → UInt64
  | 0, _bits, result => result
  | fuel + 1, bits, result =>
      if bits == 0 then result
      else
        let index := firstSetBitIndex bits
        incompatibleRowIndexMaskAux pairMasks fuel (bits &&& (bits - 1))
          (result ||| pairMasks.getD index 0)

/-- Legal-row indices incompatible with pairs already seen in two rows. -/
def incompatibleRowIndexMask (centre : Vertex) (seenTwice : UInt64) : UInt64 :=
  incompatibleRowIndexMaskAux (pairRowIndexMasks.getD centre.val #[])
    64 seenTwice 0

/-- Legal-row indices not ruled out by the accumulated pair conflicts. -/
def compatibleRowIndices (incompatible : UInt64) : List Nat :=
  let compatible := incompatible ^^^ 34359738367
  [0, 5, 10, 15, 20, 25, 30].flatMap fun offset =>
    let word := ((compatible >>> UInt64.ofNat offset) &&& 31).toNat
    (fiveBitIndices.getD word []).map fun index => offset + index

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
