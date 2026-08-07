/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Lightweight coverage-summary data types -/

namespace Erdos97Octagon.RawIncidence

/-- A lightweight reference to a monotone obstruction. -/
structure PatternSummary where
  /-- Source identifier of the referenced obstruction. -/
  origin : Nat
  /-- Packed incidence mask of the obstruction. -/
  mask : UInt64

/-- A lightweight reference to an exact-table obstruction. -/
structure HardSummary where
  /-- Source identifier of the referenced obstruction. -/
  origin : Nat
  /-- Packed incidence code of the exact table. -/
  code : UInt64

/-- Shallow buckets of pattern summaries, used to bound kernel reduction depth. -/
abbrev PatternSummaryBuckets := List (List PatternSummary)

/-- Shallow buckets of exact-table summaries, used to bound kernel reduction depth. -/
abbrev HardSummaryBuckets := List (List HardSummary)

/-- One legal row, its six selected vertex pairs, and its pattern-summary buckets. -/
structure SummaryRowChoice where
  /-- Eight-bit target-row mask. -/
  rowMask : UInt64
  /-- Bit mask of unordered vertex pairs selected together by the row. -/
  pairMask : UInt64
  /-- Patterns whose highest nonempty row is compatible with this row. -/
  patterns : PatternSummaryBuckets

/-- Compute the unordered vertex-pair bits selected together by a row mask. -/
def rowPairMask (rowMask : UInt64) : UInt64 :=
  (List.finRange 8).foldl (fun result first =>
    (List.finRange 8).foldl (fun result second =>
      if decide (first < second) && bitSetB rowMask first.val &&
          bitSetB rowMask second.val then
        result ||| (1 <<< UInt64.ofNat (varIndex first second))
      else result) result) 0

/-- Check the precomputed pair mask attached to a row choice. -/
def SummaryRowChoice.pairMaskValidB (choice : SummaryRowChoice) : Bool :=
  choice.pairMask == rowPairMask choice.rowMask

/-- Check a pattern summary against one eight-bucket data shard. -/
def PatternSummary.validAgainstB
    (buckets : Array (List PatternEntry)) (summary : PatternSummary) : Bool :=
  match (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) with
  | some entry => entry.mask == summary.mask && entry.validB
  | none => false

/-- Check an exact-table summary against one eight-bucket data shard. -/
def HardSummary.validAgainstB
    (buckets : Array (List HardEntry)) (summary : HardSummary) : Bool :=
  match (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) with
  | some entry => entry.code == summary.code && entry.validB
  | none => false

end Erdos97Octagon.RawIncidence
