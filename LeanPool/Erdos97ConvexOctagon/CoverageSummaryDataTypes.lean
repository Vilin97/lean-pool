/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Lightweight coverage-summary data validation -/

namespace Erdos97Octagon.RawIncidence

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
