/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks

/-! # Types and local audit for repeated-pair row-mask covers -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Repeated pairs and legal rows that they soundly reject at one search centre. -/
structure ConflictCover where
  /-- Search centre for which the row-index mask is valid. -/
  centre : Nat
  /-- Repeated-pair bits sufficient to justify the rejected rows. -/
  requiredPairs : UInt64
  /-- Masked rows, each of which contains one of the required pairs. -/
  incompatibleRows : UInt64
  /-- Short list of pair bits whose row-mask union is `incompatibleRows`. -/
  pairIndices : List Nat

/-- Audit the short pair list and its precomputed row-mask union. -/
def ConflictCover.validB (cover : ConflictCover) : Bool :=
  if _hcentre : cover.centre < 8 then
    let masks := pairRowIndexMasks.getD cover.centre #[]
    cover.pairIndices.all (fun index =>
      index < 64 && bitSetB cover.requiredPairs index) &&
      cover.pairIndices.foldl (fun rows index =>
        rows ||| masks.getD index 0) 0 == cover.incompatibleRows
  else false

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
