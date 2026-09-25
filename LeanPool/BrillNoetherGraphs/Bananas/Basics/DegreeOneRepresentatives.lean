/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroVertexBridge

/-!
# Degree-one representatives

This small interface isolates the standard step in the theta proof: a
rank-zero, degree-one divisor class is represented by one vertex; on a
nontrivial banana that vertex is unique.
-/

namespace Bananas

open Utilities

/-- On a nontrivial banana the vertex representative in the previous theorem
is unique. -/
theorem one_chip_representative_unique_on_banana
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) {D : CFDiv B.graph}
    {x y : B.graph.V} (hDx : linearEquiv B.graph D (oneChip x))
    (hDy : linearEquiv B.graph D (oneChip y)) :
    x = y := by
  by_contra hxy
  have hxyEquiv : linearEquiv B.graph (oneChip x) (oneChip y) :=
    hDx.symm.trans hDy
  apply marks_not_linearEquiv hg B hxy
  unfold linearEquiv at hxyEquiv ⊢
  simpa using hxyEquiv

end Bananas
