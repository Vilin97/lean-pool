/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCircDominationFinite
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCircDominationQOne
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCircDominationTop

/-!
# Exact circ domination of the dual negative Besov kernels

This module collects the three source exponent regimes of the Chapter 1
dual-to-circ comparison.  It also records that the depth-zero circ weight in
the full-norm bounds is literally the manuscript factor `3^(s m)`, with
`m = Q.scale`.
-/

namespace Homogenization

open scoped ENNReal

/-- The depth-zero exact circ weight is the manuscript root factor `3^(s m)`,
where `m` is the scale of the parent cube. -/
theorem exactCircDepthWeight_zero_eq_sourceRootWeight {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) :
    exactCircDepthWeight Q s 0 =
      (3 : ℝ≥0∞) ^ (s * (Q.scale : ℝ)) := by
  simp only [exactCircDepthWeight, exactCircSourceDepth, Nat.cast_zero,
    sub_zero]
  congr 1
  ring

end Homogenization
