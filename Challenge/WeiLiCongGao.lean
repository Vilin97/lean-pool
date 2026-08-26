/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Six distances from the E2 diameter-heptagon pattern

Source: doi:10.11650/tjm.18.2014.4030, url:https://github.com/lyfar/erdos132-wei-certificates
Proposed by: Egor Lyfar
Open declarations: `Challenge.WeiLiCongGao.e2_pattern_six_distances`
Tags: discrete-geometry, distance-sets, diameter-graph, erdos-132
MSC: 52C10, 05C62
Estimated size: ~4000 lines of Lean

Informal statement:
* `Challenge.WeiLiCongGao.e2_pattern_six_distances` — Take seven points in the plane, indexed by i =
  0..6, with all pairwise distances at most 1, such that the distance between points i and i+3 (mod
  7) is exactly 1 for every i, and every other pair is at strictly smaller distance. Suppose the
  seven boundary edges d(i, i+1 mod 7) satisfy e0 = e3, e1 = e2, e4 = e5 = e6, and e1 < e4 < e0.
  Then the number of distinct values among the pairwise distances of the seven points is at least
  six.
-/

namespace Challenge.WeiLiCongGao

/-- **The repaired E2 step of Wei–Li–Cong–Gao (2014), Theorem 4.** Seven planar points whose
diameter graph is exactly the 7-cycle `{i, i+3}` of unit diameters, with boundary-edge pattern
`(C, B, B, C, A, A, A)` and `B < A < C`, realize at least six distinct pairwise distances.

The published proof of Theorem 4 handles this configuration by a value-swap appeal ("the proof is
similar"); an exact line audit found that on this pattern the intended strict comparison is an
exact equality, so the published argument does not close the case. A computational repair —
reducing the seven undetermined diagonals to three algebraic classes and excluding every
five-distance label assignment by unit Gröbner ideals over `ℚ` — establishes the statement; this
challenge asks for the Lean proof. The bound is sharp: the configuration family generically
realizes seven distinct distances and drops to exactly six at three isolated configurations, never
to five. -/
theorem e2_pattern_six_distances
    (p : Fin 7 → EuclideanSpace ℝ (Fin 2))
    (hdiam : ∀ i : Fin 7, dist (p i) (p (i + 3)) = 1)
    (hshort : ∀ i j : Fin 7, i ≠ j → j ≠ i + 3 → i ≠ j + 3 → dist (p i) (p j) < 1)
    (hC : dist (p 0) (p 1) = dist (p 3) (p 4))
    (hB : dist (p 1) (p 2) = dist (p 2) (p 3))
    (hA₁ : dist (p 4) (p 5) = dist (p 5) (p 6))
    (hA₂ : dist (p 5) (p 6) = dist (p 6) (p 0))
    (hBA : dist (p 1) (p 2) < dist (p 4) (p 5))
    (hAC : dist (p 4) (p 5) < dist (p 0) (p 1)) :
    6 ≤ ((Finset.univ.filter fun q : Fin 7 × Fin 7 => q.1 ≠ q.2).image
      fun q => dist (p q.1) (p q.2)).card := sorry

end Challenge.WeiLiCongGao
