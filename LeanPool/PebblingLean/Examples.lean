/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.Hypercube

/-!
# Small examples

These definitions give named vertices and distributions for testing the basic
API on low-dimensional cubes.
-/

namespace PebblingLean

namespace Hypercube

/-- The all-zero vertex of a hypercube. -/
def zeroVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => false

/-- The all-one vertex of a hypercube. -/
def oneVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => true

theorem dist_zero_zero (n : ℕ) : dist (zeroVertex n) (zeroVertex n) = 0 := by
  exact dist_self (zeroVertex n)

end Hypercube

namespace Examples

/-- Three pebbles on one vertex of the square `Q_2`. -/
def squareThreeAtZero : Pebbling (HypercubeVertex 2) :=
  fun x => if x = Hypercube.zeroVertex 2 then 3 else 0

end Examples

end PebblingLean
