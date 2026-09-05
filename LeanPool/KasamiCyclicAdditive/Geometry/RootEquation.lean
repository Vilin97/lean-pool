/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# The geometric input, in slope-free form

`RootEqSolvable` is the bare statement that the twisted root equation is
solvable at *every* affine Fermat target with nonzero coordinates: the
interface universally quantifies over the Fermat target, rather than carrying
a chosen target and cube-root-of-unity pair as external parameters.  The
root-count bound of `Assembly/GeometricChain.lean` uses it directly.

Concretely `w = W ^ 3`, `z = T ^ 3` for a point `(W, T)` of the Fermat cubic, so
`w + z = 1` is the Fermat equation and `w ^ m = W ^ (3m) = W ^ (2^k+1)`; the
equation in the definition below is then exactly the twisted root equation of
`KasamiCyclicAdditive.FermatCubic.exists_twisted_root_equation`.

It lives in its own file so that `Geometry/EvenCase.lean`, which proves
`RootEqSolvable` for even `n`, can be imported *by*
`Assembly/GeometricChain.lean` without an import cycle.
-/

namespace KasamiCyclicAdditive

/-- Solvability of the twisted root equation: at every affine Fermat target
`(p, q)` with `p, q ≠ 0` there are `w, z` with `w + z = 1` and
`w ^ m + p * z ^ m = q`. -/
def RootEqSolvable (m : ℕ) (K : Type*) [Field K] : Prop :=
  ∀ p q : K, p ≠ 0 → q ≠ 0 → p ^ 3 + q ^ 3 = 1 →
    ∃ w z : K, w + z = 1 ∧ w ^ m + p * z ^ m = q

end KasamiCyclicAdditive
