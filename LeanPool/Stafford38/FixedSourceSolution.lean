/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.FoundationClosure
import LeanPool.Stafford38.Stafford38.FixedSourceChallengeTransport

/-!
# Solution for the exact-source challenge

The substantive development proves the exact fixed-source theorem on the same
`RingQuot` presentation of the Weyl algebra
(`Stafford38.universalFixedSourceStatement`).  The transport module identifies
the challenge's intrinsic ordered-word filtration and its least-level degree
with the development's checked PBW normal-form filtration and degree, and the
two linear symplectic coordinate predicates are definitionally equal.  This
file only combines those facts; it adds no hypothesis and supplies no degree
or normal-form datum.
-/

namespace Stafford38FixedSourceChallenge

universe u

theorem universalFixedSourceStatement : UniversalFixedSourceStatement := by
  intro k _ _ n d hd
  obtain ⟨ell, R, S, hell, hcert⟩ :=
    Stafford38.universalFixedSourceStatement (k := k) n d hd
  have hdeg := Stafford38FixedSourceChallengeTransport.bernsteinDegree_eq k d
  refine ⟨ell, R, S,
    (Stafford38FixedSourceChallengeTransport.isLinearWeylCoordinate_iff
      k n ell).mpr hell, ?_⟩
  rw [hdeg]
  exact hcert

end Stafford38FixedSourceChallenge
