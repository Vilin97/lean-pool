/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.HollowReduction
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.TheoremOneTwelve

/-!
# The polytope centerpoint theorem

This module assembles the canonical support-hull face flag, Flag Helly and
its centerpoint corollary, and the prime-reduction bound for hollow rational
polytopes into Theorem 1.12.
-/

namespace EGZ

/-- Theorem 1.12 (`thm:cpt`), with the rational-support hypothesis made
explicit.  In the paper this is intended by `P ⊆ ℚ^d`; it is necessary once
the polytope is represented in its real affine span. -/
theorem theorem_1_12_polytope_centerpoint {d : ℕ} (hd : 0 < d)
    (P : RationalPolytope d) (w : RealCoord d → NNReal)
    (hfinite : (Function.support w).Finite)
    (hnonzero : w ≠ 0)
    (hsupport : Function.support w ⊆ P.carrier)
    (hrational : ∀ q ∈ Function.support w, IsRational q) :
    PolytopeCenterpointConclusion P w := by
  let G : HollowPolytopeGeometry d := {
    hollowCounts_bddAbove :=
      bddAbove_hollowPolytopeVertexCount_of_reductionBridge
        (Nat.succ_le_iff.mpr hd) (hollowReductionBridge d) }
  exact polytopeCenterpointConclusion_of_hollowGeometry
    P w hfinite hnonzero hsupport hrational G

end EGZ
