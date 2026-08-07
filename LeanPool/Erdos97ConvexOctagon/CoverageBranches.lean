/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSoundness

/-!
# Exhaustive coverage contradiction

The compact kernel-checked coverage certificate excludes all seven canonical
first rows.
-/

namespace Erdos97Octagon.RawIncidence

/-- Every normalized counterexample with a canonical first row contradicts
the exhaustive coverage certificate. -/
theorem canonicalBranch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (rowOneIndex : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask rowOneIndex)) :
    False :=
  coverageCanonicalBranch_impossible hC hR hN hSparse hBalanced
    rowOneIndex hrowOne

end Erdos97Octagon.RawIncidence
