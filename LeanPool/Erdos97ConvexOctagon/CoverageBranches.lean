/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.MasterCertificate

/-!
# Master coverage contradiction

One kernel-checked certificate excludes all seven canonical first rows at once.
-/

namespace Erdos97Octagon.RawIncidence

open LRAT

/-- Every normalized counterexample with a canonical first row contradicts
the master LRAT certificate. -/
theorem canonicalBranch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (rowOneIndex : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask rowOneIndex)) :
    False :=
  masterFormula_unsatisfiable (valuation Q.targets)
    (masterFormula_satisfied hC hR hN hSparse hBalanced rowOneIndex hrowOne)

end Erdos97Octagon.RawIncidence
