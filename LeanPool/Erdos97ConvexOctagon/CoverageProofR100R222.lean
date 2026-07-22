/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (0, 22) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (0, 22). -/
def coverageRefsR100R222 : List ℕ := [
  10, 11, 12, 3376, 20661, 20662, 20663
]

lrat_semantic coverageUnsatR100R222 coverageCoveredR100R222
  semantic_formula (coverageFormula 29 154 coverageRefsR100R222)
  coverage_fact (coverageRefsR100R222.all (coveredB 29 154) = true)
  dimacs
    "p cnf 64 7\n3 0\n4 0\n5 0\n-3 -4 -5 -11 -12 -13 0\n11 0\n12 0\n13 0\n"
  lrat_first
    "7 d 0\n11 0 1 2 3 5 6 7 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (0, 22) cannot be realised convexly. -/
theorem coverageBranchR100R222_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 29)
    (hrowTwo : Q.targets 2 = packedRow 154) : False := by
  apply coverageUnsatR100R222 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR100R222 coverageCoveredR100R222

end Erdos97Octagon.RawIncidence
