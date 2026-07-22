/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (1, 4) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (1, 4). -/
def coverageRefsR101R204 : List ℕ := [
  6, 7, 14, 15, 1589, 1595, 1599, 1703, 1709, 1713, 3366, 20665, 20666, 20673, 20674
]

lrat_semantic coverageUnsatR101R204 coverageCoveredR101R204
  semantic_formula (coverageFormula 45 51 coverageRefsR101R204)
  coverage_fact (coverageRefsR101R204.all (coveredB 45 51) = true)
  dimacs
    "p cnf 64 15\n-55 0\n-64 0\n-7 0\n-8 0\n7 15 23 31 55 0\n7 15 23 39 55 0\n7 15 2"
    "3 47 55 0\n8 16 24 32 64 0\n8 16 24 40 64 0\n8 16 24 48 64 0\n-31 -32 -39 -4"
    "0 -47 -48 0\n-15 0\n-16 0\n-23 0\n-24 0\n"
  lrat_first
    "15 d 0\n29 0 1 2 3 4 12 13 14 15 5 6 7 8 9 10 11 0\n"
  lrat_second
    ""

/-- Canonical row branch (1, 4) cannot be realised convexly. -/
theorem coverageBranchR101R204_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 45)
    (hrowTwo : Q.targets 2 = packedRow 51) : False := by
  apply coverageUnsatR101R204 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR101R204 coverageCoveredR101R204

end Erdos97Octagon.RawIncidence
