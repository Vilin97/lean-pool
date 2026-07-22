/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (1, 21) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (1, 21). -/
def coverageRefsR101R221 : List ℕ := [
  9, 10, 11, 3617, 20659, 20661, 20662, 20668, 20670
]

lrat_semantic coverageUnsatR101R221 coverageCoveredR101R221
  semantic_formula (coverageFormula 45 90 coverageRefsR101R221)
  coverage_fact (coverageRefsR101R221.all (coveredB 45 90) = true)
  dimacs
    "p cnf 64 9\n2 0\n3 0\n4 0\n-2 -3 -4 -9 -11 -12 -18 -20 0\n9 0\n11 0\n12 0\n18 0\n"
    "20 0\n"
  lrat_first
    "9 d 0\n13 0 1 2 3 5 6 7 8 9 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (1, 21) cannot be realised convexly. -/
theorem coverageBranchR101R221_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 45)
    (hrowTwo : Q.targets 2 = packedRow 90) : False := by
  apply coverageUnsatR101R221 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR101R221 coverageCoveredR101R221

end Erdos97Octagon.RawIncidence
