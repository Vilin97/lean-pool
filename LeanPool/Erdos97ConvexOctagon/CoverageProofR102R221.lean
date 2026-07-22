/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (2, 21) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (2, 21). -/
def coverageRefsR102R221 : List ℕ := [
  9, 11, 12, 3377, 20668, 20670, 20671
]

lrat_semantic coverageUnsatR102R221 coverageCoveredR102R221
  semantic_formula (coverageFormula 101 90 coverageRefsR102R221)
  coverage_fact (coverageRefsR102R221.all (coveredB 101 90) = true)
  dimacs
    "p cnf 64 7\n2 0\n4 0\n5 0\n-2 -4 -5 -18 -20 -21 0\n18 0\n20 0\n21 0\n"
  lrat_first
    "7 d 0\n11 0 1 2 3 5 6 7 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (2, 21) cannot be realised convexly. -/
theorem coverageBranchR102R221_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 101)
    (hrowTwo : Q.targets 2 = packedRow 90) : False := by
  apply coverageUnsatR102R221 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR102R221 coverageCoveredR102R221

end Erdos97Octagon.RawIncidence
