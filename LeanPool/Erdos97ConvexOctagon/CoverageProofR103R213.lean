/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (3, 13) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (3, 13). -/
def coverageRefsR103R213 : List ℕ := [
  3382, 20659, 20664, 20665, 20667, 20672, 20673
]

lrat_semantic coverageUnsatR103R213 coverageCoveredR103R213
  semantic_formula (coverageFormula 225 105 coverageRefsR103R213)
  coverage_fact (coverageRefsR103R213.all (coveredB 225 105) = true)
  dimacs
    "p cnf 64 7\n-9 -14 -15 -17 -22 -23 0\n9 0\n14 0\n15 0\n17 0\n22 0\n23 0\n"
  lrat_first
    "7 d 0\n10 0 2 3 4 5 6 7 1 0\n"
  lrat_second
    ""

/-- Canonical row branch (3, 13) cannot be realised convexly. -/
theorem coverageBranchR103R213_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 225)
    (hrowTwo : Q.targets 2 = packedRow 105) : False := by
  apply coverageUnsatR103R213 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR103R213 coverageCoveredR103R213

end Erdos97Octagon.RawIncidence
