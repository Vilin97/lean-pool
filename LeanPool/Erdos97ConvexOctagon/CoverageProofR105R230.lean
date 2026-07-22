/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (5, 30) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (5, 30). -/
def coverageRefsR105R230 : List ℕ := [
  3383, 20662, 20664, 20665, 20670, 20672, 20673
]

lrat_semantic coverageUnsatR105R230 coverageCoveredR105R230
  semantic_formula (coverageFormula 108 120 coverageRefsR105R230)
  coverage_fact (coverageRefsR105R230.all (coveredB 108 120) = true)
  dimacs
    "p cnf 64 7\n-12 -14 -15 -20 -22 -23 0\n12 0\n14 0\n15 0\n20 0\n22 0\n23 0\n"
  lrat_first
    "7 d 0\n10 0 2 3 4 5 6 7 1 0\n"
  lrat_second
    ""

/-- Canonical row branch (5, 30) cannot be realised convexly. -/
theorem coverageBranchR105R230_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 108)
    (hrowTwo : Q.targets 2 = packedRow 120) : False := by
  apply coverageUnsatR105R230 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR105R230 coverageCoveredR105R230

end Erdos97Octagon.RawIncidence
