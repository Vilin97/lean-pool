/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (2, 19) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (2, 19). -/
def coverageRefsR102R219 : List ℕ := [
  3382, 20659, 20664, 20665, 20667, 20672, 20673
]

lrat_semantic coverageUnsatR102R219 coverageCoveredR102R219
  semantic_formula (coverageFormula 101 225 coverageRefsR102R219)
  coverage_fact (coverageRefsR102R219.all (coveredB 101 225) = true)
  dimacs
    "p cnf 64 7\n-9 -14 -15 -17 -22 -23 0\n9 0\n14 0\n15 0\n17 0\n22 0\n23 0\n"
  lrat_first
    "7 d 0\n10 0 2 3 4 5 6 7 1 0\n"
  lrat_second
    ""

/-- Canonical row branch (2, 19) cannot be realised convexly. -/
theorem coverageBranchR102R219_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 101)
    (hrowTwo : Q.targets 2 = packedRow 225) : False := by
  apply coverageUnsatR102R219 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR102R219 coverageCoveredR102R219

end Erdos97Octagon.RawIncidence
