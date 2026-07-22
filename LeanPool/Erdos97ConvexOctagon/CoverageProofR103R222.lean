/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (3, 22) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (3, 22). -/
def coverageRefsR103R222 : List ℕ := [
  9, 11, 12, 3377, 20668, 20670, 20671
]

lrat_semantic coverageUnsatR103R222 coverageCoveredR103R222
  semantic_formula (coverageFormula 225 154 coverageRefsR103R222)
  coverage_fact (coverageRefsR103R222.all (coveredB 225 154) = true)
  dimacs
    "p cnf 64 7\n2 0\n4 0\n5 0\n-2 -4 -5 -18 -20 -21 0\n18 0\n20 0\n21 0\n"
  lrat_first
    "7 d 0\n11 0 1 2 3 5 6 7 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (3, 22) cannot be realised convexly. -/
theorem coverageBranchR103R222_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 225)
    (hrowTwo : Q.targets 2 = packedRow 154) : False := by
  apply coverageUnsatR103R222 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR103R222 coverageCoveredR103R222

end Erdos97Octagon.RawIncidence
