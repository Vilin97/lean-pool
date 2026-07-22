/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (1, 2) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (1, 2). -/
def coverageRefsR101R202 : List ℕ := [
  9, 10, 11, 3616, 20659, 20661, 20662, 20667, 20670
]

lrat_semantic coverageUnsatR101R202 coverageCoveredR101R202
  semantic_formula (coverageFormula 45 75 coverageRefsR101R202)
  coverage_fact (coverageRefsR101R202.all (coveredB 45 75) = true)
  dimacs
    "p cnf 64 9\n2 0\n3 0\n4 0\n-2 -3 -4 -9 -11 -12 -17 -20 0\n9 0\n11 0\n12 0\n17 0\n"
    "20 0\n"
  lrat_first
    "9 d 0\n13 0 1 2 3 5 6 7 8 9 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (1, 2) cannot be realised convexly. -/
theorem coverageBranchR101R202_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 45)
    (hrowTwo : Q.targets 2 = packedRow 75) : False := by
  apply coverageUnsatR101R202 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR101R202 coverageCoveredR101R202

end Erdos97Octagon.RawIncidence
