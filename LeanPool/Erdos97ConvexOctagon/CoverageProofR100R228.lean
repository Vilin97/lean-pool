/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (0, 28) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (0, 28). -/
def coverageRefsR100R228 : List ℕ := [
  10, 11, 12, 3376, 20661, 20662, 20663
]

lrat_semantic coverageUnsatR100R228 coverageCoveredR100R228
  semantic_formula (coverageFormula 29 210 coverageRefsR100R228)
  coverage_fact (coverageRefsR100R228.all (coveredB 29 210) = true)
  dimacs
    "p cnf 64 7\n3 0\n4 0\n5 0\n-3 -4 -5 -11 -12 -13 0\n11 0\n12 0\n13 0\n"
  lrat_first
    "7 d 0\n11 0 1 2 3 5 6 7 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (0, 28) cannot be realised convexly. -/
theorem coverageBranchR100R228_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 29)
    (hrowTwo : Q.targets 2 = packedRow 210) : False := by
  apply coverageUnsatR100R228 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR100R228 coverageCoveredR100R228

end Erdos97Octagon.RawIncidence
