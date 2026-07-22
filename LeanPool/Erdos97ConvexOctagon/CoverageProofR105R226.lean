/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (5, 26) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (5, 26). -/
def coverageRefsR105R226 : List ℕ := [
  0, 7, 15, 913, 915, 917, 921, 923, 927, 1703, 1709, 1713, 1715, 2190, 2191, 2193, 2196,
  20659, 20666, 20667, 20674
]

lrat_semantic coverageUnsatR105R226 coverageCoveredR105R226
  semantic_formula (coverageFormula 108 114 coverageRefsR105R226)
  coverage_fact (coverageRefsR105R226.all (coveredB 108 114) = true)
  dimacs
    "p cnf 64 21\n-1 0\n-64 0\n-8 0\n1 9 17 25 33 0\n1 9 17 25 41 0\n1 9 17 25 49 0"
    "\n1 9 17 33 41 0\n1 9 17 33 49 0\n1 9 17 41 49 0\n8 16 24 32 64 0\n8 16 24 40"
    " 64 0\n8 16 24 48 64 0\n8 16 24 56 64 0\n-25 -32 -33 -40 -41 -48 0\n-25 -32 "
    "-33 -40 -49 -56 0\n-25 -32 -41 -48 -49 -56 0\n-33 -40 -41 -48 -49 -56 0\n-9"
    " 0\n-16 0\n-17 0\n-24 0\n"
  lrat_first
    "21 d 0\n22 25 33 0 1 18 20 4 0\n22 d 4 0\n23 25 41 0 1 18 20 5 0\n23 d 5 0\n2"
    "4 25 49 0 1 18 20 6 0\n24 d 6 0\n25 33 41 0 1 18 20 7 0\n25 d 7 0\n26 33 49 "
    "0 1 18 20 8 0\n26 d 8 0\n27 41 49 0 1 18 20 9 0\n27 d 9 0\n36 -41 -49 0 2 3 "
    "18 19 20 21 10 11 12 13 17 16 22 0\n36 d 17 16 22 0\n37 -49 0 2 3 18 19 20"
    " 21 10 11 13 36 25 23 15 0\n37 d 13 36 25 23 15 0\n42 0 2 3 18 19 20 21 10"
    " 11 12 37 27 26 24 14 0\n"
  lrat_second
    ""

/-- Canonical row branch (5, 26) cannot be realised convexly. -/
theorem coverageBranchR105R226_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 108)
    (hrowTwo : Q.targets 2 = packedRow 114) : False := by
  apply coverageUnsatR105R226 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR105R226 coverageCoveredR105R226

end Erdos97Octagon.RawIncidence
