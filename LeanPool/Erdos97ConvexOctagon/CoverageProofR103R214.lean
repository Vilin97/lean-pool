/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (3, 14) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (3, 14). -/
def coverageRefsR103R214 : List ℕ := [
  3387, 20659, 20664, 20666, 20667, 20672, 20674
]

lrat_semantic coverageUnsatR103R214 coverageCoveredR103R214
  semantic_formula (coverageFormula 225 169 coverageRefsR103R214)
  coverage_fact (coverageRefsR103R214.all (coveredB 225 169) = true)
  dimacs
    "p cnf 64 7\n-9 -14 -16 -17 -22 -24 0\n9 0\n14 0\n16 0\n17 0\n22 0\n24 0\n"
  lrat_first
    "7 d 0\n10 0 2 3 4 5 6 7 1 0\n"
  lrat_second
    ""

/-- Canonical row branch (3, 14) cannot be realised convexly. -/
theorem coverageBranchR103R214_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 225)
    (hrowTwo : Q.targets 2 = packedRow 169) : False := by
  apply coverageUnsatR103R214 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR103R214 coverageCoveredR103R214

end Erdos97Octagon.RawIncidence
