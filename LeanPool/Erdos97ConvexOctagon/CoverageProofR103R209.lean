/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (3, 9) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (3, 9). -/
def coverageRefsR103R209 : List ℕ := [
  3390, 20659, 20665, 20666, 20667, 20673, 20674
]

lrat_semantic coverageUnsatR103R209 coverageCoveredR103R209
  semantic_formula (coverageFormula 225 195 coverageRefsR103R209)
  coverage_fact (coverageRefsR103R209.all (coveredB 225 195) = true)
  dimacs
    "p cnf 64 7\n-9 -15 -16 -17 -23 -24 0\n9 0\n15 0\n16 0\n17 0\n23 0\n24 0\n"
  lrat_first
    "7 d 0\n10 0 2 3 4 5 6 7 1 0\n"
  lrat_second
    ""

/-- Canonical row branch (3, 9) cannot be realised convexly. -/
theorem coverageBranchR103R209_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 225)
    (hrowTwo : Q.targets 2 = packedRow 195) : False := by
  apply coverageUnsatR103R209 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR103R209 coverageCoveredR103R209

end Erdos97Octagon.RawIncidence
