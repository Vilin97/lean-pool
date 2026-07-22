/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


import LeanPool.Erdos97ConvexOctagon.CoverageFormula
import LeanPool.Erdos97ConvexOctagon.Lrat

/-! # Canonical certificate branch (4, 24) -/

namespace Erdos97Octagon.RawIncidence

/-- Clause references for canonical row branch (4, 24). -/
def coverageRefsR104R224 : List ℕ := [
  10, 11, 12, 3376, 20661, 20662, 20663
]

lrat_semantic coverageUnsatR104R224 coverageCoveredR104R224
  semantic_formula (coverageFormula 60 170 coverageRefsR104R224)
  coverage_fact (coverageRefsR104R224.all (coveredB 60 170) = true)
  dimacs
    "p cnf 64 7\n3 0\n4 0\n5 0\n-3 -4 -5 -11 -12 -13 0\n11 0\n12 0\n13 0\n"
  lrat_first
    "7 d 0\n11 0 1 2 3 5 6 7 4 0\n"
  lrat_second
    ""

/-- Canonical row branch (4, 24) cannot be realised convexly. -/
theorem coverageBranchR104R224_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (hrowOne : Q.targets 1 = packedRow 60)
    (hrowTwo : Q.targets 2 = packedRow 170) : False := by
  apply coverageUnsatR104R224 (valuation Q.targets)
  exact coverageFormula_satisfied hC hR hN hSparse hBalanced hrowOne hrowTwo
    coverageRefsR104R224 coverageCoveredR104R224

end Erdos97Octagon.RawIncidence
