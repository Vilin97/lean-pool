/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 1). -/
theorem coverageBranchRoot_4_01 :
    branchClaimRootValidB 4 1 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 10). -/
theorem coverageBranchRoot_6_10 :
    branchClaimRootValidB 6 10 (.search branchClaims6Row10) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 9), starting at 64. -/
theorem coverageBranchNodes_6_09_00064 :
    nodeClaimChunkValidB branchClaims6Row9 64 51 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 0. -/
theorem coverageBranchNodes_6_10_00000 :
    nodeClaimChunkValidB branchClaims6Row10 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 64. -/
theorem coverageBranchNodes_6_10_00064 :
    nodeClaimChunkValidB branchClaims6Row10 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 128. -/
theorem coverageBranchNodes_6_10_00128 :
    nodeClaimChunkValidB branchClaims6Row10 128 30 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
