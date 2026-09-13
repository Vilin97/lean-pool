/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 1). -/
theorem coverageBranchRoot_0_01 :
    branchClaimRootValidB 0 1 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 19). -/
theorem coverageBranchRoot_4_19 :
    branchClaimRootValidB 4 19 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 6). -/
theorem coverageBranchRoot_1_06 :
    branchClaimRootValidB 1 6 (.search branchClaims1Row6) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 7). -/
theorem coverageBranchRoot_1_07 :
    branchClaimRootValidB 1 7 (.search branchClaims1Row7) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 6), starting at 0. -/
theorem coverageBranchNodes_1_06_00000 :
    nodeClaimChunkValidB branchClaims1Row6 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 6), starting at 64. -/
theorem coverageBranchNodes_1_06_00064 :
    nodeClaimChunkValidB branchClaims1Row6 64 57 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 7), starting at 0. -/
theorem coverageBranchNodes_1_07_00000 :
    nodeClaimChunkValidB branchClaims1Row7 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 7), starting at 64. -/
theorem coverageBranchNodes_1_07_00064 :
    nodeClaimChunkValidB branchClaims1Row7 64 51 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
