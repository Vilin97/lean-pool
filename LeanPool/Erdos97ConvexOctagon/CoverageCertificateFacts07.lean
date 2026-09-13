/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 7). -/
theorem coverageBranchRoot_0_07 :
    branchClaimRootValidB 0 7 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 25). -/
theorem coverageBranchRoot_4_25 :
    branchClaimRootValidB 4 25 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 28). -/
theorem coverageBranchRoot_1_28 :
    branchClaimRootValidB 1 28 (.search branchClaims1Row28) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 29). -/
theorem coverageBranchRoot_1_29 :
    branchClaimRootValidB 1 29 (.search branchClaims1Row29) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 28), starting at 0. -/
theorem coverageBranchNodes_1_28_00000 :
    nodeClaimChunkValidB branchClaims1Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 28), starting at 64. -/
theorem coverageBranchNodes_1_28_00064 :
    nodeClaimChunkValidB branchClaims1Row28 64 56 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 0. -/
theorem coverageBranchNodes_1_29_00000 :
    nodeClaimChunkValidB branchClaims1Row29 0 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 32. -/
theorem coverageBranchNodes_1_29_00032 :
    nodeClaimChunkValidB branchClaims1Row29 32 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
