/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 22). -/
theorem coverageBranchRoot_1_22 :
    branchClaimRootValidB 1 22 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 6). -/
theorem coverageBranchRoot_5_06 :
    branchClaimRootValidB 5 6 (.search branchClaims5Row6) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 7). -/
theorem coverageBranchRoot_5_07 :
    branchClaimRootValidB 5 7 (.search branchClaims5Row7) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 5), starting at 64. -/
theorem coverageBranchNodes_5_05_00064 :
    nodeClaimChunkValidB branchClaims5Row5 64 30 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 6), starting at 0. -/
theorem coverageBranchNodes_5_06_00000 :
    nodeClaimChunkValidB branchClaims5Row6 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 6), starting at 64. -/
theorem coverageBranchNodes_5_06_00064 :
    nodeClaimChunkValidB branchClaims5Row6 64 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 7), starting at 0. -/
theorem coverageBranchNodes_5_07_00000 :
    nodeClaimChunkValidB branchClaims5Row7 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
