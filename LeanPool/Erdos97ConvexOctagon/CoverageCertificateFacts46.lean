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

/-- Root audit for fixed branch (1, 21). -/
theorem coverageBranchRoot_1_21 :
    branchClaimRootValidB 1 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 4). -/
theorem coverageBranchRoot_5_04 :
    branchClaimRootValidB 5 4 (.search branchClaims5Row4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 5). -/
theorem coverageBranchRoot_5_05 :
    branchClaimRootValidB 5 5 (.search branchClaims5Row5) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 256. -/
theorem coverageBranchNodes_3_32_00256 :
    nodeClaimChunkValidB branchClaims3Row32 256 12 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 4), starting at 0. -/
theorem coverageBranchNodes_5_04_00000 :
    nodeClaimChunkValidB branchClaims5Row4 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 4), starting at 64. -/
theorem coverageBranchNodes_5_04_00064 :
    nodeClaimChunkValidB branchClaims5Row4 64 50 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 5), starting at 0. -/
theorem coverageBranchNodes_5_05_00000 :
    nodeClaimChunkValidB branchClaims5Row5 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
