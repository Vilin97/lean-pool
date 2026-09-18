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

/-- Root audit for fixed branch (0, 0). -/
theorem coverageBranchRoot_0_00 :
    branchClaimRootValidB 0 0 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 18). -/
theorem coverageBranchRoot_4_18 :
    branchClaimRootValidB 4 18 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 4). -/
theorem coverageBranchRoot_1_04 :
    branchClaimRootValidB 1 4 (.search branchClaims1Row4) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 5). -/
theorem coverageBranchRoot_1_05 :
    branchClaimRootValidB 1 5 (.search branchClaims1Row5) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 4), starting at 0. -/
theorem coverageBranchNodes_1_04_00000 :
    nodeClaimChunkValidB branchClaims1Row4 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 4), starting at 64. -/
theorem coverageBranchNodes_1_04_00064 :
    nodeClaimChunkValidB branchClaims1Row4 64 38 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 5), starting at 0. -/
theorem coverageBranchNodes_1_05_00000 :
    nodeClaimChunkValidB branchClaims1Row5 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 5), starting at 64. -/
theorem coverageBranchNodes_1_05_00064 :
    nodeClaimChunkValidB branchClaims1Row5 64 37 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
