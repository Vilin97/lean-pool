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

/-- Root audit for fixed branch (0, 8). -/
theorem coverageBranchRoot_0_08 :
    branchClaimRootValidB 0 8 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 26). -/
theorem coverageBranchRoot_4_26 :
    branchClaimRootValidB 4 26 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 30). -/
theorem coverageBranchRoot_1_30 :
    branchClaimRootValidB 1 30 (.search branchClaims1Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 64. -/
theorem coverageBranchNodes_1_29_00064 :
    nodeClaimChunkValidB branchClaims1Row29 64 3 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 0. -/
theorem coverageBranchNodes_1_30_00000 :
    nodeClaimChunkValidB branchClaims1Row30 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 64. -/
theorem coverageBranchNodes_1_30_00064 :
    nodeClaimChunkValidB branchClaims1Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 128. -/
theorem coverageBranchNodes_1_30_00128 :
    nodeClaimChunkValidB branchClaims1Row30 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
