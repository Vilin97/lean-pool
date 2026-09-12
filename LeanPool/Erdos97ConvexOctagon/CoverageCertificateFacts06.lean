/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 6). -/
theorem coverageBranchRoot_0_06 :
    branchClaimRootValidB 0 6 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 24). -/
theorem coverageBranchRoot_4_24 :
    branchClaimRootValidB 4 24 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 27). -/
theorem coverageBranchRoot_1_27 :
    branchClaimRootValidB 1 27 (.search branchClaims1Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 26), starting at 64. -/
theorem coverageBranchNodes_1_26_00064 :
    nodeClaimChunkValidB branchClaims1Row26 64 53 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 0. -/
theorem coverageBranchNodes_1_27_00000 :
    nodeClaimChunkValidB branchClaims1Row27 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 64. -/
theorem coverageBranchNodes_1_27_00064 :
    nodeClaimChunkValidB branchClaims1Row27 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 128. -/
theorem coverageBranchNodes_1_27_00128 :
    nodeClaimChunkValidB branchClaims1Row27 128 36 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
