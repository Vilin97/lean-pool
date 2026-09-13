/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 34). -/
theorem coverageBranchRoot_0_34 :
    branchClaimRootValidB 0 34 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 33). -/
theorem coverageBranchRoot_6_33 :
    branchClaimRootValidB 6 33 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 23). -/
theorem coverageBranchRoot_3_23 :
    branchClaimRootValidB 3 23 (.search branchClaims3Row23) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 0. -/
theorem coverageBranchNodes_3_23_00000 :
    nodeClaimChunkValidB branchClaims3Row23 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 64. -/
theorem coverageBranchNodes_3_23_00064 :
    nodeClaimChunkValidB branchClaims3Row23 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 128. -/
theorem coverageBranchNodes_3_23_00128 :
    nodeClaimChunkValidB branchClaims3Row23 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 192. -/
theorem coverageBranchNodes_3_23_00192 :
    nodeClaimChunkValidB branchClaims3Row23 192 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
