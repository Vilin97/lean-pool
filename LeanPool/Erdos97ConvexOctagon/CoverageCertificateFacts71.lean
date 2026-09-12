/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 21). -/
theorem coverageBranchRoot_3_21 :
    branchClaimRootValidB 3 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 34). -/
theorem coverageBranchRoot_5_34 :
    branchClaimRootValidB 5 34 (.search branchClaims5Row34) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 352. -/
theorem coverageBranchNodes_5_32_00352 :
    nodeClaimChunkValidB branchClaims5Row32 352 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 384. -/
theorem coverageBranchNodes_5_32_00384 :
    nodeClaimChunkValidB branchClaims5Row32 384 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 413. -/
theorem coverageBranchNodes_5_32_00413 :
    nodeClaimChunkValidB branchClaims5Row32 413 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 0. -/
theorem coverageBranchNodes_5_34_00000 :
    nodeClaimChunkValidB branchClaims5Row34 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
