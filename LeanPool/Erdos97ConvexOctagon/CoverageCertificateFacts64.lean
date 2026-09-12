/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 14). -/
theorem coverageBranchRoot_3_14 :
    branchClaimRootValidB 3 14 (.patternThree 4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 28). -/
theorem coverageBranchRoot_5_28 :
    branchClaimRootValidB 5 28 (.search branchClaims5Row28) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 384. -/
theorem coverageBranchNodes_5_27_00384 :
    nodeClaimChunkValidB branchClaims5Row27 384 8 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 0. -/
theorem coverageBranchNodes_5_28_00000 :
    nodeClaimChunkValidB branchClaims5Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 64. -/
theorem coverageBranchNodes_5_28_00064 :
    nodeClaimChunkValidB branchClaims5Row28 64 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 96. -/
theorem coverageBranchNodes_5_28_00096 :
    nodeClaimChunkValidB branchClaims5Row28 96 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
