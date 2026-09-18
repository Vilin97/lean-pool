/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 13). -/
theorem coverageBranchRoot_2_13 :
    branchClaimRootValidB 2 13 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 15). -/
theorem coverageBranchRoot_5_15 :
    branchClaimRootValidB 5 15 (.search branchClaims5Row15) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 320. -/
theorem coverageBranchNodes_5_14_00320 :
    nodeClaimChunkValidB branchClaims5Row14 320 44 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 0. -/
theorem coverageBranchNodes_5_15_00000 :
    nodeClaimChunkValidB branchClaims5Row15 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 64. -/
theorem coverageBranchNodes_5_15_00064 :
    nodeClaimChunkValidB branchClaims5Row15 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 128. -/
theorem coverageBranchNodes_5_15_00128 :
    nodeClaimChunkValidB branchClaims5Row15 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
