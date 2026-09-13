/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 14). -/
theorem coverageBranchRoot_4_14 :
    branchClaimRootValidB 4 14 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 30). -/
theorem coverageBranchRoot_6_30 :
    branchClaimRootValidB 6 30 (.search branchClaims6Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 0. -/
theorem coverageBranchNodes_6_30_00000 :
    nodeClaimChunkValidB branchClaims6Row30 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 64. -/
theorem coverageBranchNodes_6_30_00064 :
    nodeClaimChunkValidB branchClaims6Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 128. -/
theorem coverageBranchNodes_6_30_00128 :
    nodeClaimChunkValidB branchClaims6Row30 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 192. -/
theorem coverageBranchNodes_6_30_00192 :
    nodeClaimChunkValidB branchClaims6Row30 192 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
