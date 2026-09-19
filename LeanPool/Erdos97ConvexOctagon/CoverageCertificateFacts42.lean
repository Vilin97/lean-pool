/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 13). -/
theorem coverageBranchRoot_1_13 :
    branchClaimRootValidB 1 13 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 30). -/
theorem coverageBranchRoot_3_30 :
    branchClaimRootValidB 3 30 (.search branchClaims3Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 192. -/
theorem coverageBranchNodes_3_28_00192 :
    nodeClaimChunkValidB branchClaims3Row28 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 256. -/
theorem coverageBranchNodes_3_28_00256 :
    nodeClaimChunkValidB branchClaims3Row28 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 320. -/
theorem coverageBranchNodes_3_28_00320 :
    nodeClaimChunkValidB branchClaims3Row28 320 21 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 30), starting at 0. -/
theorem coverageBranchNodes_3_30_00000 :
    nodeClaimChunkValidB branchClaims3Row30 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
