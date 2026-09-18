/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 25). -/
theorem coverageBranchRoot_0_25 :
    branchClaimRootValidB 0 25 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 23). -/
theorem coverageBranchRoot_5_23 :
    branchClaimRootValidB 5 23 (.patternThree 3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 31). -/
theorem coverageBranchRoot_2_31 :
    branchClaimRootValidB 2 31 (.search branchClaims2Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 64. -/
theorem coverageBranchNodes_2_30_00064 :
    nodeClaimChunkValidB branchClaims2Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 128. -/
theorem coverageBranchNodes_2_30_00128 :
    nodeClaimChunkValidB branchClaims2Row30 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 192. -/
theorem coverageBranchNodes_2_30_00192 :
    nodeClaimChunkValidB branchClaims2Row30 192 14 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 31), starting at 0. -/
theorem coverageBranchNodes_2_31_00000 :
    nodeClaimChunkValidB branchClaims2Row31 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
