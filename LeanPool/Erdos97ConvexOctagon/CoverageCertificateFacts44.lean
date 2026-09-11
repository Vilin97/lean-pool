/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 15). -/
theorem coverageBranchRoot_1_15 :
    branchClaimRootValidB 1 15 (.patternThree 178) = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 64. -/
theorem coverageBranchNodes_3_31_00064 :
    nodeClaimChunkValidB branchClaims3Row31 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 128. -/
theorem coverageBranchNodes_3_31_00128 :
    nodeClaimChunkValidB branchClaims3Row31 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 192. -/
theorem coverageBranchNodes_3_31_00192 :
    nodeClaimChunkValidB branchClaims3Row31 192 26 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 218. -/
theorem coverageBranchNodes_3_31_00218 :
    nodeClaimChunkValidB branchClaims3Row31 218 27 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
