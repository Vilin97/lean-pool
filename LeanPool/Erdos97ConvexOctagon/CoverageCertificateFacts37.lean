/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 2). -/
theorem coverageBranchRoot_1_02 :
    branchClaimRootValidB 1 2 (.patternThree 178) = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 64. -/
theorem coverageBranchNodes_3_25_00064 :
    nodeClaimChunkValidB branchClaims3Row25 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 128. -/
theorem coverageBranchNodes_3_25_00128 :
    nodeClaimChunkValidB branchClaims3Row25 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 192. -/
theorem coverageBranchNodes_3_25_00192 :
    nodeClaimChunkValidB branchClaims3Row25 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 256. -/
theorem coverageBranchNodes_3_25_00256 :
    nodeClaimChunkValidB branchClaims3Row25 256 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
