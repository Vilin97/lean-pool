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

/-- Root audit for fixed branch (4, 10). -/
theorem coverageBranchRoot_4_10 :
    branchClaimRootValidB 4 10 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 25). -/
theorem coverageBranchRoot_6_25 :
    branchClaimRootValidB 6 25 (.search branchClaims6Row25) = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 0. -/
theorem coverageBranchNodes_6_25_00000 :
    nodeClaimChunkValidB branchClaims6Row25 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 64. -/
theorem coverageBranchNodes_6_25_00064 :
    nodeClaimChunkValidB branchClaims6Row25 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 128. -/
theorem coverageBranchNodes_6_25_00128 :
    nodeClaimChunkValidB branchClaims6Row25 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 192. -/
theorem coverageBranchNodes_6_25_00192 :
    nodeClaimChunkValidB branchClaims6Row25 192 19 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
