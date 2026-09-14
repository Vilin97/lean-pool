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

/-- Root audit for fixed branch (3, 13). -/
theorem coverageBranchRoot_3_13 :
    branchClaimRootValidB 3 13 (.patternThree 2) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 128. -/
theorem coverageBranchNodes_5_27_00128 :
    nodeClaimChunkValidB branchClaims5Row27 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 192. -/
theorem coverageBranchNodes_5_27_00192 :
    nodeClaimChunkValidB branchClaims5Row27 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 256. -/
theorem coverageBranchNodes_5_27_00256 :
    nodeClaimChunkValidB branchClaims5Row27 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 320. -/
theorem coverageBranchNodes_5_27_00320 :
    nodeClaimChunkValidB branchClaims5Row27 320 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
