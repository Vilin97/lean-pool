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

/-- Root audit for fixed branch (1, 10). -/
theorem coverageBranchRoot_1_10 :
    branchClaimRootValidB 1 10 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 27). -/
theorem coverageBranchRoot_3_27 :
    branchClaimRootValidB 3 27 (.search branchClaims3Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 192. -/
theorem coverageBranchNodes_3_26_00192 :
    nodeClaimChunkValidB branchClaims3Row26 192 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 224. -/
theorem coverageBranchNodes_3_26_00224 :
    nodeClaimChunkValidB branchClaims3Row26 224 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 256. -/
theorem coverageBranchNodes_3_26_00256 :
    nodeClaimChunkValidB branchClaims3Row26 256 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 0. -/
theorem coverageBranchNodes_3_27_00000 :
    nodeClaimChunkValidB branchClaims3Row27 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
