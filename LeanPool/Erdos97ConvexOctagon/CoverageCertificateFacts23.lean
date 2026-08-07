/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 23). -/
theorem coverageBranchRoot_0_23 :
    branchClaimRootValidB 0 23 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 21). -/
theorem coverageBranchRoot_5_21 :
    branchClaimRootValidB 5 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (2, 27). -/
theorem coverageBranchRoot_2_27 :
    branchClaimRootValidB 2 27 (.search branchClaims_2_27) = true := by
  rfl

/-- Root audit for fixed branch (2, 28). -/
theorem coverageBranchRoot_2_28 :
    branchClaimRootValidB 2 28 (.search branchClaims_2_28) = true := by
  rfl

/-- Node audit for fixed branch (2, 26), starting at 64. -/
theorem coverageBranchNodes_2_26_00064 :
    nodeClaimChunkValidB branchClaims_2_26 64 34 = true := by
  rfl

/-- Node audit for fixed branch (2, 27), starting at 0. -/
theorem coverageBranchNodes_2_27_00000 :
    nodeClaimChunkValidB branchClaims_2_27 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 27), starting at 64. -/
theorem coverageBranchNodes_2_27_00064 :
    nodeClaimChunkValidB branchClaims_2_27 64 26 = true := by
  rfl

/-- Node audit for fixed branch (2, 28), starting at 0. -/
theorem coverageBranchNodes_2_28_00000 :
    nodeClaimChunkValidB branchClaims_2_28 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
