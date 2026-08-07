/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 23). -/
theorem coverageBranchRoot_0_23 :
    branchClaimRootValidB 0 23 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 2). -/
theorem coverageBranchRoot_5_02 :
    branchClaimRootValidB 5 2 (.patternThree 180) = true := by
  rfl

/-- Root audit for fixed branch (2, 28). -/
theorem coverageBranchRoot_2_28 :
    branchClaimRootValidB 2 28 (.search branchClaims_2_28) = true := by
  rfl

/-- Root audit for fixed branch (2, 29). -/
theorem coverageBranchRoot_2_29 :
    branchClaimRootValidB 2 29 (.search branchClaims_2_29) = true := by
  rfl

/-- Node audit for fixed branch (2, 28), starting at 0. -/
theorem coverageBranchNodes_2_28_00000 :
    nodeClaimChunkValidB branchClaims_2_28 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 28), starting at 64. -/
theorem coverageBranchNodes_2_28_00064 :
    nodeClaimChunkValidB branchClaims_2_28 64 32 = true := by
  rfl

/-- Node audit for fixed branch (2, 29), starting at 0. -/
theorem coverageBranchNodes_2_29_00000 :
    nodeClaimChunkValidB branchClaims_2_29 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 29), starting at 64. -/
theorem coverageBranchNodes_2_29_00064 :
    nodeClaimChunkValidB branchClaims_2_29 64 39 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
