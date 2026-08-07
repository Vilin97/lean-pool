/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 7). -/
theorem coverageBranchRoot_0_07 :
    branchClaimRootValidB 0 7 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 21). -/
theorem coverageBranchRoot_4_21 :
    branchClaimRootValidB 4 21 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 28). -/
theorem coverageBranchRoot_1_28 :
    branchClaimRootValidB 1 28 (.search branchClaims_1_28) = true := by
  rfl

/-- Root audit for fixed branch (1, 29). -/
theorem coverageBranchRoot_1_29 :
    branchClaimRootValidB 1 29 (.search branchClaims_1_29) = true := by
  rfl

/-- Node audit for fixed branch (1, 28), starting at 0. -/
theorem coverageBranchNodes_1_28_00000 :
    nodeClaimChunkValidB branchClaims_1_28 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 28), starting at 64. -/
theorem coverageBranchNodes_1_28_00064 :
    nodeClaimChunkValidB branchClaims_1_28 64 56 = true := by
  rfl

/-- Node audit for fixed branch (1, 29), starting at 0. -/
theorem coverageBranchNodes_1_29_00000 :
    nodeClaimChunkValidB branchClaims_1_29 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 29), starting at 64. -/
theorem coverageBranchNodes_1_29_00064 :
    nodeClaimChunkValidB branchClaims_1_29 64 3 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
