/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 21). -/
theorem coverageBranchRoot_0_21 :
    branchClaimRootValidB 0 21 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 13). -/
theorem coverageBranchRoot_5_13 :
    branchClaimRootValidB 5 13 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (2, 23). -/
theorem coverageBranchRoot_2_23 :
    branchClaimRootValidB 2 23 (.search branchClaims_2_23) = true := by
  rfl

/-- Root audit for fixed branch (2, 24). -/
theorem coverageBranchRoot_2_24 :
    branchClaimRootValidB 2 24 (.search branchClaims_2_24) = true := by
  rfl

/-- Node audit for fixed branch (2, 18), starting at 128. -/
theorem coverageBranchNodes_2_18_00128 :
    nodeClaimChunkValidB branchClaims_2_18 128 12 = true := by
  rfl

/-- Node audit for fixed branch (2, 23), starting at 0. -/
theorem coverageBranchNodes_2_23_00000 :
    nodeClaimChunkValidB branchClaims_2_23 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 23), starting at 64. -/
theorem coverageBranchNodes_2_23_00064 :
    nodeClaimChunkValidB branchClaims_2_23 64 56 = true := by
  rfl

/-- Node audit for fixed branch (2, 24), starting at 0. -/
theorem coverageBranchNodes_2_24_00000 :
    nodeClaimChunkValidB branchClaims_2_24 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
