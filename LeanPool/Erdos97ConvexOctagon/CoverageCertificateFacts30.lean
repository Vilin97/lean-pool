/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 30). -/
theorem coverageBranchRoot_0_30 :
    branchClaimRootValidB 0 30 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 20). -/
theorem coverageBranchRoot_6_20 :
    branchClaimRootValidB 6 20 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (3, 3). -/
theorem coverageBranchRoot_3_03 :
    branchClaimRootValidB 3 3 (.search branchClaims_3_3) = true := by
  rfl

/-- Root audit for fixed branch (3, 4). -/
theorem coverageBranchRoot_3_04 :
    branchClaimRootValidB 3 4 (.search branchClaims_3_4) = true := by
  rfl

/-- Node audit for fixed branch (3, 2), starting at 64. -/
theorem coverageBranchNodes_3_02_00064 :
    nodeClaimChunkValidB branchClaims_3_2 64 52 = true := by
  rfl

/-- Node audit for fixed branch (3, 3), starting at 0. -/
theorem coverageBranchNodes_3_03_00000 :
    nodeClaimChunkValidB branchClaims_3_3 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 3), starting at 64. -/
theorem coverageBranchNodes_3_03_00064 :
    nodeClaimChunkValidB branchClaims_3_3 64 31 = true := by
  rfl

/-- Node audit for fixed branch (3, 4), starting at 0. -/
theorem coverageBranchNodes_3_04_00000 :
    nodeClaimChunkValidB branchClaims_3_4 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
