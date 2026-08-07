/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 29). -/
theorem coverageBranchRoot_0_29 :
    branchClaimRootValidB 0 29 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 23). -/
theorem coverageBranchRoot_5_23 :
    branchClaimRootValidB 5 23 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (3, 2). -/
theorem coverageBranchRoot_3_02 :
    branchClaimRootValidB 3 2 (.search branchClaims_3_2) = true := by
  rfl

/-- Root audit for fixed branch (3, 3). -/
theorem coverageBranchRoot_3_03 :
    branchClaimRootValidB 3 3 (.search branchClaims_3_3) = true := by
  rfl

/-- Node audit for fixed branch (3, 2), starting at 0. -/
theorem coverageBranchNodes_3_02_00000 :
    nodeClaimChunkValidB branchClaims_3_2 0 64 = true := by
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

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
