/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 20). -/
theorem coverageBranchRoot_0_20 :
    branchClaimRootValidB 0 20 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 3). -/
theorem coverageBranchRoot_5_03 :
    branchClaimRootValidB 5 3 (.patternThree 180) = true := by
  rfl

/-- Root audit for fixed branch (2, 17). -/
theorem coverageBranchRoot_2_17 :
    branchClaimRootValidB 2 17 (.search branchClaims_2_17) = true := by
  rfl

/-- Root audit for fixed branch (2, 18). -/
theorem coverageBranchRoot_2_18 :
    branchClaimRootValidB 2 18 (.search branchClaims_2_18) = true := by
  rfl

/-- Node audit for fixed branch (2, 17), starting at 0. -/
theorem coverageBranchNodes_2_17_00000 :
    nodeClaimChunkValidB branchClaims_2_17 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 17), starting at 64. -/
theorem coverageBranchNodes_2_17_00064 :
    nodeClaimChunkValidB branchClaims_2_17 64 60 = true := by
  rfl

/-- Node audit for fixed branch (2, 18), starting at 0. -/
theorem coverageBranchNodes_2_18_00000 :
    nodeClaimChunkValidB branchClaims_2_18 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 18), starting at 64. -/
theorem coverageBranchNodes_2_18_00064 :
    nodeClaimChunkValidB branchClaims_2_18 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
