/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 20). -/
theorem coverageBranchRoot_0_20 :
    branchClaimRootValidB 0 20 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 34). -/
theorem coverageBranchRoot_4_34 :
    branchClaimRootValidB 4 34 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 23). -/
theorem coverageBranchRoot_2_23 :
    branchClaimRootValidB 2 23 (.search branchClaims_2_23) = true := by
  rfl

/-- Node audit for fixed branch (2, 18), starting at 64. -/
theorem coverageBranchNodes_2_18_00064 :
    nodeClaimChunkValidB branchClaims_2_18 64 64 = true := by
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

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
