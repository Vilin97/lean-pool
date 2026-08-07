/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 4). -/
theorem coverageBranchRoot_0_04 :
    branchClaimRootValidB 0 4 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 22). -/
theorem coverageBranchRoot_4_22 :
    branchClaimRootValidB 4 22 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 17). -/
theorem coverageBranchRoot_1_17 :
    branchClaimRootValidB 1 17 (.search branchClaims_1_17) = true := by
  rfl

/-- Root audit for fixed branch (1, 18). -/
theorem coverageBranchRoot_1_18 :
    branchClaimRootValidB 1 18 (.search branchClaims_1_18) = true := by
  rfl

/-- Node audit for fixed branch (1, 17), starting at 0. -/
theorem coverageBranchNodes_1_17_00000 :
    nodeClaimChunkValidB branchClaims_1_17 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 17), starting at 64. -/
theorem coverageBranchNodes_1_17_00064 :
    nodeClaimChunkValidB branchClaims_1_17 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 17), starting at 128. -/
theorem coverageBranchNodes_1_17_00128 :
    nodeClaimChunkValidB branchClaims_1_17 128 10 = true := by
  rfl

/-- Node audit for fixed branch (1, 18), starting at 0. -/
theorem coverageBranchNodes_1_18_00000 :
    nodeClaimChunkValidB branchClaims_1_18 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
