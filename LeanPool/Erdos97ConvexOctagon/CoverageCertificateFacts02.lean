/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 2). -/
theorem coverageBranchRoot_0_02 :
    branchClaimRootValidB 0 2 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 20). -/
theorem coverageBranchRoot_4_20 :
    branchClaimRootValidB 4 20 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 8). -/
theorem coverageBranchRoot_1_08 :
    branchClaimRootValidB 1 8 (.search branchClaims_1_8) = true := by
  rfl

/-- Root audit for fixed branch (1, 9). -/
theorem coverageBranchRoot_1_09 :
    branchClaimRootValidB 1 9 (.search branchClaims_1_9) = true := by
  rfl

/-- Node audit for fixed branch (1, 8), starting at 0. -/
theorem coverageBranchNodes_1_08_00000 :
    nodeClaimChunkValidB branchClaims_1_8 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 8), starting at 64. -/
theorem coverageBranchNodes_1_08_00064 :
    nodeClaimChunkValidB branchClaims_1_8 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 8), starting at 128. -/
theorem coverageBranchNodes_1_08_00128 :
    nodeClaimChunkValidB branchClaims_1_8 128 18 = true := by
  rfl

/-- Node audit for fixed branch (1, 9), starting at 0. -/
theorem coverageBranchNodes_1_09_00000 :
    nodeClaimChunkValidB branchClaims_1_9 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
