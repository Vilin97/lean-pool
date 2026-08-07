/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 3). -/
theorem coverageBranchRoot_0_03 :
    branchClaimRootValidB 0 3 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 17). -/
theorem coverageBranchRoot_4_17 :
    branchClaimRootValidB 4 17 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 16). -/
theorem coverageBranchRoot_1_16 :
    branchClaimRootValidB 1 16 (.search branchClaims_1_16) = true := by
  rfl

/-- Node audit for fixed branch (1, 9), starting at 64. -/
theorem coverageBranchNodes_1_09_00064 :
    nodeClaimChunkValidB branchClaims_1_9 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 9), starting at 128. -/
theorem coverageBranchNodes_1_09_00128 :
    nodeClaimChunkValidB branchClaims_1_9 128 16 = true := by
  rfl

/-- Node audit for fixed branch (1, 16), starting at 0. -/
theorem coverageBranchNodes_1_16_00000 :
    nodeClaimChunkValidB branchClaims_1_16 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 16), starting at 64. -/
theorem coverageBranchNodes_1_16_00064 :
    nodeClaimChunkValidB branchClaims_1_16 64 28 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
