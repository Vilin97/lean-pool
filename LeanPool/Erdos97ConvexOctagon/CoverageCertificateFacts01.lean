/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 1). -/
theorem coverageBranchRoot_0_01 :
    branchClaimRootValidB 0 1 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 15). -/
theorem coverageBranchRoot_4_15 :
    branchClaimRootValidB 4 15 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 6). -/
theorem coverageBranchRoot_1_06 :
    branchClaimRootValidB 1 6 (.search branchClaims_1_6) = true := by
  rfl

/-- Root audit for fixed branch (1, 7). -/
theorem coverageBranchRoot_1_07 :
    branchClaimRootValidB 1 7 (.search branchClaims_1_7) = true := by
  rfl

/-- Node audit for fixed branch (1, 6), starting at 0. -/
theorem coverageBranchNodes_1_06_00000 :
    nodeClaimChunkValidB branchClaims_1_6 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 6), starting at 64. -/
theorem coverageBranchNodes_1_06_00064 :
    nodeClaimChunkValidB branchClaims_1_6 64 57 = true := by
  rfl

/-- Node audit for fixed branch (1, 7), starting at 0. -/
theorem coverageBranchNodes_1_07_00000 :
    nodeClaimChunkValidB branchClaims_1_7 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 7), starting at 64. -/
theorem coverageBranchNodes_1_07_00064 :
    nodeClaimChunkValidB branchClaims_1_7 64 51 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
