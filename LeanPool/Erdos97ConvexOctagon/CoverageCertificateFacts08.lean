/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 8). -/
theorem coverageBranchRoot_0_08 :
    branchClaimRootValidB 0 8 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 22). -/
theorem coverageBranchRoot_4_22 :
    branchClaimRootValidB 4 22 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 30). -/
theorem coverageBranchRoot_1_30 :
    branchClaimRootValidB 1 30 (.search branchClaims_1_30) = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 0. -/
theorem coverageBranchNodes_1_30_00000 :
    nodeClaimChunkValidB branchClaims_1_30 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 64. -/
theorem coverageBranchNodes_1_30_00064 :
    nodeClaimChunkValidB branchClaims_1_30 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 128. -/
theorem coverageBranchNodes_1_30_00128 :
    nodeClaimChunkValidB branchClaims_1_30 128 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 192. -/
theorem coverageBranchNodes_1_30_00192 :
    nodeClaimChunkValidB branchClaims_1_30 192 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
