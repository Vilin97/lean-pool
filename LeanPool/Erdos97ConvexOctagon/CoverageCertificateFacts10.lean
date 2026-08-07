/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 10). -/
theorem coverageBranchRoot_0_10 :
    branchClaimRootValidB 0 10 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 24). -/
theorem coverageBranchRoot_4_24 :
    branchClaimRootValidB 4 24 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 32). -/
theorem coverageBranchRoot_1_32 :
    branchClaimRootValidB 1 32 (.search branchClaims_1_32) = true := by
  rfl

/-- Node audit for fixed branch (1, 31), starting at 192. -/
theorem coverageBranchNodes_1_31_00192 :
    nodeClaimChunkValidB branchClaims_1_31 192 58 = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 0. -/
theorem coverageBranchNodes_1_32_00000 :
    nodeClaimChunkValidB branchClaims_1_32 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 64. -/
theorem coverageBranchNodes_1_32_00064 :
    nodeClaimChunkValidB branchClaims_1_32 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 128. -/
theorem coverageBranchNodes_1_32_00128 :
    nodeClaimChunkValidB branchClaims_1_32 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
