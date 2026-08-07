/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 14). -/
theorem coverageBranchRoot_1_14 :
    branchClaimRootValidB 1 14 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (3, 32). -/
theorem coverageBranchRoot_3_32 :
    branchClaimRootValidB 3 32 (.search branchClaims_3_32) = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 64. -/
theorem coverageBranchNodes_3_31_00064 :
    nodeClaimChunkValidB branchClaims_3_31 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 128. -/
theorem coverageBranchNodes_3_31_00128 :
    nodeClaimChunkValidB branchClaims_3_31 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 192. -/
theorem coverageBranchNodes_3_31_00192 :
    nodeClaimChunkValidB branchClaims_3_31 192 53 = true := by
  rfl

/-- Node audit for fixed branch (3, 32), starting at 0. -/
theorem coverageBranchNodes_3_32_00000 :
    nodeClaimChunkValidB branchClaims_3_32 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
