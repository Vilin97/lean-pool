/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 25). -/
theorem coverageBranchRoot_1_25 :
    branchClaimRootValidB 1 25 (.patternThree 179) = true := by
  rfl

/-- Root audit for fixed branch (5, 14). -/
theorem coverageBranchRoot_5_14 :
    branchClaimRootValidB 5 14 (.search branchClaims_5_14) = true := by
  rfl

/-- Node audit for fixed branch (5, 12), starting at 128. -/
theorem coverageBranchNodes_5_12_00128 :
    nodeClaimChunkValidB branchClaims_5_12 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 12), starting at 192. -/
theorem coverageBranchNodes_5_12_00192 :
    nodeClaimChunkValidB branchClaims_5_12 192 10 = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 0. -/
theorem coverageBranchNodes_5_14_00000 :
    nodeClaimChunkValidB branchClaims_5_14 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 64. -/
theorem coverageBranchNodes_5_14_00064 :
    nodeClaimChunkValidB branchClaims_5_14 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
