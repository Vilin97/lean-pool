/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData16

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 17). -/
theorem coverageBranchRoot_3_17 :
    branchClaimRootValidB 3 17 (.patternThree 4) = true := by
  rfl

/-- Root audit for fixed branch (5, 32). -/
theorem coverageBranchRoot_5_32 :
    branchClaimRootValidB 5 32 (.search branchClaims_5_32) = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 0. -/
theorem coverageBranchNodes_5_32_00000 :
    nodeClaimChunkValidB branchClaims_5_32 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 64. -/
theorem coverageBranchNodes_5_32_00064 :
    nodeClaimChunkValidB branchClaims_5_32 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 128. -/
theorem coverageBranchNodes_5_32_00128 :
    nodeClaimChunkValidB branchClaims_5_32 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 192. -/
theorem coverageBranchNodes_5_32_00192 :
    nodeClaimChunkValidB branchClaims_5_32 192 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
