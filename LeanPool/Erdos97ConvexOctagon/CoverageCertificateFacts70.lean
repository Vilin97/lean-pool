/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 20). -/
theorem coverageBranchRoot_3_20 :
    branchClaimRootValidB 3 20 (.patternThree 1) = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 128. -/
theorem coverageBranchNodes_5_32_00128 :
    nodeClaimChunkValidB branchClaims5Row32 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 192. -/
theorem coverageBranchNodes_5_32_00192 :
    nodeClaimChunkValidB branchClaims5Row32 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 256. -/
theorem coverageBranchNodes_5_32_00256 :
    nodeClaimChunkValidB branchClaims5Row32 256 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 320. -/
theorem coverageBranchNodes_5_32_00320 :
    nodeClaimChunkValidB branchClaims5Row32 320 32 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
