/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 15). -/
theorem coverageBranchRoot_3_15 :
    branchClaimRootValidB 3 15 (.patternThree 5) = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 128. -/
theorem coverageBranchNodes_5_28_00128 :
    nodeClaimChunkValidB branchClaims5Row28 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 192. -/
theorem coverageBranchNodes_5_28_00192 :
    nodeClaimChunkValidB branchClaims5Row28 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 256. -/
theorem coverageBranchNodes_5_28_00256 :
    nodeClaimChunkValidB branchClaims5Row28 256 32 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 288. -/
theorem coverageBranchNodes_5_28_00288 :
    nodeClaimChunkValidB branchClaims5Row28 288 32 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
