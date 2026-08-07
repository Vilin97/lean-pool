/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 13). -/
theorem coverageBranchRoot_3_13 :
    branchClaimRootValidB 3 13 (.patternThree 2) = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 128. -/
theorem coverageBranchNodes_5_28_00128 :
    nodeClaimChunkValidB branchClaims_5_28 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 192. -/
theorem coverageBranchNodes_5_28_00192 :
    nodeClaimChunkValidB branchClaims_5_28 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 256. -/
theorem coverageBranchNodes_5_28_00256 :
    nodeClaimChunkValidB branchClaims_5_28 256 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 320. -/
theorem coverageBranchNodes_5_28_00320 :
    nodeClaimChunkValidB branchClaims_5_28 320 14 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
