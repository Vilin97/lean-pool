/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 16). -/
theorem coverageBranchRoot_3_16 :
    branchClaimRootValidB 3 16 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 29). -/
theorem coverageBranchRoot_5_29 :
    branchClaimRootValidB 5 29 (.search branchClaims_5_29) = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 320. -/
theorem coverageBranchNodes_5_28_00320 :
    nodeClaimChunkValidB branchClaims_5_28 320 14 = true := by
  rfl

/-- Node audit for fixed branch (5, 29), starting at 0. -/
theorem coverageBranchNodes_5_29_00000 :
    nodeClaimChunkValidB branchClaims_5_29 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 29), starting at 64. -/
theorem coverageBranchNodes_5_29_00064 :
    nodeClaimChunkValidB branchClaims_5_29 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 29), starting at 128. -/
theorem coverageBranchNodes_5_29_00128 :
    nodeClaimChunkValidB branchClaims_5_29 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
