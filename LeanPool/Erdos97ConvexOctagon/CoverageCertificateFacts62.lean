/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 9). -/
theorem coverageBranchRoot_3_09 :
    branchClaimRootValidB 3 9 (.patternThree 5) = true := by
  rfl

/-- Root audit for fixed branch (5, 28). -/
theorem coverageBranchRoot_5_28 :
    branchClaimRootValidB 5 28 (.search branchClaims_5_28) = true := by
  rfl

/-- Node audit for fixed branch (5, 27), starting at 320. -/
theorem coverageBranchNodes_5_27_00320 :
    nodeClaimChunkValidB branchClaims_5_27 320 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 27), starting at 384. -/
theorem coverageBranchNodes_5_27_00384 :
    nodeClaimChunkValidB branchClaims_5_27 384 8 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 0. -/
theorem coverageBranchNodes_5_28_00000 :
    nodeClaimChunkValidB branchClaims_5_28 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 28), starting at 64. -/
theorem coverageBranchNodes_5_28_00064 :
    nodeClaimChunkValidB branchClaims_5_28 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
