/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 12). -/
theorem coverageBranchRoot_1_12 :
    branchClaimRootValidB 1 12 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (3, 28). -/
theorem coverageBranchRoot_3_28 :
    branchClaimRootValidB 3 28 (.search branchClaims_3_28) = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 320. -/
theorem coverageBranchNodes_3_27_00320 :
    nodeClaimChunkValidB branchClaims_3_27 320 25 = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 0. -/
theorem coverageBranchNodes_3_28_00000 :
    nodeClaimChunkValidB branchClaims_3_28 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 64. -/
theorem coverageBranchNodes_3_28_00064 :
    nodeClaimChunkValidB branchClaims_3_28 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 128. -/
theorem coverageBranchNodes_3_28_00128 :
    nodeClaimChunkValidB branchClaims_3_28 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
