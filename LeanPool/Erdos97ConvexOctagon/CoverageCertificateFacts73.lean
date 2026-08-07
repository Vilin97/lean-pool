/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 29). -/
theorem coverageBranchRoot_3_29 :
    branchClaimRootValidB 3 29 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 9). -/
theorem coverageBranchRoot_6_09 :
    branchClaimRootValidB 6 9 (.search branchClaims_6_9) = true := by
  rfl

/-- Root audit for fixed branch (6, 10). -/
theorem coverageBranchRoot_6_10 :
    branchClaimRootValidB 6 10 (.search branchClaims_6_10) = true := by
  rfl

/-- Node audit for fixed branch (6, 8), starting at 64. -/
theorem coverageBranchNodes_6_08_00064 :
    nodeClaimChunkValidB branchClaims_6_8 64 57 = true := by
  rfl

/-- Node audit for fixed branch (6, 9), starting at 0. -/
theorem coverageBranchNodes_6_09_00000 :
    nodeClaimChunkValidB branchClaims_6_9 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 9), starting at 64. -/
theorem coverageBranchNodes_6_09_00064 :
    nodeClaimChunkValidB branchClaims_6_9 64 51 = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 0. -/
theorem coverageBranchNodes_6_10_00000 :
    nodeClaimChunkValidB branchClaims_6_10 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
