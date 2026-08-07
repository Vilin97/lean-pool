/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 23). -/
theorem coverageBranchRoot_1_23 :
    branchClaimRootValidB 1 23 (.patternThree 179) = true := by
  rfl

/-- Root audit for fixed branch (5, 10). -/
theorem coverageBranchRoot_5_10 :
    branchClaimRootValidB 5 10 (.search branchClaims_5_10) = true := by
  rfl

/-- Root audit for fixed branch (5, 11). -/
theorem coverageBranchRoot_5_11 :
    branchClaimRootValidB 5 11 (.search branchClaims_5_11) = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 0. -/
theorem coverageBranchNodes_5_10_00000 :
    nodeClaimChunkValidB branchClaims_5_10 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 64. -/
theorem coverageBranchNodes_5_10_00064 :
    nodeClaimChunkValidB branchClaims_5_10 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 128. -/
theorem coverageBranchNodes_5_10_00128 :
    nodeClaimChunkValidB branchClaims_5_10 128 31 = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 0. -/
theorem coverageBranchNodes_5_11_00000 :
    nodeClaimChunkValidB branchClaims_5_11 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
