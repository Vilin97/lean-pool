/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 24). -/
theorem coverageBranchRoot_1_24 :
    branchClaimRootValidB 1 24 (.patternThree 179) = true := by
  rfl

/-- Root audit for fixed branch (5, 12). -/
theorem coverageBranchRoot_5_12 :
    branchClaimRootValidB 5 12 (.search branchClaims_5_12) = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 64. -/
theorem coverageBranchNodes_5_11_00064 :
    nodeClaimChunkValidB branchClaims_5_11 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 128. -/
theorem coverageBranchNodes_5_11_00128 :
    nodeClaimChunkValidB branchClaims_5_11 128 25 = true := by
  rfl

/-- Node audit for fixed branch (5, 12), starting at 0. -/
theorem coverageBranchNodes_5_12_00000 :
    nodeClaimChunkValidB branchClaims_5_12 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 12), starting at 64. -/
theorem coverageBranchNodes_5_12_00064 :
    nodeClaimChunkValidB branchClaims_5_12 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
