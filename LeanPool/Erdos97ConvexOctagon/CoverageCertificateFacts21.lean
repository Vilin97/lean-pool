/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 21). -/
theorem coverageBranchRoot_0_21 :
    branchClaimRootValidB 0 21 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 0). -/
theorem coverageBranchRoot_5_00 :
    branchClaimRootValidB 5 0 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (2, 24). -/
theorem coverageBranchRoot_2_24 :
    branchClaimRootValidB 2 24 (.search branchClaims_2_24) = true := by
  rfl

/-- Root audit for fixed branch (2, 25). -/
theorem coverageBranchRoot_2_25 :
    branchClaimRootValidB 2 25 (.search branchClaims_2_25) = true := by
  rfl

/-- Node audit for fixed branch (2, 24), starting at 0. -/
theorem coverageBranchNodes_2_24_00000 :
    nodeClaimChunkValidB branchClaims_2_24 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 24), starting at 64. -/
theorem coverageBranchNodes_2_24_00064 :
    nodeClaimChunkValidB branchClaims_2_24 64 46 = true := by
  rfl

/-- Node audit for fixed branch (2, 25), starting at 0. -/
theorem coverageBranchNodes_2_25_00000 :
    nodeClaimChunkValidB branchClaims_2_25 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 25), starting at 64. -/
theorem coverageBranchNodes_2_25_00064 :
    nodeClaimChunkValidB branchClaims_2_25 64 41 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
