/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 1). -/
theorem coverageBranchRoot_4_01 :
    branchClaimRootValidB 4 1 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 10). -/
theorem coverageBranchRoot_6_10 :
    branchClaimRootValidB 6 10 (.search branchClaims_6_10) = true := by
  rfl

/-- Node audit for fixed branch (6, 9), starting at 64. -/
theorem coverageBranchNodes_6_09_00064 :
    nodeClaimChunkValidB branchClaims_6_9 64 51 = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 0. -/
theorem coverageBranchNodes_6_10_00000 :
    nodeClaimChunkValidB branchClaims_6_10 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 64. -/
theorem coverageBranchNodes_6_10_00064 :
    nodeClaimChunkValidB branchClaims_6_10 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 128. -/
theorem coverageBranchNodes_6_10_00128 :
    nodeClaimChunkValidB branchClaims_6_10 128 30 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
