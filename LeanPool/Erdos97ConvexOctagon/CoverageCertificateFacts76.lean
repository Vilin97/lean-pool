/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData18

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 0). -/
theorem coverageBranchRoot_4_00 :
    branchClaimRootValidB 4 0 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 14). -/
theorem coverageBranchRoot_6_14 :
    branchClaimRootValidB 6 14 (.search branchClaims_6_14) = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 64. -/
theorem coverageBranchNodes_6_13_00064 :
    nodeClaimChunkValidB branchClaims_6_13 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 128. -/
theorem coverageBranchNodes_6_13_00128 :
    nodeClaimChunkValidB branchClaims_6_13 128 5 = true := by
  rfl

/-- Node audit for fixed branch (6, 14), starting at 0. -/
theorem coverageBranchNodes_6_14_00000 :
    nodeClaimChunkValidB branchClaims_6_14 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 14), starting at 64. -/
theorem coverageBranchNodes_6_14_00064 :
    nodeClaimChunkValidB branchClaims_6_14 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
