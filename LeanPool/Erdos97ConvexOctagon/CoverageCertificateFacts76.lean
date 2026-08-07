/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 0). -/
theorem coverageBranchRoot_4_00 :
    branchClaimRootValidB 4 0 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 8). -/
theorem coverageBranchRoot_6_08 :
    branchClaimRootValidB 6 8 (.search branchClaims_6_8) = true := by
  rfl

/-- Root audit for fixed branch (6, 9). -/
theorem coverageBranchRoot_6_09 :
    branchClaimRootValidB 6 9 (.search branchClaims_6_9) = true := by
  rfl

/-- Node audit for fixed branch (6, 8), starting at 0. -/
theorem coverageBranchNodes_6_08_00000 :
    nodeClaimChunkValidB branchClaims_6_8 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 8), starting at 64. -/
theorem coverageBranchNodes_6_08_00064 :
    nodeClaimChunkValidB branchClaims_6_8 64 28 = true := by
  rfl

/-- Node audit for fixed branch (6, 8), starting at 92. -/
theorem coverageBranchNodes_6_08_00092 :
    nodeClaimChunkValidB branchClaims_6_8 92 29 = true := by
  rfl

/-- Node audit for fixed branch (6, 9), starting at 0. -/
theorem coverageBranchNodes_6_09_00000 :
    nodeClaimChunkValidB branchClaims_6_9 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
