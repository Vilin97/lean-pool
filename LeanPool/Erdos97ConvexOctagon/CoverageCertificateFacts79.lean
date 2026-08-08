/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 3). -/
theorem coverageBranchRoot_4_03 :
    branchClaimRootValidB 4 3 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 13). -/
theorem coverageBranchRoot_6_13 :
    branchClaimRootValidB 6 13 (.search branchClaims6Row13) = true := by
  rfl

/-- Node audit for fixed branch (6, 12), starting at 64. -/
theorem coverageBranchNodes_6_12_00064 :
    nodeClaimChunkValidB branchClaims6Row12 64 61 = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 0. -/
theorem coverageBranchNodes_6_13_00000 :
    nodeClaimChunkValidB branchClaims6Row13 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 64. -/
theorem coverageBranchNodes_6_13_00064 :
    nodeClaimChunkValidB branchClaims6Row13 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 128. -/
theorem coverageBranchNodes_6_13_00128 :
    nodeClaimChunkValidB branchClaims6Row13 128 5 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
