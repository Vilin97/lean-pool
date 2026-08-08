/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 9). -/
theorem coverageBranchRoot_4_09 :
    branchClaimRootValidB 4 9 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 24). -/
theorem coverageBranchRoot_6_24 :
    branchClaimRootValidB 6 24 (.search branchClaims6Row24) = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 0. -/
theorem coverageBranchNodes_6_24_00000 :
    nodeClaimChunkValidB branchClaims6Row24 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 64. -/
theorem coverageBranchNodes_6_24_00064 :
    nodeClaimChunkValidB branchClaims6Row24 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 128. -/
theorem coverageBranchNodes_6_24_00128 :
    nodeClaimChunkValidB branchClaims6Row24 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 192. -/
theorem coverageBranchNodes_6_24_00192 :
    nodeClaimChunkValidB branchClaims6Row24 192 43 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
