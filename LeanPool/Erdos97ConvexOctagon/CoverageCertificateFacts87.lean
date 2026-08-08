/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 11). -/
theorem coverageBranchRoot_4_11 :
    branchClaimRootValidB 4 11 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 26). -/
theorem coverageBranchRoot_6_26 :
    branchClaimRootValidB 6 26 (.search branchClaims6Row26) = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 0. -/
theorem coverageBranchNodes_6_26_00000 :
    nodeClaimChunkValidB branchClaims6Row26 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 64. -/
theorem coverageBranchNodes_6_26_00064 :
    nodeClaimChunkValidB branchClaims6Row26 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 128. -/
theorem coverageBranchNodes_6_26_00128 :
    nodeClaimChunkValidB branchClaims6Row26 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 192. -/
theorem coverageBranchNodes_6_26_00192 :
    nodeClaimChunkValidB branchClaims6Row26 192 40 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
