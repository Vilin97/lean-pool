/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 4). -/
theorem coverageBranchRoot_4_04 :
    branchClaimRootValidB 4 4 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 14). -/
theorem coverageBranchRoot_6_14 :
    branchClaimRootValidB 6 14 (.search branchClaims6Row14) = true := by
  rfl

/-- Root audit for fixed branch (6, 15). -/
theorem coverageBranchRoot_6_15 :
    branchClaimRootValidB 6 15 (.search branchClaims6Row15) = true := by
  rfl

/-- Node audit for fixed branch (6, 14), starting at 0. -/
theorem coverageBranchNodes_6_14_00000 :
    nodeClaimChunkValidB branchClaims6Row14 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 14), starting at 64. -/
theorem coverageBranchNodes_6_14_00064 :
    nodeClaimChunkValidB branchClaims6Row14 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 14), starting at 128. -/
theorem coverageBranchNodes_6_14_00128 :
    nodeClaimChunkValidB branchClaims6Row14 128 50 = true := by
  rfl

/-- Node audit for fixed branch (6, 15), starting at 0. -/
theorem coverageBranchNodes_6_15_00000 :
    nodeClaimChunkValidB branchClaims6Row15 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
