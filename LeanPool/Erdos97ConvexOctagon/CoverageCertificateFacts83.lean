/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 7). -/
theorem coverageBranchRoot_4_07 :
    branchClaimRootValidB 4 7 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 18). -/
theorem coverageBranchRoot_6_18 :
    branchClaimRootValidB 6 18 (.search branchClaims_6_18) = true := by
  rfl

/-- Node audit for fixed branch (6, 18), starting at 0. -/
theorem coverageBranchNodes_6_18_00000 :
    nodeClaimChunkValidB branchClaims_6_18 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 18), starting at 64. -/
theorem coverageBranchNodes_6_18_00064 :
    nodeClaimChunkValidB branchClaims_6_18 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 18), starting at 128. -/
theorem coverageBranchNodes_6_18_00128 :
    nodeClaimChunkValidB branchClaims_6_18 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 18), starting at 192. -/
theorem coverageBranchNodes_6_18_00192 :
    nodeClaimChunkValidB branchClaims_6_18 192 3 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
