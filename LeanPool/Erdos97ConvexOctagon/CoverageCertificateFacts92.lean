/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 16). -/
theorem coverageBranchRoot_4_16 :
    branchClaimRootValidB 4 16 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 32). -/
theorem coverageBranchRoot_6_32 :
    branchClaimRootValidB 6 32 (.search branchClaims_6_32) = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 192. -/
theorem coverageBranchNodes_6_31_00192 :
    nodeClaimChunkValidB branchClaims_6_31 192 29 = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 221. -/
theorem coverageBranchNodes_6_31_00221 :
    nodeClaimChunkValidB branchClaims_6_31 221 29 = true := by
  rfl

/-- Node audit for fixed branch (6, 32), starting at 0. -/
theorem coverageBranchNodes_6_32_00000 :
    nodeClaimChunkValidB branchClaims_6_32 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 32), starting at 64. -/
theorem coverageBranchNodes_6_32_00064 :
    nodeClaimChunkValidB branchClaims_6_32 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
