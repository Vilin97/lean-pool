/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 13). -/
theorem coverageBranchRoot_2_13 :
    branchClaimRootValidB 2 13 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 16). -/
theorem coverageBranchRoot_5_16 :
    branchClaimRootValidB 5 16 (.search branchClaims_5_16) = true := by
  rfl

/-- Node audit for fixed branch (5, 15), starting at 256. -/
theorem coverageBranchNodes_5_15_00256 :
    nodeClaimChunkValidB branchClaims_5_15 256 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 15), starting at 320. -/
theorem coverageBranchNodes_5_15_00320 :
    nodeClaimChunkValidB branchClaims_5_15 320 45 = true := by
  rfl

/-- Node audit for fixed branch (5, 16), starting at 0. -/
theorem coverageBranchNodes_5_16_00000 :
    nodeClaimChunkValidB branchClaims_5_16 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 16), starting at 64. -/
theorem coverageBranchNodes_5_16_00064 :
    nodeClaimChunkValidB branchClaims_5_16 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
