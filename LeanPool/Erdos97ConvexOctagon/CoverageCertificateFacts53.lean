/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 13). -/
theorem coverageBranchRoot_2_13 :
    branchClaimRootValidB 2 13 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 15). -/
theorem coverageBranchRoot_5_15 :
    branchClaimRootValidB 5 15 (.search branchClaims_5_15) = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 320. -/
theorem coverageBranchNodes_5_14_00320 :
    nodeClaimChunkValidB branchClaims_5_14 320 44 = true := by
  rfl

/-- Node audit for fixed branch (5, 15), starting at 0. -/
theorem coverageBranchNodes_5_15_00000 :
    nodeClaimChunkValidB branchClaims_5_15 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 15), starting at 64. -/
theorem coverageBranchNodes_5_15_00064 :
    nodeClaimChunkValidB branchClaims_5_15 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 15), starting at 128. -/
theorem coverageBranchNodes_5_15_00128 :
    nodeClaimChunkValidB branchClaims_5_15 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
