/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 14). -/
theorem coverageBranchRoot_1_14 :
    branchClaimRootValidB 1 14 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (3, 31). -/
theorem coverageBranchRoot_3_31 :
    branchClaimRootValidB 3 31 (.search branchClaims_3_31) = true := by
  rfl

/-- Node audit for fixed branch (3, 30), starting at 64. -/
theorem coverageBranchNodes_3_30_00064 :
    nodeClaimChunkValidB branchClaims_3_30 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 30), starting at 128. -/
theorem coverageBranchNodes_3_30_00128 :
    nodeClaimChunkValidB branchClaims_3_30 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 30), starting at 192. -/
theorem coverageBranchNodes_3_30_00192 :
    nodeClaimChunkValidB branchClaims_3_30 192 31 = true := by
  rfl

/-- Node audit for fixed branch (3, 31), starting at 0. -/
theorem coverageBranchNodes_3_31_00000 :
    nodeClaimChunkValidB branchClaims_3_31 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
