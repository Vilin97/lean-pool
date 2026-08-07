/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 1). -/
theorem coverageBranchRoot_1_01 :
    branchClaimRootValidB 1 1 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (6, 22). -/
theorem coverageBranchRoot_6_22 :
    branchClaimRootValidB 6 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (3, 25). -/
theorem coverageBranchRoot_3_25 :
    branchClaimRootValidB 3 25 (.search branchClaims_3_25) = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 0. -/
theorem coverageBranchNodes_3_25_00000 :
    nodeClaimChunkValidB branchClaims_3_25 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 64. -/
theorem coverageBranchNodes_3_25_00064 :
    nodeClaimChunkValidB branchClaims_3_25 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 128. -/
theorem coverageBranchNodes_3_25_00128 :
    nodeClaimChunkValidB branchClaims_3_25 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 192. -/
theorem coverageBranchNodes_3_25_00192 :
    nodeClaimChunkValidB branchClaims_3_25 192 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
