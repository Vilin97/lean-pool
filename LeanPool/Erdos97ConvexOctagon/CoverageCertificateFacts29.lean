/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 29). -/
theorem coverageBranchRoot_0_29 :
    branchClaimRootValidB 0 29 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 19). -/
theorem coverageBranchRoot_6_19 :
    branchClaimRootValidB 6 19 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 1). -/
theorem coverageBranchRoot_3_01 :
    branchClaimRootValidB 3 1 (.search branchClaims_3_1) = true := by
  rfl

/-- Root audit for fixed branch (3, 2). -/
theorem coverageBranchRoot_3_02 :
    branchClaimRootValidB 3 2 (.search branchClaims_3_2) = true := by
  rfl

/-- Node audit for fixed branch (2, 34), starting at 128. -/
theorem coverageBranchNodes_2_34_00128 :
    nodeClaimChunkValidB branchClaims_2_34 128 34 = true := by
  rfl

/-- Node audit for fixed branch (3, 1), starting at 0. -/
theorem coverageBranchNodes_3_01_00000 :
    nodeClaimChunkValidB branchClaims_3_1 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 1), starting at 64. -/
theorem coverageBranchNodes_3_01_00064 :
    nodeClaimChunkValidB branchClaims_3_1 64 47 = true := by
  rfl

/-- Node audit for fixed branch (3, 2), starting at 0. -/
theorem coverageBranchNodes_3_02_00000 :
    nodeClaimChunkValidB branchClaims_3_2 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
