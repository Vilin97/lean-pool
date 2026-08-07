/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 2). -/
theorem coverageBranchRoot_1_02 :
    branchClaimRootValidB 1 2 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (6, 29). -/
theorem coverageBranchRoot_6_29 :
    branchClaimRootValidB 6 29 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 26). -/
theorem coverageBranchRoot_3_26 :
    branchClaimRootValidB 3 26 (.search branchClaims_3_26) = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 256. -/
theorem coverageBranchNodes_3_25_00256 :
    nodeClaimChunkValidB branchClaims_3_25 256 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 320. -/
theorem coverageBranchNodes_3_25_00320 :
    nodeClaimChunkValidB branchClaims_3_25 320 21 = true := by
  rfl

/-- Node audit for fixed branch (3, 26), starting at 0. -/
theorem coverageBranchNodes_3_26_00000 :
    nodeClaimChunkValidB branchClaims_3_26 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 26), starting at 64. -/
theorem coverageBranchNodes_3_26_00064 :
    nodeClaimChunkValidB branchClaims_3_26 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
