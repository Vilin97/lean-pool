/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 24). -/
theorem coverageBranchRoot_0_24 :
    branchClaimRootValidB 0 24 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 22). -/
theorem coverageBranchRoot_5_22 :
    branchClaimRootValidB 5 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (2, 29). -/
theorem coverageBranchRoot_2_29 :
    branchClaimRootValidB 2 29 (.search branchClaims2Row29) = true := by
  rfl

/-- Root audit for fixed branch (2, 30). -/
theorem coverageBranchRoot_2_30 :
    branchClaimRootValidB 2 30 (.search branchClaims2Row30) = true := by
  rfl

/-- Node audit for fixed branch (2, 28), starting at 64. -/
theorem coverageBranchNodes_2_28_00064 :
    nodeClaimChunkValidB branchClaims2Row28 64 32 = true := by
  rfl

/-- Node audit for fixed branch (2, 29), starting at 0. -/
theorem coverageBranchNodes_2_29_00000 :
    nodeClaimChunkValidB branchClaims2Row29 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 29), starting at 64. -/
theorem coverageBranchNodes_2_29_00064 :
    nodeClaimChunkValidB branchClaims2Row29 64 39 = true := by
  rfl

/-- Node audit for fixed branch (2, 30), starting at 0. -/
theorem coverageBranchNodes_2_30_00000 :
    nodeClaimChunkValidB branchClaims2Row30 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
