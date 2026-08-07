/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 22). -/
theorem coverageBranchRoot_3_22 :
    branchClaimRootValidB 3 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (6, 6). -/
theorem coverageBranchRoot_6_06 :
    branchClaimRootValidB 6 6 (.search branchClaims_6_6) = true := by
  rfl

/-- Root audit for fixed branch (6, 7). -/
theorem coverageBranchRoot_6_07 :
    branchClaimRootValidB 6 7 (.search branchClaims_6_7) = true := by
  rfl

/-- Root audit for fixed branch (6, 8). -/
theorem coverageBranchRoot_6_08 :
    branchClaimRootValidB 6 8 (.search branchClaims_6_8) = true := by
  rfl

/-- Node audit for fixed branch (6, 6), starting at 0. -/
theorem coverageBranchNodes_6_06_00000 :
    nodeClaimChunkValidB branchClaims_6_6 0 35 = true := by
  rfl

/-- Node audit for fixed branch (6, 7), starting at 0. -/
theorem coverageBranchNodes_6_07_00000 :
    nodeClaimChunkValidB branchClaims_6_7 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 7), starting at 64. -/
theorem coverageBranchNodes_6_07_00064 :
    nodeClaimChunkValidB branchClaims_6_7 64 39 = true := by
  rfl

/-- Node audit for fixed branch (6, 8), starting at 0. -/
theorem coverageBranchNodes_6_08_00000 :
    nodeClaimChunkValidB branchClaims_6_8 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
