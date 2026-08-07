/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 14). -/
theorem coverageBranchRoot_0_14 :
    branchClaimRootValidB 0 14 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 28). -/
theorem coverageBranchRoot_4_28 :
    branchClaimRootValidB 4 28 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 4). -/
theorem coverageBranchRoot_2_04 :
    branchClaimRootValidB 2 4 (.search branchClaims_2_4) = true := by
  rfl

/-- Root audit for fixed branch (2, 5). -/
theorem coverageBranchRoot_2_05 :
    branchClaimRootValidB 2 5 (.search branchClaims_2_5) = true := by
  rfl

/-- Node audit for fixed branch (2, 3), starting at 64. -/
theorem coverageBranchNodes_2_03_00064 :
    nodeClaimChunkValidB branchClaims_2_3 64 48 = true := by
  rfl

/-- Node audit for fixed branch (2, 4), starting at 0. -/
theorem coverageBranchNodes_2_04_00000 :
    nodeClaimChunkValidB branchClaims_2_4 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 4), starting at 64. -/
theorem coverageBranchNodes_2_04_00064 :
    nodeClaimChunkValidB branchClaims_2_4 64 50 = true := by
  rfl

/-- Node audit for fixed branch (2, 5), starting at 0. -/
theorem coverageBranchNodes_2_05_00000 :
    nodeClaimChunkValidB branchClaims_2_5 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
