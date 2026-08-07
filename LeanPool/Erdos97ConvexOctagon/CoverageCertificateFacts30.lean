/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 30). -/
theorem coverageBranchRoot_0_30 :
    branchClaimRootValidB 0 30 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 30). -/
theorem coverageBranchRoot_5_30 :
    branchClaimRootValidB 5 30 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (3, 4). -/
theorem coverageBranchRoot_3_04 :
    branchClaimRootValidB 3 4 (.search branchClaims_3_4) = true := by
  rfl

/-- Root audit for fixed branch (3, 5). -/
theorem coverageBranchRoot_3_05 :
    branchClaimRootValidB 3 5 (.search branchClaims_3_5) = true := by
  rfl

/-- Node audit for fixed branch (3, 4), starting at 0. -/
theorem coverageBranchNodes_3_04_00000 :
    nodeClaimChunkValidB branchClaims_3_4 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 4), starting at 64. -/
theorem coverageBranchNodes_3_04_00064 :
    nodeClaimChunkValidB branchClaims_3_4 64 50 = true := by
  rfl

/-- Node audit for fixed branch (3, 5), starting at 0. -/
theorem coverageBranchNodes_3_05_00000 :
    nodeClaimChunkValidB branchClaims_3_5 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 5), starting at 64. -/
theorem coverageBranchNodes_3_05_00064 :
    nodeClaimChunkValidB branchClaims_3_5 64 52 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
