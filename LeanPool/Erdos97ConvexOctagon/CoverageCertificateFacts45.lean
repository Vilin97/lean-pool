/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 20). -/
theorem coverageBranchRoot_1_20 :
    branchClaimRootValidB 1 20 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 4). -/
theorem coverageBranchRoot_5_04 :
    branchClaimRootValidB 5 4 (.search branchClaims_5_4) = true := by
  rfl

/-- Root audit for fixed branch (5, 5). -/
theorem coverageBranchRoot_5_05 :
    branchClaimRootValidB 5 5 (.search branchClaims_5_5) = true := by
  rfl

/-- Node audit for fixed branch (5, 4), starting at 0. -/
theorem coverageBranchNodes_5_04_00000 :
    nodeClaimChunkValidB branchClaims_5_4 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 4), starting at 64. -/
theorem coverageBranchNodes_5_04_00064 :
    nodeClaimChunkValidB branchClaims_5_4 64 50 = true := by
  rfl

/-- Node audit for fixed branch (5, 5), starting at 0. -/
theorem coverageBranchNodes_5_05_00000 :
    nodeClaimChunkValidB branchClaims_5_5 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 5), starting at 64. -/
theorem coverageBranchNodes_5_05_00064 :
    nodeClaimChunkValidB branchClaims_5_5 64 30 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
