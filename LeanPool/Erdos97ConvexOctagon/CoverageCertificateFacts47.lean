/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 22). -/
theorem coverageBranchRoot_1_22 :
    branchClaimRootValidB 1 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 8). -/
theorem coverageBranchRoot_5_08 :
    branchClaimRootValidB 5 8 (.search branchClaims_5_8) = true := by
  rfl

/-- Root audit for fixed branch (5, 9). -/
theorem coverageBranchRoot_5_09 :
    branchClaimRootValidB 5 9 (.search branchClaims_5_9) = true := by
  rfl

/-- Node audit for fixed branch (5, 8), starting at 0. -/
theorem coverageBranchNodes_5_08_00000 :
    nodeClaimChunkValidB branchClaims_5_8 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 8), starting at 64. -/
theorem coverageBranchNodes_5_08_00064 :
    nodeClaimChunkValidB branchClaims_5_8 64 25 = true := by
  rfl

/-- Node audit for fixed branch (5, 9), starting at 0. -/
theorem coverageBranchNodes_5_09_00000 :
    nodeClaimChunkValidB branchClaims_5_9 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 9), starting at 64. -/
theorem coverageBranchNodes_5_09_00064 :
    nodeClaimChunkValidB branchClaims_5_9 64 22 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
