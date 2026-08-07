/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 18). -/
theorem coverageBranchRoot_0_18 :
    branchClaimRootValidB 0 18 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 32). -/
theorem coverageBranchRoot_4_32 :
    branchClaimRootValidB 4 32 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 14). -/
theorem coverageBranchRoot_2_14 :
    branchClaimRootValidB 2 14 (.search branchClaims_2_14) = true := by
  rfl

/-- Root audit for fixed branch (2, 15). -/
theorem coverageBranchRoot_2_15 :
    branchClaimRootValidB 2 15 (.search branchClaims_2_15) = true := by
  rfl

/-- Node audit for fixed branch (2, 14), starting at 0. -/
theorem coverageBranchNodes_2_14_00000 :
    nodeClaimChunkValidB branchClaims_2_14 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 14), starting at 64. -/
theorem coverageBranchNodes_2_14_00064 :
    nodeClaimChunkValidB branchClaims_2_14 64 56 = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 0. -/
theorem coverageBranchNodes_2_15_00000 :
    nodeClaimChunkValidB branchClaims_2_15 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 64. -/
theorem coverageBranchNodes_2_15_00064 :
    nodeClaimChunkValidB branchClaims_2_15 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
