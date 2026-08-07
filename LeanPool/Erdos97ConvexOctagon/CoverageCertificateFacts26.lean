/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 26). -/
theorem coverageBranchRoot_0_26 :
    branchClaimRootValidB 0 26 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 20). -/
theorem coverageBranchRoot_5_20 :
    branchClaimRootValidB 5 20 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (2, 32). -/
theorem coverageBranchRoot_2_32 :
    branchClaimRootValidB 2 32 (.search branchClaims_2_32) = true := by
  rfl

/-- Node audit for fixed branch (2, 32), starting at 0. -/
theorem coverageBranchNodes_2_32_00000 :
    nodeClaimChunkValidB branchClaims_2_32 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 32), starting at 64. -/
theorem coverageBranchNodes_2_32_00064 :
    nodeClaimChunkValidB branchClaims_2_32 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 32), starting at 128. -/
theorem coverageBranchNodes_2_32_00128 :
    nodeClaimChunkValidB branchClaims_2_32 128 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 32), starting at 192. -/
theorem coverageBranchNodes_2_32_00192 :
    nodeClaimChunkValidB branchClaims_2_32 192 27 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
