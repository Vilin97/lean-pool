/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 16). -/
theorem coverageBranchRoot_0_16 :
    branchClaimRootValidB 0 16 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 30). -/
theorem coverageBranchRoot_4_30 :
    branchClaimRootValidB 4 30 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 9). -/
theorem coverageBranchRoot_2_09 :
    branchClaimRootValidB 2 9 (.search branchClaims_2_9) = true := by
  rfl

/-- Node audit for fixed branch (2, 8), starting at 64. -/
theorem coverageBranchNodes_2_08_00064 :
    nodeClaimChunkValidB branchClaims_2_8 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 8), starting at 128. -/
theorem coverageBranchNodes_2_08_00128 :
    nodeClaimChunkValidB branchClaims_2_8 128 36 = true := by
  rfl

/-- Node audit for fixed branch (2, 9), starting at 0. -/
theorem coverageBranchNodes_2_09_00000 :
    nodeClaimChunkValidB branchClaims_2_9 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 9), starting at 64. -/
theorem coverageBranchNodes_2_09_00064 :
    nodeClaimChunkValidB branchClaims_2_9 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
