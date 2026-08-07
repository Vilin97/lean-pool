/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 17). -/
theorem coverageBranchRoot_0_17 :
    branchClaimRootValidB 0 17 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 31). -/
theorem coverageBranchRoot_4_31 :
    branchClaimRootValidB 4 31 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 10). -/
theorem coverageBranchRoot_2_10 :
    branchClaimRootValidB 2 10 (.search branchClaims_2_10) = true := by
  rfl

/-- Root audit for fixed branch (2, 11). -/
theorem coverageBranchRoot_2_11 :
    branchClaimRootValidB 2 11 (.search branchClaims_2_11) = true := by
  rfl

/-- Root audit for fixed branch (2, 12). -/
theorem coverageBranchRoot_2_12 :
    branchClaimRootValidB 2 12 (.search branchClaims_2_12) = true := by
  rfl

/-- Node audit for fixed branch (2, 9), starting at 128. -/
theorem coverageBranchNodes_2_09_00128 :
    nodeClaimChunkValidB branchClaims_2_9 128 54 = true := by
  rfl

/-- Node audit for fixed branch (2, 10), starting at 0. -/
theorem coverageBranchNodes_2_10_00000 :
    nodeClaimChunkValidB branchClaims_2_10 0 15 = true := by
  rfl

/-- Node audit for fixed branch (2, 11), starting at 0. -/
theorem coverageBranchNodes_2_11_00000 :
    nodeClaimChunkValidB branchClaims_2_11 0 15 = true := by
  rfl

/-- Node audit for fixed branch (2, 12), starting at 0. -/
theorem coverageBranchNodes_2_12_00000 :
    nodeClaimChunkValidB branchClaims_2_12 0 28 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
