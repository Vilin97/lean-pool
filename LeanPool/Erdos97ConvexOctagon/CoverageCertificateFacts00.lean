/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 0). -/
theorem coverageBranchRoot_0_00 :
    branchClaimRootValidB 0 0 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 18). -/
theorem coverageBranchRoot_4_18 :
    branchClaimRootValidB 4 18 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 4). -/
theorem coverageBranchRoot_1_04 :
    branchClaimRootValidB 1 4 (.search branchClaims_1_4) = true := by
  rfl

/-- Root audit for fixed branch (1, 5). -/
theorem coverageBranchRoot_1_05 :
    branchClaimRootValidB 1 5 (.search branchClaims_1_5) = true := by
  rfl

/-- Node audit for fixed branch (1, 4), starting at 0. -/
theorem coverageBranchNodes_1_04_00000 :
    nodeClaimChunkValidB branchClaims_1_4 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 4), starting at 64. -/
theorem coverageBranchNodes_1_04_00064 :
    nodeClaimChunkValidB branchClaims_1_4 64 38 = true := by
  rfl

/-- Node audit for fixed branch (1, 5), starting at 0. -/
theorem coverageBranchNodes_1_05_00000 :
    nodeClaimChunkValidB branchClaims_1_5 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 5), starting at 64. -/
theorem coverageBranchNodes_1_05_00064 :
    nodeClaimChunkValidB branchClaims_1_5 64 37 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
