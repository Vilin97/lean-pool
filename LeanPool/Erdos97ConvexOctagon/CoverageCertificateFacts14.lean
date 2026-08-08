/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 14). -/
theorem coverageBranchRoot_0_14 :
    branchClaimRootValidB 0 14 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 32). -/
theorem coverageBranchRoot_4_32 :
    branchClaimRootValidB 4 32 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 3). -/
theorem coverageBranchRoot_2_03 :
    branchClaimRootValidB 2 3 (.search branchClaims2Row3) = true := by
  rfl

/-- Root audit for fixed branch (2, 4). -/
theorem coverageBranchRoot_2_04 :
    branchClaimRootValidB 2 4 (.search branchClaims2Row4) = true := by
  rfl

/-- Node audit for fixed branch (2, 2), starting at 64. -/
theorem coverageBranchNodes_2_02_00064 :
    nodeClaimChunkValidB branchClaims2Row2 64 51 = true := by
  rfl

/-- Node audit for fixed branch (2, 3), starting at 0. -/
theorem coverageBranchNodes_2_03_00000 :
    nodeClaimChunkValidB branchClaims2Row3 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 3), starting at 64. -/
theorem coverageBranchNodes_2_03_00064 :
    nodeClaimChunkValidB branchClaims2Row3 64 48 = true := by
  rfl

/-- Node audit for fixed branch (2, 4), starting at 0. -/
theorem coverageBranchNodes_2_04_00000 :
    nodeClaimChunkValidB branchClaims2Row4 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
