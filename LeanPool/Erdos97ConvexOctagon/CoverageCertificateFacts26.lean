/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 26). -/
theorem coverageBranchRoot_0_26 :
    branchClaimRootValidB 0 26 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 30). -/
theorem coverageBranchRoot_5_30 :
    branchClaimRootValidB 5 30 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (2, 32). -/
theorem coverageBranchRoot_2_32 :
    branchClaimRootValidB 2 32 (.search branchClaims2Row32) = true := by
  rfl

/-- Node audit for fixed branch (2, 31), starting at 64. -/
theorem coverageBranchNodes_2_31_00064 :
    nodeClaimChunkValidB branchClaims2Row31 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 31), starting at 128. -/
theorem coverageBranchNodes_2_31_00128 :
    nodeClaimChunkValidB branchClaims2Row31 128 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 31), starting at 192. -/
theorem coverageBranchNodes_2_31_00192 :
    nodeClaimChunkValidB branchClaims2Row31 192 31 = true := by
  rfl

/-- Node audit for fixed branch (2, 32), starting at 0. -/
theorem coverageBranchNodes_2_32_00000 :
    nodeClaimChunkValidB branchClaims2Row32 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
