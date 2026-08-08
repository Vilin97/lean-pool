/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 9). -/
theorem coverageBranchRoot_0_09 :
    branchClaimRootValidB 0 9 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 27). -/
theorem coverageBranchRoot_4_27 :
    branchClaimRootValidB 4 27 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 31). -/
theorem coverageBranchRoot_1_31 :
    branchClaimRootValidB 1 31 (.search branchClaims1Row31) = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 192. -/
theorem coverageBranchNodes_1_30_00192 :
    nodeClaimChunkValidB branchClaims1Row30 192 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 30), starting at 256. -/
theorem coverageBranchNodes_1_30_00256 :
    nodeClaimChunkValidB branchClaims1Row30 256 19 = true := by
  rfl

/-- Node audit for fixed branch (1, 31), starting at 0. -/
theorem coverageBranchNodes_1_31_00000 :
    nodeClaimChunkValidB branchClaims1Row31 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 31), starting at 64. -/
theorem coverageBranchNodes_1_31_00064 :
    nodeClaimChunkValidB branchClaims1Row31 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
