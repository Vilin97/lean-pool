/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 11). -/
theorem coverageBranchRoot_0_11 :
    branchClaimRootValidB 0 11 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 29). -/
theorem coverageBranchRoot_4_29 :
    branchClaimRootValidB 4 29 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 33). -/
theorem coverageBranchRoot_1_33 :
    branchClaimRootValidB 1 33 (.search branchClaims1Row33) = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 64. -/
theorem coverageBranchNodes_1_32_00064 :
    nodeClaimChunkValidB branchClaims1Row32 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 128. -/
theorem coverageBranchNodes_1_32_00128 :
    nodeClaimChunkValidB branchClaims1Row32 128 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 32), starting at 192. -/
theorem coverageBranchNodes_1_32_00192 :
    nodeClaimChunkValidB branchClaims1Row32 192 54 = true := by
  rfl

/-- Node audit for fixed branch (1, 33), starting at 0. -/
theorem coverageBranchNodes_1_33_00000 :
    nodeClaimChunkValidB branchClaims1Row33 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
