/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 27). -/
theorem coverageBranchRoot_0_27 :
    branchClaimRootValidB 0 27 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 33). -/
theorem coverageBranchRoot_5_33 :
    branchClaimRootValidB 5 33 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (2, 33). -/
theorem coverageBranchRoot_2_33 :
    branchClaimRootValidB 2 33 (.search branchClaims_2_33) = true := by
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

/-- Node audit for fixed branch (2, 33), starting at 0. -/
theorem coverageBranchNodes_2_33_00000 :
    nodeClaimChunkValidB branchClaims_2_33 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
