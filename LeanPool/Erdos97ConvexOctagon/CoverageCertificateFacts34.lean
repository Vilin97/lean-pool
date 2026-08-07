/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 34). -/
theorem coverageBranchRoot_0_34 :
    branchClaimRootValidB 0 34 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 33). -/
theorem coverageBranchRoot_6_33 :
    branchClaimRootValidB 6 33 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 23). -/
theorem coverageBranchRoot_3_23 :
    branchClaimRootValidB 3 23 (.search branchClaims_3_23) = true := by
  rfl

/-- Node audit for fixed branch (3, 23), starting at 0. -/
theorem coverageBranchNodes_3_23_00000 :
    nodeClaimChunkValidB branchClaims_3_23 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 23), starting at 64. -/
theorem coverageBranchNodes_3_23_00064 :
    nodeClaimChunkValidB branchClaims_3_23 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 23), starting at 128. -/
theorem coverageBranchNodes_3_23_00128 :
    nodeClaimChunkValidB branchClaims_3_23 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 23), starting at 192. -/
theorem coverageBranchNodes_3_23_00192 :
    nodeClaimChunkValidB branchClaims_3_23 192 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
