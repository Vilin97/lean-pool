/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 28). -/
theorem coverageBranchRoot_0_28 :
    branchClaimRootValidB 0 28 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 0). -/
theorem coverageBranchRoot_6_00 :
    branchClaimRootValidB 6 0 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (2, 34). -/
theorem coverageBranchRoot_2_34 :
    branchClaimRootValidB 2 34 (.search branchClaims_2_34) = true := by
  rfl

/-- Node audit for fixed branch (2, 33), starting at 64. -/
theorem coverageBranchNodes_2_33_00064 :
    nodeClaimChunkValidB branchClaims_2_33 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 33), starting at 128. -/
theorem coverageBranchNodes_2_33_00128 :
    nodeClaimChunkValidB branchClaims_2_33 128 38 = true := by
  rfl

/-- Node audit for fixed branch (2, 34), starting at 0. -/
theorem coverageBranchNodes_2_34_00000 :
    nodeClaimChunkValidB branchClaims_2_34 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 34), starting at 64. -/
theorem coverageBranchNodes_2_34_00064 :
    nodeClaimChunkValidB branchClaims_2_34 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
