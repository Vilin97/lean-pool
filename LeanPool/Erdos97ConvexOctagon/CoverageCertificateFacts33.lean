/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 33). -/
theorem coverageBranchRoot_0_33 :
    branchClaimRootValidB 0 33 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 29). -/
theorem coverageBranchRoot_6_29 :
    branchClaimRootValidB 6 29 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 11). -/
theorem coverageBranchRoot_3_11 :
    branchClaimRootValidB 3 11 (.search branchClaims_3_11) = true := by
  rfl

/-- Root audit for fixed branch (3, 12). -/
theorem coverageBranchRoot_3_12 :
    branchClaimRootValidB 3 12 (.search branchClaims_3_12) = true := by
  rfl

/-- Node audit for fixed branch (3, 11), starting at 0. -/
theorem coverageBranchNodes_3_11_00000 :
    nodeClaimChunkValidB branchClaims_3_11 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 11), starting at 64. -/
theorem coverageBranchNodes_3_11_00064 :
    nodeClaimChunkValidB branchClaims_3_11 64 49 = true := by
  rfl

/-- Node audit for fixed branch (3, 12), starting at 0. -/
theorem coverageBranchNodes_3_12_00000 :
    nodeClaimChunkValidB branchClaims_3_12 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 12), starting at 64. -/
theorem coverageBranchNodes_3_12_00064 :
    nodeClaimChunkValidB branchClaims_3_12 64 43 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
