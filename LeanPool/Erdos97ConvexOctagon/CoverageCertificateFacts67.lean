/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 17). -/
theorem coverageBranchRoot_3_17 :
    branchClaimRootValidB 3 17 (.patternThree 4) = true := by
  rfl

/-- Root audit for fixed branch (5, 31). -/
theorem coverageBranchRoot_5_31 :
    branchClaimRootValidB 5 31 (.search branchClaims_5_31) = true := by
  rfl

/-- Node audit for fixed branch (5, 29), starting at 192. -/
theorem coverageBranchNodes_5_29_00192 :
    nodeClaimChunkValidB branchClaims_5_29 192 57 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 0. -/
theorem coverageBranchNodes_5_31_00000 :
    nodeClaimChunkValidB branchClaims_5_31 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 64. -/
theorem coverageBranchNodes_5_31_00064 :
    nodeClaimChunkValidB branchClaims_5_31 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 128. -/
theorem coverageBranchNodes_5_31_00128 :
    nodeClaimChunkValidB branchClaims_5_31 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
