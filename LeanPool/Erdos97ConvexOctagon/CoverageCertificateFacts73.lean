/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 29). -/
theorem coverageBranchRoot_3_29 :
    branchClaimRootValidB 3 29 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 1). -/
theorem coverageBranchRoot_6_01 :
    branchClaimRootValidB 6 1 (.search branchClaims_6_1) = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 320. -/
theorem coverageBranchNodes_5_34_00320 :
    nodeClaimChunkValidB branchClaims_5_34 320 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 384. -/
theorem coverageBranchNodes_5_34_00384 :
    nodeClaimChunkValidB branchClaims_5_34 384 6 = true := by
  rfl

/-- Node audit for fixed branch (6, 1), starting at 0. -/
theorem coverageBranchNodes_6_01_00000 :
    nodeClaimChunkValidB branchClaims_6_1 0 32 = true := by
  rfl

/-- Node audit for fixed branch (6, 1), starting at 32. -/
theorem coverageBranchNodes_6_01_00032 :
    nodeClaimChunkValidB branchClaims_6_1 32 32 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
