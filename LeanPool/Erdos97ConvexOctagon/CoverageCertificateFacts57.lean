/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 21). -/
theorem coverageBranchRoot_2_21 :
    branchClaimRootValidB 2 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 24). -/
theorem coverageBranchRoot_5_24 :
    branchClaimRootValidB 5 24 (.search branchClaims_5_24) = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 192. -/
theorem coverageBranchNodes_5_19_00192 :
    nodeClaimChunkValidB branchClaims_5_19 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 256. -/
theorem coverageBranchNodes_5_19_00256 :
    nodeClaimChunkValidB branchClaims_5_19 256 42 = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 0. -/
theorem coverageBranchNodes_5_24_00000 :
    nodeClaimChunkValidB branchClaims_5_24 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 64. -/
theorem coverageBranchNodes_5_24_00064 :
    nodeClaimChunkValidB branchClaims_5_24 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
