/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 0). -/
theorem coverageBranchRoot_1_00 :
    branchClaimRootValidB 1 0 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (6, 21). -/
theorem coverageBranchRoot_6_21 :
    branchClaimRootValidB 6 21 (.patternThree 1) = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 128. -/
theorem coverageBranchNodes_3_24_00128 :
    nodeClaimChunkValidB branchClaims_3_24 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 192. -/
theorem coverageBranchNodes_3_24_00192 :
    nodeClaimChunkValidB branchClaims_3_24 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 256. -/
theorem coverageBranchNodes_3_24_00256 :
    nodeClaimChunkValidB branchClaims_3_24 256 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 320. -/
theorem coverageBranchNodes_3_24_00320 :
    nodeClaimChunkValidB branchClaims_3_24 320 29 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
