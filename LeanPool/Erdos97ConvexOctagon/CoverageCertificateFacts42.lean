/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 13). -/
theorem coverageBranchRoot_1_13 :
    branchClaimRootValidB 1 13 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (3, 30). -/
theorem coverageBranchRoot_3_30 :
    branchClaimRootValidB 3 30 (.search branchClaims_3_30) = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 192. -/
theorem coverageBranchNodes_3_28_00192 :
    nodeClaimChunkValidB branchClaims_3_28 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 256. -/
theorem coverageBranchNodes_3_28_00256 :
    nodeClaimChunkValidB branchClaims_3_28 256 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 28), starting at 320. -/
theorem coverageBranchNodes_3_28_00320 :
    nodeClaimChunkValidB branchClaims_3_28 320 21 = true := by
  rfl

/-- Node audit for fixed branch (3, 30), starting at 0. -/
theorem coverageBranchNodes_3_30_00000 :
    nodeClaimChunkValidB branchClaims_3_30 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
