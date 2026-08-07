/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 7). -/
theorem coverageBranchRoot_3_07 :
    branchClaimRootValidB 3 7 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 27). -/
theorem coverageBranchRoot_5_27 :
    branchClaimRootValidB 5 27 (.search branchClaims_5_27) = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 128. -/
theorem coverageBranchNodes_5_26_00128 :
    nodeClaimChunkValidB branchClaims_5_26 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 192. -/
theorem coverageBranchNodes_5_26_00192 :
    nodeClaimChunkValidB branchClaims_5_26 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 256. -/
theorem coverageBranchNodes_5_26_00256 :
    nodeClaimChunkValidB branchClaims_5_26 256 7 = true := by
  rfl

/-- Node audit for fixed branch (5, 27), starting at 0. -/
theorem coverageBranchNodes_5_27_00000 :
    nodeClaimChunkValidB branchClaims_5_27 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
