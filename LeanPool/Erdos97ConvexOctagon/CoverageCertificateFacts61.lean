/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 8). -/
theorem coverageBranchRoot_3_08 :
    branchClaimRootValidB 3 8 (.patternThree 4) = true := by
  rfl

/-- Root audit for fixed branch (5, 26). -/
theorem coverageBranchRoot_5_26 :
    branchClaimRootValidB 5 26 (.search branchClaims_5_26) = true := by
  rfl

/-- Node audit for fixed branch (5, 25), starting at 223. -/
theorem coverageBranchNodes_5_25_00223 :
    nodeClaimChunkValidB branchClaims_5_25 223 31 = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 0. -/
theorem coverageBranchNodes_5_26_00000 :
    nodeClaimChunkValidB branchClaims_5_26 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 64. -/
theorem coverageBranchNodes_5_26_00064 :
    nodeClaimChunkValidB branchClaims_5_26 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 26), starting at 128. -/
theorem coverageBranchNodes_5_26_00128 :
    nodeClaimChunkValidB branchClaims_5_26 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
