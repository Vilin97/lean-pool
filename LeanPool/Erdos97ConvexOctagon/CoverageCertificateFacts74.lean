/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 33). -/
theorem coverageBranchRoot_3_33 :
    branchClaimRootValidB 3 33 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 11). -/
theorem coverageBranchRoot_6_11 :
    branchClaimRootValidB 6 11 (.search branchClaims_6_11) = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 64. -/
theorem coverageBranchNodes_6_10_00064 :
    nodeClaimChunkValidB branchClaims_6_10 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 10), starting at 128. -/
theorem coverageBranchNodes_6_10_00128 :
    nodeClaimChunkValidB branchClaims_6_10 128 30 = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 0. -/
theorem coverageBranchNodes_6_11_00000 :
    nodeClaimChunkValidB branchClaims_6_11 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 64. -/
theorem coverageBranchNodes_6_11_00064 :
    nodeClaimChunkValidB branchClaims_6_11 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
