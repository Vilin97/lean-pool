/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData20

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 9). -/
theorem coverageBranchRoot_4_09 :
    branchClaimRootValidB 4 9 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 28). -/
theorem coverageBranchRoot_6_28 :
    branchClaimRootValidB 6 28 (.search branchClaims_6_28) = true := by
  rfl

/-- Node audit for fixed branch (6, 27), starting at 128. -/
theorem coverageBranchNodes_6_27_00128 :
    nodeClaimChunkValidB branchClaims_6_27 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 27), starting at 192. -/
theorem coverageBranchNodes_6_27_00192 :
    nodeClaimChunkValidB branchClaims_6_27 192 32 = true := by
  rfl

/-- Node audit for fixed branch (6, 28), starting at 0. -/
theorem coverageBranchNodes_6_28_00000 :
    nodeClaimChunkValidB branchClaims_6_28 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 28), starting at 64. -/
theorem coverageBranchNodes_6_28_00064 :
    nodeClaimChunkValidB branchClaims_6_28 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
