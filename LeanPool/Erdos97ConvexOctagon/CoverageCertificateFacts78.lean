/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData18

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 2). -/
theorem coverageBranchRoot_4_02 :
    branchClaimRootValidB 4 2 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 16). -/
theorem coverageBranchRoot_6_16 :
    branchClaimRootValidB 6 16 (.search branchClaims_6_16) = true := by
  rfl

/-- Root audit for fixed branch (6, 17). -/
theorem coverageBranchRoot_6_17 :
    branchClaimRootValidB 6 17 (.search branchClaims_6_17) = true := by
  rfl

/-- Node audit for fixed branch (6, 15), starting at 192. -/
theorem coverageBranchNodes_6_15_00192 :
    nodeClaimChunkValidB branchClaims_6_15 192 9 = true := by
  rfl

/-- Node audit for fixed branch (6, 16), starting at 0. -/
theorem coverageBranchNodes_6_16_00000 :
    nodeClaimChunkValidB branchClaims_6_16 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 16), starting at 64. -/
theorem coverageBranchNodes_6_16_00064 :
    nodeClaimChunkValidB branchClaims_6_16 64 54 = true := by
  rfl

/-- Node audit for fixed branch (6, 17), starting at 0. -/
theorem coverageBranchNodes_6_17_00000 :
    nodeClaimChunkValidB branchClaims_6_17 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
