/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 6). -/
theorem coverageBranchRoot_4_06 :
    branchClaimRootValidB 4 6 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 17). -/
theorem coverageBranchRoot_6_17 :
    branchClaimRootValidB 6 17 (.search branchClaims_6_17) = true := by
  rfl

/-- Node audit for fixed branch (6, 16), starting at 64. -/
theorem coverageBranchNodes_6_16_00064 :
    nodeClaimChunkValidB branchClaims_6_16 64 54 = true := by
  rfl

/-- Node audit for fixed branch (6, 17), starting at 0. -/
theorem coverageBranchNodes_6_17_00000 :
    nodeClaimChunkValidB branchClaims_6_17 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 17), starting at 64. -/
theorem coverageBranchNodes_6_17_00064 :
    nodeClaimChunkValidB branchClaims_6_17 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 17), starting at 128. -/
theorem coverageBranchNodes_6_17_00128 :
    nodeClaimChunkValidB branchClaims_6_17 128 43 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
