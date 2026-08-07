/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData19

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 6). -/
theorem coverageBranchRoot_4_06 :
    branchClaimRootValidB 4 6 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 25). -/
theorem coverageBranchRoot_6_25 :
    branchClaimRootValidB 6 25 (.search branchClaims_6_25) = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 128. -/
theorem coverageBranchNodes_6_24_00128 :
    nodeClaimChunkValidB branchClaims_6_24 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 24), starting at 192. -/
theorem coverageBranchNodes_6_24_00192 :
    nodeClaimChunkValidB branchClaims_6_24 192 43 = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 0. -/
theorem coverageBranchNodes_6_25_00000 :
    nodeClaimChunkValidB branchClaims_6_25 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 25), starting at 64. -/
theorem coverageBranchNodes_6_25_00064 :
    nodeClaimChunkValidB branchClaims_6_25 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
