/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 17). -/
theorem coverageBranchRoot_4_17 :
    branchClaimRootValidB 4 17 (.patternTwo 0) = true := by
  rfl

/-- Node audit for fixed branch (6, 32), starting at 128. -/
theorem coverageBranchNodes_6_32_00128 :
    nodeClaimChunkValidB branchClaims_6_32 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 32), starting at 192. -/
theorem coverageBranchNodes_6_32_00192 :
    nodeClaimChunkValidB branchClaims_6_32 192 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 32), starting at 256. -/
theorem coverageBranchNodes_6_32_00256 :
    nodeClaimChunkValidB branchClaims_6_32 256 1 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
