/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 15). -/
theorem coverageBranchRoot_4_15 :
    branchClaimRootValidB 4 15 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 31). -/
theorem coverageBranchRoot_6_31 :
    branchClaimRootValidB 6 31 (.search branchClaims_6_31) = true := by
  rfl

/-- Node audit for fixed branch (6, 30), starting at 256. -/
theorem coverageBranchNodes_6_30_00256 :
    nodeClaimChunkValidB branchClaims_6_30 256 9 = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 0. -/
theorem coverageBranchNodes_6_31_00000 :
    nodeClaimChunkValidB branchClaims_6_31 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 64. -/
theorem coverageBranchNodes_6_31_00064 :
    nodeClaimChunkValidB branchClaims_6_31 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 128. -/
theorem coverageBranchNodes_6_31_00128 :
    nodeClaimChunkValidB branchClaims_6_31 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
