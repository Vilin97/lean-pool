/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData20

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 11). -/
theorem coverageBranchRoot_4_11 :
    branchClaimRootValidB 4 11 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 31). -/
theorem coverageBranchRoot_6_31 :
    branchClaimRootValidB 6 31 (.search branchClaims_6_31) = true := by
  rfl

/-- Node audit for fixed branch (6, 30), starting at 128. -/
theorem coverageBranchNodes_6_30_00128 :
    nodeClaimChunkValidB branchClaims_6_30 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 30), starting at 192. -/
theorem coverageBranchNodes_6_30_00192 :
    nodeClaimChunkValidB branchClaims_6_30 192 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 30), starting at 256. -/
theorem coverageBranchNodes_6_30_00256 :
    nodeClaimChunkValidB branchClaims_6_30 256 9 = true := by
  rfl

/-- Node audit for fixed branch (6, 31), starting at 0. -/
theorem coverageBranchNodes_6_31_00000 :
    nodeClaimChunkValidB branchClaims_6_31 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
