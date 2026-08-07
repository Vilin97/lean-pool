/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 7). -/
theorem coverageBranchRoot_2_07 :
    branchClaimRootValidB 2 7 (.patternThree 2) = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 64. -/
theorem coverageBranchNodes_5_14_00064 :
    nodeClaimChunkValidB branchClaims_5_14 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 128. -/
theorem coverageBranchNodes_5_14_00128 :
    nodeClaimChunkValidB branchClaims_5_14 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 192. -/
theorem coverageBranchNodes_5_14_00192 :
    nodeClaimChunkValidB branchClaims_5_14 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 14), starting at 256. -/
theorem coverageBranchNodes_5_14_00256 :
    nodeClaimChunkValidB branchClaims_5_14 256 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
