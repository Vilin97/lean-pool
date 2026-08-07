/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 11). -/
theorem coverageBranchRoot_1_11 :
    branchClaimRootValidB 1 11 (.patternThree 178) = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 64. -/
theorem coverageBranchNodes_3_27_00064 :
    nodeClaimChunkValidB branchClaims_3_27 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 128. -/
theorem coverageBranchNodes_3_27_00128 :
    nodeClaimChunkValidB branchClaims_3_27 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 192. -/
theorem coverageBranchNodes_3_27_00192 :
    nodeClaimChunkValidB branchClaims_3_27 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 256. -/
theorem coverageBranchNodes_3_27_00256 :
    nodeClaimChunkValidB branchClaims_3_27 256 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
