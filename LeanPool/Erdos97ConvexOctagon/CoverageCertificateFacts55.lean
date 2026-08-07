/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 19). -/
theorem coverageBranchRoot_2_19 :
    branchClaimRootValidB 2 19 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 18). -/
theorem coverageBranchRoot_5_18 :
    branchClaimRootValidB 5 18 (.search branchClaims_5_18) = true := by
  rfl

/-- Node audit for fixed branch (5, 17), starting at 192. -/
theorem coverageBranchNodes_5_17_00192 :
    nodeClaimChunkValidB branchClaims_5_17 192 28 = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 0. -/
theorem coverageBranchNodes_5_18_00000 :
    nodeClaimChunkValidB branchClaims_5_18 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 64. -/
theorem coverageBranchNodes_5_18_00064 :
    nodeClaimChunkValidB branchClaims_5_18 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 128. -/
theorem coverageBranchNodes_5_18_00128 :
    nodeClaimChunkValidB branchClaims_5_18 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
