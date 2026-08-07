/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData16

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 19). -/
theorem coverageBranchRoot_3_19 :
    branchClaimRootValidB 3 19 (.patternThree 2) = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 64. -/
theorem coverageBranchNodes_5_34_00064 :
    nodeClaimChunkValidB branchClaims_5_34 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 128. -/
theorem coverageBranchNodes_5_34_00128 :
    nodeClaimChunkValidB branchClaims_5_34 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 192. -/
theorem coverageBranchNodes_5_34_00192 :
    nodeClaimChunkValidB branchClaims_5_34 192 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 256. -/
theorem coverageBranchNodes_5_34_00256 :
    nodeClaimChunkValidB branchClaims_5_34 256 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
