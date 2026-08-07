/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 20). -/
theorem coverageBranchRoot_2_20 :
    branchClaimRootValidB 2 20 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 19). -/
theorem coverageBranchRoot_5_19 :
    branchClaimRootValidB 5 19 (.search branchClaims_5_19) = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 192. -/
theorem coverageBranchNodes_5_18_00192 :
    nodeClaimChunkValidB branchClaims_5_18 192 62 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 0. -/
theorem coverageBranchNodes_5_19_00000 :
    nodeClaimChunkValidB branchClaims_5_19 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 64. -/
theorem coverageBranchNodes_5_19_00064 :
    nodeClaimChunkValidB branchClaims_5_19 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 128. -/
theorem coverageBranchNodes_5_19_00128 :
    nodeClaimChunkValidB branchClaims_5_19 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
