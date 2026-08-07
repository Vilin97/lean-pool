/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 21). -/
theorem coverageBranchRoot_3_21 :
    branchClaimRootValidB 3 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 34). -/
theorem coverageBranchRoot_5_34 :
    branchClaimRootValidB 5 34 (.search branchClaims_5_34) = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 352. -/
theorem coverageBranchNodes_5_32_00352 :
    nodeClaimChunkValidB branchClaims_5_32 352 32 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 384. -/
theorem coverageBranchNodes_5_32_00384 :
    nodeClaimChunkValidB branchClaims_5_32 384 29 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 413. -/
theorem coverageBranchNodes_5_32_00413 :
    nodeClaimChunkValidB branchClaims_5_32 413 29 = true := by
  rfl

/-- Node audit for fixed branch (5, 34), starting at 0. -/
theorem coverageBranchNodes_5_34_00000 :
    nodeClaimChunkValidB branchClaims_5_34 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
