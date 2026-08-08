/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 19). -/
theorem coverageBranchRoot_3_19 :
    branchClaimRootValidB 3 19 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 32). -/
theorem coverageBranchRoot_5_32 :
    branchClaimRootValidB 5 32 (.search branchClaims5Row32) = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 384. -/
theorem coverageBranchNodes_5_31_00384 :
    nodeClaimChunkValidB branchClaims5Row31 384 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 448. -/
theorem coverageBranchNodes_5_31_00448 :
    nodeClaimChunkValidB branchClaims5Row31 448 38 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 0. -/
theorem coverageBranchNodes_5_32_00000 :
    nodeClaimChunkValidB branchClaims5Row32 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 32), starting at 64. -/
theorem coverageBranchNodes_5_32_00064 :
    nodeClaimChunkValidB branchClaims5Row32 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
