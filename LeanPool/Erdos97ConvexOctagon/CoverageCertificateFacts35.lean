/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 0). -/
theorem coverageBranchRoot_1_00 :
    branchClaimRootValidB 1 0 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (6, 34). -/
theorem coverageBranchRoot_6_34 :
    branchClaimRootValidB 6 34 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 24). -/
theorem coverageBranchRoot_3_24 :
    branchClaimRootValidB 3 24 (.search branchClaims3Row24) = true := by
  rfl

/-- Node audit for fixed branch (3, 23), starting at 256. -/
theorem coverageBranchNodes_3_23_00256 :
    nodeClaimChunkValidB branchClaims3Row23 256 41 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 0. -/
theorem coverageBranchNodes_3_24_00000 :
    nodeClaimChunkValidB branchClaims3Row24 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 64. -/
theorem coverageBranchNodes_3_24_00064 :
    nodeClaimChunkValidB branchClaims3Row24 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 128. -/
theorem coverageBranchNodes_3_24_00128 :
    nodeClaimChunkValidB branchClaims3Row24 128 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
