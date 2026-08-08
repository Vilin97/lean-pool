/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 32). -/
theorem coverageBranchRoot_0_32 :
    branchClaimRootValidB 0 32 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 22). -/
theorem coverageBranchRoot_6_22 :
    branchClaimRootValidB 6 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (3, 10). -/
theorem coverageBranchRoot_3_10 :
    branchClaimRootValidB 3 10 (.search branchClaims3Row10) = true := by
  rfl

/-- Node audit for fixed branch (3, 6), starting at 64. -/
theorem coverageBranchNodes_3_06_00064 :
    nodeClaimChunkValidB branchClaims3Row6 64 33 = true := by
  rfl

/-- Node audit for fixed branch (3, 10), starting at 0. -/
theorem coverageBranchNodes_3_10_00000 :
    nodeClaimChunkValidB branchClaims3Row10 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 10), starting at 64. -/
theorem coverageBranchNodes_3_10_00064 :
    nodeClaimChunkValidB branchClaims3Row10 64 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 10), starting at 128. -/
theorem coverageBranchNodes_3_10_00128 :
    nodeClaimChunkValidB branchClaims3Row10 128 17 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
