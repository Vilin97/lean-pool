/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 34). -/
theorem coverageBranchRoot_3_34 :
    branchClaimRootValidB 3 34 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 5). -/
theorem coverageBranchRoot_6_05 :
    branchClaimRootValidB 6 5 (.search branchClaims6Row5) = true := by
  rfl

/-- Root audit for fixed branch (6, 6). -/
theorem coverageBranchRoot_6_06 :
    branchClaimRootValidB 6 6 (.search branchClaims6Row6) = true := by
  rfl

/-- Root audit for fixed branch (6, 7). -/
theorem coverageBranchRoot_6_07 :
    branchClaimRootValidB 6 7 (.search branchClaims6Row7) = true := by
  rfl

/-- Node audit for fixed branch (6, 5), starting at 0. -/
theorem coverageBranchNodes_6_05_00000 :
    nodeClaimChunkValidB branchClaims6Row5 0 40 = true := by
  rfl

/-- Node audit for fixed branch (6, 6), starting at 0. -/
theorem coverageBranchNodes_6_06_00000 :
    nodeClaimChunkValidB branchClaims6Row6 0 35 = true := by
  rfl

/-- Node audit for fixed branch (6, 7), starting at 0. -/
theorem coverageBranchNodes_6_07_00000 :
    nodeClaimChunkValidB branchClaims6Row7 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 7), starting at 64. -/
theorem coverageBranchNodes_6_07_00064 :
    nodeClaimChunkValidB branchClaims6Row7 64 39 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
