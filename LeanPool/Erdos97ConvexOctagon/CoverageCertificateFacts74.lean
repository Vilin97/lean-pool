/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 33). -/
theorem coverageBranchRoot_3_33 :
    branchClaimRootValidB 3 33 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 2). -/
theorem coverageBranchRoot_6_02 :
    branchClaimRootValidB 6 2 (.search branchClaims6Row2) = true := by
  rfl

/-- Root audit for fixed branch (6, 3). -/
theorem coverageBranchRoot_6_03 :
    branchClaimRootValidB 6 3 (.search branchClaims6Row3) = true := by
  rfl

/-- Root audit for fixed branch (6, 4). -/
theorem coverageBranchRoot_6_04 :
    branchClaimRootValidB 6 4 (.search branchClaims6Row4) = true := by
  rfl

/-- Node audit for fixed branch (6, 1), starting at 64. -/
theorem coverageBranchNodes_6_01_00064 :
    nodeClaimChunkValidB branchClaims6Row1 64 1 = true := by
  rfl

/-- Node audit for fixed branch (6, 2), starting at 0. -/
theorem coverageBranchNodes_6_02_00000 :
    nodeClaimChunkValidB branchClaims6Row2 0 52 = true := by
  rfl

/-- Node audit for fixed branch (6, 3), starting at 0. -/
theorem coverageBranchNodes_6_03_00000 :
    nodeClaimChunkValidB branchClaims6Row3 0 42 = true := by
  rfl

/-- Node audit for fixed branch (6, 4), starting at 0. -/
theorem coverageBranchNodes_6_04_00000 :
    nodeClaimChunkValidB branchClaims6Row4 0 51 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
