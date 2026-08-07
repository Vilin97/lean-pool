/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData16
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 21). -/
theorem coverageBranchRoot_3_21 :
    branchClaimRootValidB 3 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (6, 2). -/
theorem coverageBranchRoot_6_02 :
    branchClaimRootValidB 6 2 (.search branchClaims_6_2) = true := by
  rfl

/-- Root audit for fixed branch (6, 3). -/
theorem coverageBranchRoot_6_03 :
    branchClaimRootValidB 6 3 (.search branchClaims_6_3) = true := by
  rfl

/-- Root audit for fixed branch (6, 4). -/
theorem coverageBranchRoot_6_04 :
    branchClaimRootValidB 6 4 (.search branchClaims_6_4) = true := by
  rfl

/-- Root audit for fixed branch (6, 5). -/
theorem coverageBranchRoot_6_05 :
    branchClaimRootValidB 6 5 (.search branchClaims_6_5) = true := by
  rfl

/-- Node audit for fixed branch (6, 2), starting at 0. -/
theorem coverageBranchNodes_6_02_00000 :
    nodeClaimChunkValidB branchClaims_6_2 0 52 = true := by
  rfl

/-- Node audit for fixed branch (6, 3), starting at 0. -/
theorem coverageBranchNodes_6_03_00000 :
    nodeClaimChunkValidB branchClaims_6_3 0 42 = true := by
  rfl

/-- Node audit for fixed branch (6, 4), starting at 0. -/
theorem coverageBranchNodes_6_04_00000 :
    nodeClaimChunkValidB branchClaims_6_4 0 51 = true := by
  rfl

/-- Node audit for fixed branch (6, 5), starting at 0. -/
theorem coverageBranchNodes_6_05_00000 :
    nodeClaimChunkValidB branchClaims_6_5 0 40 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
