/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 12). -/
theorem coverageBranchRoot_0_12 :
    branchClaimRootValidB 0 12 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 26). -/
theorem coverageBranchRoot_4_26 :
    branchClaimRootValidB 4 26 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 34). -/
theorem coverageBranchRoot_1_34 :
    branchClaimRootValidB 1 34 (.search branchClaims_1_34) = true := by
  rfl

/-- Root audit for fixed branch (2, 1). -/
theorem coverageBranchRoot_2_01 :
    branchClaimRootValidB 2 1 (.search branchClaims_2_1) = true := by
  rfl

/-- Node audit for fixed branch (1, 33), starting at 192. -/
theorem coverageBranchNodes_1_33_00192 :
    nodeClaimChunkValidB branchClaims_1_33 192 40 = true := by
  rfl

/-- Node audit for fixed branch (1, 34), starting at 0. -/
theorem coverageBranchNodes_1_34_00000 :
    nodeClaimChunkValidB branchClaims_1_34 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 34), starting at 64. -/
theorem coverageBranchNodes_1_34_00064 :
    nodeClaimChunkValidB branchClaims_1_34 64 41 = true := by
  rfl

/-- Node audit for fixed branch (2, 1), starting at 0. -/
theorem coverageBranchNodes_2_01_00000 :
    nodeClaimChunkValidB branchClaims_2_1 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
