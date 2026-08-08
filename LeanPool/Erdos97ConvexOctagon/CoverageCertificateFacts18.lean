/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 18). -/
theorem coverageBranchRoot_0_18 :
    branchClaimRootValidB 0 18 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 1). -/
theorem coverageBranchRoot_5_01 :
    branchClaimRootValidB 5 1 (.patternThree 180) = true := by
  rfl

/-- Root audit for fixed branch (2, 11). -/
theorem coverageBranchRoot_2_11 :
    branchClaimRootValidB 2 11 (.search branchClaims2Row11) = true := by
  rfl

/-- Root audit for fixed branch (2, 12). -/
theorem coverageBranchRoot_2_12 :
    branchClaimRootValidB 2 12 (.search branchClaims2Row12) = true := by
  rfl

/-- Root audit for fixed branch (2, 14). -/
theorem coverageBranchRoot_2_14 :
    branchClaimRootValidB 2 14 (.search branchClaims2Row14) = true := by
  rfl

/-- Node audit for fixed branch (2, 11), starting at 0. -/
theorem coverageBranchNodes_2_11_00000 :
    nodeClaimChunkValidB branchClaims2Row11 0 15 = true := by
  rfl

/-- Node audit for fixed branch (2, 12), starting at 0. -/
theorem coverageBranchNodes_2_12_00000 :
    nodeClaimChunkValidB branchClaims2Row12 0 28 = true := by
  rfl

/-- Node audit for fixed branch (2, 14), starting at 0. -/
theorem coverageBranchNodes_2_14_00000 :
    nodeClaimChunkValidB branchClaims2Row14 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 14), starting at 64. -/
theorem coverageBranchNodes_2_14_00064 :
    nodeClaimChunkValidB branchClaims2Row14 64 56 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
