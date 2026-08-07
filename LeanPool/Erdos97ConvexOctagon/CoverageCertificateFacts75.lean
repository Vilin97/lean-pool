/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData18

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 34). -/
theorem coverageBranchRoot_3_34 :
    branchClaimRootValidB 3 34 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (6, 12). -/
theorem coverageBranchRoot_6_12 :
    branchClaimRootValidB 6 12 (.search branchClaims_6_12) = true := by
  rfl

/-- Root audit for fixed branch (6, 13). -/
theorem coverageBranchRoot_6_13 :
    branchClaimRootValidB 6 13 (.search branchClaims_6_13) = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 128. -/
theorem coverageBranchNodes_6_11_00128 :
    nodeClaimChunkValidB branchClaims_6_11 128 14 = true := by
  rfl

/-- Node audit for fixed branch (6, 12), starting at 0. -/
theorem coverageBranchNodes_6_12_00000 :
    nodeClaimChunkValidB branchClaims_6_12 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 12), starting at 64. -/
theorem coverageBranchNodes_6_12_00064 :
    nodeClaimChunkValidB branchClaims_6_12 64 61 = true := by
  rfl

/-- Node audit for fixed branch (6, 13), starting at 0. -/
theorem coverageBranchNodes_6_13_00000 :
    nodeClaimChunkValidB branchClaims_6_13 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
