/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 12). -/
theorem coverageBranchRoot_0_12 :
    branchClaimRootValidB 0 12 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 30). -/
theorem coverageBranchRoot_4_30 :
    branchClaimRootValidB 4 30 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 34). -/
theorem coverageBranchRoot_1_34 :
    branchClaimRootValidB 1 34 (.search branchClaims1Row34) = true := by
  rfl

/-- Node audit for fixed branch (1, 33), starting at 64. -/
theorem coverageBranchNodes_1_33_00064 :
    nodeClaimChunkValidB branchClaims1Row33 64 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 33), starting at 128. -/
theorem coverageBranchNodes_1_33_00128 :
    nodeClaimChunkValidB branchClaims1Row33 128 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 33), starting at 192. -/
theorem coverageBranchNodes_1_33_00192 :
    nodeClaimChunkValidB branchClaims1Row33 192 40 = true := by
  rfl

/-- Node audit for fixed branch (1, 34), starting at 0. -/
theorem coverageBranchNodes_1_34_00000 :
    nodeClaimChunkValidB branchClaims1Row34 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
