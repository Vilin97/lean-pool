/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 22). -/
theorem coverageBranchRoot_1_22 :
    branchClaimRootValidB 1 22 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 6). -/
theorem coverageBranchRoot_5_06 :
    branchClaimRootValidB 5 6 (.search branchClaims5Row6) = true := by
  rfl

/-- Root audit for fixed branch (5, 7). -/
theorem coverageBranchRoot_5_07 :
    branchClaimRootValidB 5 7 (.search branchClaims5Row7) = true := by
  rfl

/-- Node audit for fixed branch (5, 5), starting at 64. -/
theorem coverageBranchNodes_5_05_00064 :
    nodeClaimChunkValidB branchClaims5Row5 64 30 = true := by
  rfl

/-- Node audit for fixed branch (5, 6), starting at 0. -/
theorem coverageBranchNodes_5_06_00000 :
    nodeClaimChunkValidB branchClaims5Row6 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 6), starting at 64. -/
theorem coverageBranchNodes_5_06_00064 :
    nodeClaimChunkValidB branchClaims5Row6 64 29 = true := by
  rfl

/-- Node audit for fixed branch (5, 7), starting at 0. -/
theorem coverageBranchNodes_5_07_00000 :
    nodeClaimChunkValidB branchClaims5Row7 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
