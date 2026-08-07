/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 5). -/
theorem coverageBranchRoot_0_05 :
    branchClaimRootValidB 0 5 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 19). -/
theorem coverageBranchRoot_4_19 :
    branchClaimRootValidB 4 19 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (1, 19). -/
theorem coverageBranchRoot_1_19 :
    branchClaimRootValidB 1 19 (.search branchClaims_1_19) = true := by
  rfl

/-- Root audit for fixed branch (1, 26). -/
theorem coverageBranchRoot_1_26 :
    branchClaimRootValidB 1 26 (.search branchClaims_1_26) = true := by
  rfl

/-- Node audit for fixed branch (1, 18), starting at 64. -/
theorem coverageBranchNodes_1_18_00064 :
    nodeClaimChunkValidB branchClaims_1_18 64 42 = true := by
  rfl

/-- Node audit for fixed branch (1, 19), starting at 0. -/
theorem coverageBranchNodes_1_19_00000 :
    nodeClaimChunkValidB branchClaims_1_19 0 64 = true := by
  rfl

/-- Node audit for fixed branch (1, 19), starting at 64. -/
theorem coverageBranchNodes_1_19_00064 :
    nodeClaimChunkValidB branchClaims_1_19 64 53 = true := by
  rfl

/-- Node audit for fixed branch (1, 26), starting at 0. -/
theorem coverageBranchNodes_1_26_00000 :
    nodeClaimChunkValidB branchClaims_1_26 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
