/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 15). -/
theorem coverageBranchRoot_0_15 :
    branchClaimRootValidB 0 15 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 33). -/
theorem coverageBranchRoot_4_33 :
    branchClaimRootValidB 4 33 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 5). -/
theorem coverageBranchRoot_2_05 :
    branchClaimRootValidB 2 5 (.search branchClaims_2_5) = true := by
  rfl

/-- Root audit for fixed branch (2, 6). -/
theorem coverageBranchRoot_2_06 :
    branchClaimRootValidB 2 6 (.search branchClaims_2_6) = true := by
  rfl

/-- Node audit for fixed branch (2, 4), starting at 64. -/
theorem coverageBranchNodes_2_04_00064 :
    nodeClaimChunkValidB branchClaims_2_4 64 50 = true := by
  rfl

/-- Node audit for fixed branch (2, 5), starting at 0. -/
theorem coverageBranchNodes_2_05_00000 :
    nodeClaimChunkValidB branchClaims_2_5 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 5), starting at 64. -/
theorem coverageBranchNodes_2_05_00064 :
    nodeClaimChunkValidB branchClaims_2_5 64 61 = true := by
  rfl

/-- Node audit for fixed branch (2, 6), starting at 0. -/
theorem coverageBranchNodes_2_06_00000 :
    nodeClaimChunkValidB branchClaims_2_6 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
