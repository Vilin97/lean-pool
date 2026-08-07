/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 16). -/
theorem coverageBranchRoot_0_16 :
    branchClaimRootValidB 0 16 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (4, 34). -/
theorem coverageBranchRoot_4_34 :
    branchClaimRootValidB 4 34 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (2, 8). -/
theorem coverageBranchRoot_2_08 :
    branchClaimRootValidB 2 8 (.search branchClaims_2_8) = true := by
  rfl

/-- Node audit for fixed branch (2, 6), starting at 64. -/
theorem coverageBranchNodes_2_06_00064 :
    nodeClaimChunkValidB branchClaims_2_6 64 45 = true := by
  rfl

/-- Node audit for fixed branch (2, 8), starting at 0. -/
theorem coverageBranchNodes_2_08_00000 :
    nodeClaimChunkValidB branchClaims_2_8 0 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 8), starting at 64. -/
theorem coverageBranchNodes_2_08_00064 :
    nodeClaimChunkValidB branchClaims_2_8 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 8), starting at 128. -/
theorem coverageBranchNodes_2_08_00128 :
    nodeClaimChunkValidB branchClaims_2_8 128 36 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
