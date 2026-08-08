/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 19). -/
theorem coverageBranchRoot_0_19 :
    branchClaimRootValidB 0 19 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 2). -/
theorem coverageBranchRoot_5_02 :
    branchClaimRootValidB 5 2 (.patternThree 180) = true := by
  rfl

/-- Root audit for fixed branch (2, 15). -/
theorem coverageBranchRoot_2_15 :
    branchClaimRootValidB 2 15 (.search branchClaims2Row15) = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 0. -/
theorem coverageBranchNodes_2_15_00000 :
    nodeClaimChunkValidB branchClaims2Row15 0 32 = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 32. -/
theorem coverageBranchNodes_2_15_00032 :
    nodeClaimChunkValidB branchClaims2Row15 32 32 = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 64. -/
theorem coverageBranchNodes_2_15_00064 :
    nodeClaimChunkValidB branchClaims2Row15 64 64 = true := by
  rfl

/-- Node audit for fixed branch (2, 15), starting at 128. -/
theorem coverageBranchNodes_2_15_00128 :
    nodeClaimChunkValidB branchClaims2Row15 128 7 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
