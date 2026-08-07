/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 31). -/
theorem coverageBranchRoot_0_31 :
    branchClaimRootValidB 0 31 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 21). -/
theorem coverageBranchRoot_6_21 :
    branchClaimRootValidB 6 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (3, 5). -/
theorem coverageBranchRoot_3_05 :
    branchClaimRootValidB 3 5 (.search branchClaims_3_5) = true := by
  rfl

/-- Root audit for fixed branch (3, 6). -/
theorem coverageBranchRoot_3_06 :
    branchClaimRootValidB 3 6 (.search branchClaims_3_6) = true := by
  rfl

/-- Node audit for fixed branch (3, 4), starting at 64. -/
theorem coverageBranchNodes_3_04_00064 :
    nodeClaimChunkValidB branchClaims_3_4 64 50 = true := by
  rfl

/-- Node audit for fixed branch (3, 5), starting at 0. -/
theorem coverageBranchNodes_3_05_00000 :
    nodeClaimChunkValidB branchClaims_3_5 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 5), starting at 64. -/
theorem coverageBranchNodes_3_05_00064 :
    nodeClaimChunkValidB branchClaims_3_5 64 52 = true := by
  rfl

/-- Node audit for fixed branch (3, 6), starting at 0. -/
theorem coverageBranchNodes_3_06_00000 :
    nodeClaimChunkValidB branchClaims_3_6 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
