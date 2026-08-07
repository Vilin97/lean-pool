/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 31). -/
theorem coverageBranchRoot_0_31 :
    branchClaimRootValidB 0 31 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (5, 33). -/
theorem coverageBranchRoot_5_33 :
    branchClaimRootValidB 5 33 (.patternThree 3) = true := by
  rfl

/-- Root audit for fixed branch (3, 6). -/
theorem coverageBranchRoot_3_06 :
    branchClaimRootValidB 3 6 (.search branchClaims_3_6) = true := by
  rfl

/-- Root audit for fixed branch (3, 10). -/
theorem coverageBranchRoot_3_10 :
    branchClaimRootValidB 3 10 (.search branchClaims_3_10) = true := by
  rfl

/-- Node audit for fixed branch (3, 6), starting at 0. -/
theorem coverageBranchNodes_3_06_00000 :
    nodeClaimChunkValidB branchClaims_3_6 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 6), starting at 64. -/
theorem coverageBranchNodes_3_06_00064 :
    nodeClaimChunkValidB branchClaims_3_6 64 33 = true := by
  rfl

/-- Node audit for fixed branch (3, 10), starting at 0. -/
theorem coverageBranchNodes_3_10_00000 :
    nodeClaimChunkValidB branchClaims_3_10 0 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 10), starting at 64. -/
theorem coverageBranchNodes_3_10_00064 :
    nodeClaimChunkValidB branchClaims_3_10 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
