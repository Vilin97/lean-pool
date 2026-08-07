/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 3). -/
theorem coverageBranchRoot_1_03 :
    branchClaimRootValidB 1 3 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (6, 33). -/
theorem coverageBranchRoot_6_33 :
    branchClaimRootValidB 6 33 (.patternThree 6) = true := by
  rfl

/-- Root audit for fixed branch (3, 27). -/
theorem coverageBranchRoot_3_27 :
    branchClaimRootValidB 3 27 (.search branchClaims_3_27) = true := by
  rfl

/-- Node audit for fixed branch (3, 26), starting at 128. -/
theorem coverageBranchNodes_3_26_00128 :
    nodeClaimChunkValidB branchClaims_3_26 128 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 26), starting at 192. -/
theorem coverageBranchNodes_3_26_00192 :
    nodeClaimChunkValidB branchClaims_3_26 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 26), starting at 256. -/
theorem coverageBranchNodes_3_26_00256 :
    nodeClaimChunkValidB branchClaims_3_26 256 42 = true := by
  rfl

/-- Node audit for fixed branch (3, 27), starting at 0. -/
theorem coverageBranchNodes_3_27_00000 :
    nodeClaimChunkValidB branchClaims_3_27 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
