/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 1). -/
theorem coverageBranchRoot_1_01 :
    branchClaimRootValidB 1 1 (.patternThree 178) = true := by
  rfl

/-- Root audit for fixed branch (3, 25). -/
theorem coverageBranchRoot_3_25 :
    branchClaimRootValidB 3 25 (.search branchClaims3Row25) = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 192. -/
theorem coverageBranchNodes_3_24_00192 :
    nodeClaimChunkValidB branchClaims3Row24 192 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 256. -/
theorem coverageBranchNodes_3_24_00256 :
    nodeClaimChunkValidB branchClaims3Row24 256 64 = true := by
  rfl

/-- Node audit for fixed branch (3, 24), starting at 320. -/
theorem coverageBranchNodes_3_24_00320 :
    nodeClaimChunkValidB branchClaims3Row24 320 29 = true := by
  rfl

/-- Node audit for fixed branch (3, 25), starting at 0. -/
theorem coverageBranchNodes_3_25_00000 :
    nodeClaimChunkValidB branchClaims3Row25 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
