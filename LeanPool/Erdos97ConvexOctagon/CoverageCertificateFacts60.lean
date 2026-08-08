/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 7). -/
theorem coverageBranchRoot_3_07 :
    branchClaimRootValidB 3 7 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 25). -/
theorem coverageBranchRoot_5_25 :
    branchClaimRootValidB 5 25 (.search branchClaims5Row25) = true := by
  rfl

/-- Node audit for fixed branch (5, 25), starting at 0. -/
theorem coverageBranchNodes_5_25_00000 :
    nodeClaimChunkValidB branchClaims5Row25 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 25), starting at 64. -/
theorem coverageBranchNodes_5_25_00064 :
    nodeClaimChunkValidB branchClaims5Row25 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 25), starting at 128. -/
theorem coverageBranchNodes_5_25_00128 :
    nodeClaimChunkValidB branchClaims5Row25 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 25), starting at 192. -/
theorem coverageBranchNodes_5_25_00192 :
    nodeClaimChunkValidB branchClaims5Row25 192 31 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
