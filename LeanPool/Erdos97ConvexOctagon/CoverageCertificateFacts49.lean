/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 24). -/
theorem coverageBranchRoot_1_24 :
    branchClaimRootValidB 1 24 (.patternThree 179) = true := by
  rfl

/-- Root audit for fixed branch (5, 10). -/
theorem coverageBranchRoot_5_10 :
    branchClaimRootValidB 5 10 (.search branchClaims5Row10) = true := by
  rfl

/-- Node audit for fixed branch (5, 9), starting at 64. -/
theorem coverageBranchNodes_5_09_00064 :
    nodeClaimChunkValidB branchClaims5Row9 64 22 = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 0. -/
theorem coverageBranchNodes_5_10_00000 :
    nodeClaimChunkValidB branchClaims5Row10 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 64. -/
theorem coverageBranchNodes_5_10_00064 :
    nodeClaimChunkValidB branchClaims5Row10 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 10), starting at 128. -/
theorem coverageBranchNodes_5_10_00128 :
    nodeClaimChunkValidB branchClaims5Row10 128 31 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
