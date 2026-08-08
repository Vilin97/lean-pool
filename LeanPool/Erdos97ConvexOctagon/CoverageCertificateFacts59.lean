/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 0). -/
theorem coverageBranchRoot_3_00 :
    branchClaimRootValidB 3 0 (.patternThree 1) = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 64. -/
theorem coverageBranchNodes_5_24_00064 :
    nodeClaimChunkValidB branchClaims5Row24 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 128. -/
theorem coverageBranchNodes_5_24_00128 :
    nodeClaimChunkValidB branchClaims5Row24 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 192. -/
theorem coverageBranchNodes_5_24_00192 :
    nodeClaimChunkValidB branchClaims5Row24 192 25 = true := by
  rfl

/-- Node audit for fixed branch (5, 24), starting at 217. -/
theorem coverageBranchNodes_5_24_00217 :
    nodeClaimChunkValidB branchClaims5Row24 217 25 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
