/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 21). -/
theorem coverageBranchRoot_2_21 :
    branchClaimRootValidB 2 21 (.patternThree 1) = true := by
  rfl

/-- Root audit for fixed branch (5, 19). -/
theorem coverageBranchRoot_5_19 :
    branchClaimRootValidB 5 19 (.search branchClaims5Row19) = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 128. -/
theorem coverageBranchNodes_5_18_00128 :
    nodeClaimChunkValidB branchClaims5Row18 128 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 18), starting at 192. -/
theorem coverageBranchNodes_5_18_00192 :
    nodeClaimChunkValidB branchClaims5Row18 192 62 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 0. -/
theorem coverageBranchNodes_5_19_00000 :
    nodeClaimChunkValidB branchClaims5Row19 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 19), starting at 64. -/
theorem coverageBranchNodes_5_19_00064 :
    nodeClaimChunkValidB branchClaims5Row19 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
