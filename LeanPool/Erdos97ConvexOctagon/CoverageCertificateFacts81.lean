/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 5). -/
theorem coverageBranchRoot_4_05 :
    branchClaimRootValidB 4 5 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 16). -/
theorem coverageBranchRoot_6_16 :
    branchClaimRootValidB 6 16 (.search branchClaims6Row16) = true := by
  rfl

/-- Node audit for fixed branch (6, 15), starting at 64. -/
theorem coverageBranchNodes_6_15_00064 :
    nodeClaimChunkValidB branchClaims6Row15 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 15), starting at 128. -/
theorem coverageBranchNodes_6_15_00128 :
    nodeClaimChunkValidB branchClaims6Row15 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 15), starting at 192. -/
theorem coverageBranchNodes_6_15_00192 :
    nodeClaimChunkValidB branchClaims6Row15 192 9 = true := by
  rfl

/-- Node audit for fixed branch (6, 16), starting at 0. -/
theorem coverageBranchNodes_6_16_00000 :
    nodeClaimChunkValidB branchClaims6Row16 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
