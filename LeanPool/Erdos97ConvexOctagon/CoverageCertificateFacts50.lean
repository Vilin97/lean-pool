/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 25). -/
theorem coverageBranchRoot_1_25 :
    branchClaimRootValidB 1 25 (.patternThree 179) = true := by
  rfl

/-- Root audit for fixed branch (5, 11). -/
theorem coverageBranchRoot_5_11 :
    branchClaimRootValidB 5 11 (.search branchClaims5Row11) = true := by
  rfl

/-- Root audit for fixed branch (5, 12). -/
theorem coverageBranchRoot_5_12 :
    branchClaimRootValidB 5 12 (.search branchClaims5Row12) = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 0. -/
theorem coverageBranchNodes_5_11_00000 :
    nodeClaimChunkValidB branchClaims5Row11 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 64. -/
theorem coverageBranchNodes_5_11_00064 :
    nodeClaimChunkValidB branchClaims5Row11 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 11), starting at 128. -/
theorem coverageBranchNodes_5_11_00128 :
    nodeClaimChunkValidB branchClaims5Row11 128 25 = true := by
  rfl

/-- Node audit for fixed branch (5, 12), starting at 0. -/
theorem coverageBranchNodes_5_12_00000 :
    nodeClaimChunkValidB branchClaims5Row12 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
