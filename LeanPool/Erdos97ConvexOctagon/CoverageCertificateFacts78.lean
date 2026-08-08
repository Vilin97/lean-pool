/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 2). -/
theorem coverageBranchRoot_4_02 :
    branchClaimRootValidB 4 2 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 11). -/
theorem coverageBranchRoot_6_11 :
    branchClaimRootValidB 6 11 (.search branchClaims6Row11) = true := by
  rfl

/-- Root audit for fixed branch (6, 12). -/
theorem coverageBranchRoot_6_12 :
    branchClaimRootValidB 6 12 (.search branchClaims6Row12) = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 0. -/
theorem coverageBranchNodes_6_11_00000 :
    nodeClaimChunkValidB branchClaims6Row11 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 64. -/
theorem coverageBranchNodes_6_11_00064 :
    nodeClaimChunkValidB branchClaims6Row11 64 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 11), starting at 128. -/
theorem coverageBranchNodes_6_11_00128 :
    nodeClaimChunkValidB branchClaims6Row11 128 14 = true := by
  rfl

/-- Node audit for fixed branch (6, 12), starting at 0. -/
theorem coverageBranchNodes_6_12_00000 :
    nodeClaimChunkValidB branchClaims6Row12 0 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
