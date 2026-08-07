/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData19
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData20

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 8). -/
theorem coverageBranchRoot_4_08 :
    branchClaimRootValidB 4 8 (.patternTwo 0) = true := by
  rfl

/-- Root audit for fixed branch (6, 27). -/
theorem coverageBranchRoot_6_27 :
    branchClaimRootValidB 6 27 (.search branchClaims_6_27) = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 128. -/
theorem coverageBranchNodes_6_26_00128 :
    nodeClaimChunkValidB branchClaims_6_26 128 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 26), starting at 192. -/
theorem coverageBranchNodes_6_26_00192 :
    nodeClaimChunkValidB branchClaims_6_26 192 40 = true := by
  rfl

/-- Node audit for fixed branch (6, 27), starting at 0. -/
theorem coverageBranchNodes_6_27_00000 :
    nodeClaimChunkValidB branchClaims_6_27 0 64 = true := by
  rfl

/-- Node audit for fixed branch (6, 27), starting at 64. -/
theorem coverageBranchNodes_6_27_00064 :
    nodeClaimChunkValidB branchClaims_6_27 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
