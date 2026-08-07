/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 19). -/
theorem coverageBranchRoot_2_19 :
    branchClaimRootValidB 2 19 (.patternThree 2) = true := by
  rfl

/-- Root audit for fixed branch (5, 17). -/
theorem coverageBranchRoot_5_17 :
    branchClaimRootValidB 5 17 (.search branchClaims_5_17) = true := by
  rfl

/-- Node audit for fixed branch (5, 16), starting at 64. -/
theorem coverageBranchNodes_5_16_00064 :
    nodeClaimChunkValidB branchClaims_5_16 64 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 16), starting at 128. -/
theorem coverageBranchNodes_5_16_00128 :
    nodeClaimChunkValidB branchClaims_5_16 128 42 = true := by
  rfl

/-- Node audit for fixed branch (5, 17), starting at 0. -/
theorem coverageBranchNodes_5_17_00000 :
    nodeClaimChunkValidB branchClaims_5_17 0 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 17), starting at 64. -/
theorem coverageBranchNodes_5_17_00064 :
    nodeClaimChunkValidB branchClaims_5_17 64 64 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
