/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15

/-! # Bounded coverage-certificate computation facts -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 16). -/
theorem coverageBranchRoot_3_16 :
    branchClaimRootValidB 3 16 (.patternThree 2) = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 256. -/
theorem coverageBranchNodes_5_31_00256 :
    nodeClaimChunkValidB branchClaims_5_31 256 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 320. -/
theorem coverageBranchNodes_5_31_00320 :
    nodeClaimChunkValidB branchClaims_5_31 320 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 384. -/
theorem coverageBranchNodes_5_31_00384 :
    nodeClaimChunkValidB branchClaims_5_31 384 64 = true := by
  rfl

/-- Node audit for fixed branch (5, 31), starting at 448. -/
theorem coverageBranchNodes_5_31_00448 :
    nodeClaimChunkValidB branchClaims_5_31 448 38 = true := by
  rfl

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
