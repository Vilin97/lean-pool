/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices6
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static exact-table summary choice validity for one canonical orbit -/

namespace Erdos97Octagon.RawIncidence

/-- Every hard summary for orbit 6 belongs to the audited summary data. -/
theorem hardSummaryChoices6_members :
    hardSummaryChoices6.toList.all (fun summaries =>
      summaries.all (fun bucket => bucket.all HardSummary.memberB)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
