/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static exact-table summary choices for one canonical orbit -/

namespace Erdos97Octagon.RawIncidence

/-- Exact-table summaries indexed by the second-row choice for orbit 0. -/
def hardSummaryChoices0 : Array HardSummaryBuckets :=
#[
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ],
[
  ]
]

/-- Every hard summary for orbit 0 belongs to the audited summary data. -/
theorem hardSummaryChoices0_members :
    hardSummaryChoices0.toList.all (fun summaries =>
      summaries.all (fun bucket => bucket.all HardSummary.memberB)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
