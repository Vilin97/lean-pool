/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static exact-table summary choices for one canonical orbit -/

namespace Erdos97Octagon.RawIncidence

/-- Exact-table summaries indexed by the second-row choice for orbit 4. -/
def hardSummaryChoices4 : Array HardSummaryBuckets :=
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

/-- Every hard summary for orbit 4 belongs to the audited summary data. -/
theorem hardSummaryChoices4_members :
    hardSummaryChoices4.toList.all (fun summaries =>
      summaries.all (fun bucket => bucket.all HardSummary.memberB)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
