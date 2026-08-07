/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices0
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices1
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices2
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices3
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices4
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices5
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices6
import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices7
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices0
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices1
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices2
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices3
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices4
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices5
import LeanPool.Erdos97ConvexOctagon.CoverageHardChoices6

/-! # Aggregated static coverage-summary choices -/

namespace Erdos97Octagon.RawIncidence

/-- Legal rows paired with summaries whose last assigned nonempty row is that row. -/
def patternSummaryChoices : Array (List SummaryRowChoice) := #[
  patternSummaryChoices0,
  patternSummaryChoices1,
  patternSummaryChoices2,
  patternSummaryChoices3,
  patternSummaryChoices4,
  patternSummaryChoices5,
  patternSummaryChoices6,
  patternSummaryChoices7
]

/-- Exact-table summaries indexed by canonical orbit and second-row choice. -/
def hardSummaryChoices : Array (Array HardSummaryBuckets) := #[
  hardSummaryChoices0,
  hardSummaryChoices1,
  hardSummaryChoices2,
  hardSummaryChoices3,
  hardSummaryChoices4,
  hardSummaryChoices5,
  hardSummaryChoices6
]

end Erdos97Octagon.RawIncidence
