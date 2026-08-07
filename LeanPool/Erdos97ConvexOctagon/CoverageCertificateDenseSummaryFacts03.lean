/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense pattern summary group 15 agrees with canonical audited data. -/
theorem densePatternSummaries15_canonical :
    densePatternSummaries15.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 16 agrees with canonical audited data. -/
theorem densePatternSummaries16_canonical :
    densePatternSummaries16.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 17 agrees with canonical audited data. -/
theorem densePatternSummaries17_canonical :
    densePatternSummaries17.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 18 agrees with canonical audited data. -/
theorem densePatternSummaries18_canonical :
    densePatternSummaries18.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 19 agrees with canonical audited data. -/
theorem densePatternSummaries19_canonical :
    densePatternSummaries19.toList.all patternSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
