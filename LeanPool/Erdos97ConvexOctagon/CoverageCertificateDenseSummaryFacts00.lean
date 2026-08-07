/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense pattern summary group 0 agrees with canonical audited data. -/
theorem densePatternSummaries00_canonical :
    densePatternSummaries00.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 1 agrees with canonical audited data. -/
theorem densePatternSummaries01_canonical :
    densePatternSummaries01.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 2 agrees with canonical audited data. -/
theorem densePatternSummaries02_canonical :
    densePatternSummaries02.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 3 agrees with canonical audited data. -/
theorem densePatternSummaries03_canonical :
    densePatternSummaries03.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 4 agrees with canonical audited data. -/
theorem densePatternSummaries04_canonical :
    densePatternSummaries04.toList.all patternSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

