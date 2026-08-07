/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense pattern summary group 20 agrees with canonical audited data. -/
theorem densePatternSummaries20_canonical :
    densePatternSummaries20.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 21 agrees with canonical audited data. -/
theorem densePatternSummaries21_canonical :
    densePatternSummaries21.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 0 agrees with canonical audited data. -/
theorem denseHardSummaries00_canonical :
    denseHardSummaries00.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 1 agrees with canonical audited data. -/
theorem denseHardSummaries01_canonical :
    denseHardSummaries01.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 2 agrees with canonical audited data. -/
theorem denseHardSummaries02_canonical :
    denseHardSummaries02.toList.all hardSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

