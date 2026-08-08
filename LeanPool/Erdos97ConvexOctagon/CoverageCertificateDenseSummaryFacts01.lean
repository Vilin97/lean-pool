/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense pattern summary group 5 agrees with canonical audited data. -/
theorem densePatternSummaries05_canonical :
    densePatternSummaries05.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 6 agrees with canonical audited data. -/
theorem densePatternSummaries06_canonical :
    densePatternSummaries06.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 7 agrees with canonical audited data. -/
theorem densePatternSummaries07_canonical :
    densePatternSummaries07.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 8 agrees with canonical audited data. -/
theorem densePatternSummaries08_canonical :
    densePatternSummaries08.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 9 agrees with canonical audited data. -/
theorem densePatternSummaries09_canonical :
    densePatternSummaries09.toList.all patternSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
