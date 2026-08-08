/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense pattern summary group 10 agrees with canonical audited data. -/
theorem densePatternSummaries10_canonical :
    densePatternSummaries10.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 11 agrees with canonical audited data. -/
theorem densePatternSummaries11_canonical :
    densePatternSummaries11.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 12 agrees with canonical audited data. -/
theorem densePatternSummaries12_canonical :
    densePatternSummaries12.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 13 agrees with canonical audited data. -/
theorem densePatternSummaries13_canonical :
    densePatternSummaries13.toList.all patternSummaryCanonicalB = true := by
  decide

/-- Dense pattern summary group 14 agrees with canonical audited data. -/
theorem densePatternSummaries14_canonical :
    densePatternSummaries14.toList.all patternSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
