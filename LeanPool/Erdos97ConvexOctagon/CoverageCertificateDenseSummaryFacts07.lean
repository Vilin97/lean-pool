/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense hard summary group 13 agrees with canonical audited data. -/
theorem denseHardSummaries13_canonical :
    denseHardSummaries13.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 14 agrees with canonical audited data. -/
theorem denseHardSummaries14_canonical :
    denseHardSummaries14.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 15 agrees with canonical audited data. -/
theorem denseHardSummaries15_canonical :
    denseHardSummaries15.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 16 agrees with canonical audited data. -/
theorem denseHardSummaries16_canonical :
    denseHardSummaries16.toList.all hardSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
