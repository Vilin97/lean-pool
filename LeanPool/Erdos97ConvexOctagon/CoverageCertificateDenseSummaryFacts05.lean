/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense hard summary group 3 agrees with canonical audited data. -/
theorem denseHardSummaries03_canonical :
    denseHardSummaries03.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 4 agrees with canonical audited data. -/
theorem denseHardSummaries04_canonical :
    denseHardSummaries04.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 5 agrees with canonical audited data. -/
theorem denseHardSummaries05_canonical :
    denseHardSummaries05.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 6 agrees with canonical audited data. -/
theorem denseHardSummaries06_canonical :
    denseHardSummaries06.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 7 agrees with canonical audited data. -/
theorem denseHardSummaries07_canonical :
    denseHardSummaries07.toList.all hardSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

