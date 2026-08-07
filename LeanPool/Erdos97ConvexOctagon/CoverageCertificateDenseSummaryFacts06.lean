/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness

/-! # Canonical audits for dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Dense hard summary group 8 agrees with canonical audited data. -/
theorem denseHardSummaries08_canonical :
    denseHardSummaries08.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 9 agrees with canonical audited data. -/
theorem denseHardSummaries09_canonical :
    denseHardSummaries09.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 10 agrees with canonical audited data. -/
theorem denseHardSummaries10_canonical :
    denseHardSummaries10.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 11 agrees with canonical audited data. -/
theorem denseHardSummaries11_canonical :
    denseHardSummaries11.toList.all hardSummaryCanonicalB = true := by
  decide

/-- Dense hard summary group 12 agrees with canonical audited data. -/
theorem denseHardSummaries12_canonical :
    denseHardSummaries12.toList.all hardSummaryCanonicalB = true := by
  decide

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

