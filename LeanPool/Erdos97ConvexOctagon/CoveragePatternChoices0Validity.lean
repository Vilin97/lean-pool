/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices0
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static pattern-summary choice validity for one incidence row -/

namespace Erdos97Octagon.RawIncidence

/-- Every placed pattern summary for centre 0 belongs to the audited summary data. -/
theorem patternSummaryChoices0_members :
    patternSummaryChoices0.all (fun choice =>
      choice.patterns.all (fun bucket =>
        bucket.all PatternSummary.memberB) && choice.pairMaskValidB) = true := by
  rfl

end Erdos97Octagon.RawIncidence
