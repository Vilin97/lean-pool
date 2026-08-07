/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoveragePatternChoices2
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static pattern-summary choice validity for one incidence row -/

namespace Erdos97Octagon.RawIncidence

/-- Every placed pattern summary for centre 2 belongs to the audited summary data. -/
theorem patternSummaryChoices2_members :
    patternSummaryChoices2.all (fun choice =>
      choice.patterns.all (fun bucket =>
        bucket.all PatternSummary.memberB) && choice.pairMaskValidB) = true := by
  rfl

end Erdos97Octagon.RawIncidence
