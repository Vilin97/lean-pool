/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryChoicesValidity

/-! # Validity audits for static coverage-summary placement -/

namespace Erdos97Octagon.RawIncidence

/-- Every pattern summary placed at a row belongs to the audited data, and the
precomputed pair mask describes that row. -/
theorem patternSummaryChoices_valid (centre : Vertex) :
    (patternSummaryChoices.getD centre.val []).all (fun choice =>
      choice.patterns.all (fun bucket =>
        bucket.all PatternSummary.memberB) && choice.pairMaskValidB) = true := by
  fin_cases centre
  · exact patternSummaryChoices0_members
  · exact patternSummaryChoices1_members
  · exact patternSummaryChoices2_members
  · exact patternSummaryChoices3_members
  · exact patternSummaryChoices4_members
  · exact patternSummaryChoices5_members
  · exact patternSummaryChoices6_members
  · exact patternSummaryChoices7_members

/-- Every exact summary placed in a canonical-orbit branch belongs to the
audited summary data. -/
theorem hardSummaryChoices_valid (orbit : Fin 7) :
    (hardSummaryChoices.getD orbit.val #[]).toList.all (fun summaries =>
      summaries.all (fun bucket => bucket.all HardSummary.memberB)) = true := by
  fin_cases orbit
  · exact hardSummaryChoices0_members
  · exact hardSummaryChoices1_members
  · exact hardSummaryChoices2_members
  · exact hardSummaryChoices3_members
  · exact hardSummaryChoices4_members
  · exact hardSummaryChoices5_members
  · exact hardSummaryChoices6_members

end Erdos97Octagon.RawIncidence
