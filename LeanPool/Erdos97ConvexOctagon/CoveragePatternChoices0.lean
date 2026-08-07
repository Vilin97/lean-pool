/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Static pattern-summary choices for one incidence row -/

namespace Erdos97Octagon.RawIncidence

/-- Row masks and compatible highest-row pattern summaries for centre 0. -/
def patternSummaryChoices0 : List SummaryRowChoice := [
  ⟨30, 270015488,
[
    ]⟩,
  ⟨46, 539503616,
[
    ]⟩,
  ⟨78, 1078479872,
[
    ]⟩,
  ⟨142, 2156432384,
[
    ]⟩,
  ⟨54, 137442112512,
[
    ]⟩,
  ⟨86, 274883171328,
[
    ]⟩,
  ⟨150, 549765288960,
[
    ]⟩,
  ⟨102, 70368750494720,
[
    ]⟩,
  ⟨166, 140737498883072,
[
    ]⟩,
  ⟨198, 36028797031597056,
[
    ]⟩,
  ⟨58, 138244274176,
[
    ]⟩,
  ⟨90, 276220106752,
[
    ]⟩,
  ⟨154, 552171771904,
[
    ]⟩,
  ⟨106, 70370354817024,
[
    ]⟩,
  ⟨170, 140740172752896,
[
    ]⟩,
  ⟨202, 36028800240240640,
[
    ]⟩,
  ⟨114, 70781061066752,
[
    ]⟩,
  ⟨178, 141424683167744,
[
    ]⟩,
  ⟨210, 36029621652738048,
[
    ]⟩,
  ⟨226, 36239903251554304,
[
    ]⟩,
  ⟨60, 138247929856,
[
    ]⟩,
  ⟨92, 276225851392,
[
    ]⟩,
  ⟨156, 552181694464,
[
    ]⟩,
  ⟨108, 70370361606144,
[
    ]⟩,
  ⟨172, 140740183719936,
[
    ]⟩,
  ⟨204, 36028800253296640,
[
    ]⟩,
  ⟨116, 70781068378112,
[
    ]⟩,
  ⟨180, 141424694657024,
[
    ]⟩,
  ⟨212, 36029621666316288,
[
    ]⟩,
  ⟨228, 36239903266177024,
[
    ]⟩,
  ⟨120, 70782940086272,
[
    ]⟩,
  ⟨184, 141427635912704,
[
    ]⟩,
  ⟨216, 36029625142345728,
[
    ]⟩,
  ⟨232, 36239907009593344,
[
    ]⟩,
  ⟨240, 36240865324171264,
[
    ]⟩
]

/-- Every placed pattern summary for centre 0 belongs to the audited summary data. -/
theorem patternSummaryChoices0_members :
    patternSummaryChoices0.all (fun choice =>
      choice.patterns.all (fun bucket =>
        bucket.all PatternSummary.memberB) && choice.pairMaskValidB) = true := by
  rfl

end Erdos97Octagon.RawIncidence
