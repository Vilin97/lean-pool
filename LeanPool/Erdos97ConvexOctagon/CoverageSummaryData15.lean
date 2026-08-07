/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData15
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 120–127 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets15 : Array (List PatternSummary) := #[
  [
    ⟨120, 146237277863936⟩,
    ⟨632, 1513209474805989396⟩,
    ⟨1144, 5629827295477760⟩,
    ⟨1656, 158484304929792⟩,
    ⟨6008, 20890808492318⟩
  ],
  [
    ⟨121, 146806277144576⟩,
    ⟨633, 1513210046027137044⟩,
    ⟨1145, 5629827298623488⟩,
    ⟨1401, 353502494⟩,
    ⟨6009, 20891593941278⟩
  ],
  [
    ⟨634, 1801439853380894744⟩,
    ⟨1146, 5704420951064576⟩,
    ⟨3962, 432351061796364550⟩,
    ⟨4218, 2896034912622608384⟩,
    ⟨5242, 9570170690494738⟩
  ],
  [
    ⟨123, 150633101983744⟩,
    ⟨635, 1801440439358717976⟩,
    ⟨3195, 5348316620539142⟩,
    ⟨4219, 2898225002077749248⟩
  ],
  [
    ⟨124, 151221503524864⟩,
    ⟨380, 23089747394580⟩,
    ⟨636, 2423430280246198272⟩,
    ⟨892, 12094678245642⟩,
    ⟨1404, 21476412702⟩
  ],
  [
    ⟨381, 23248657973268⟩,
    ⟨637, 2449958197300208640⟩,
    ⟨893, 12094678247434⟩,
    ⟨1405, 21593456670⟩
  ],
  [
    ⟨126, 159429195530240⟩,
    ⟨382, 27488612778008⟩,
    ⟨1150, 5717615090597888⟩,
    ⟨1406, 26089685022⟩,
    ⟨7038, 11350260412588314⟩
  ],
  [
    ⟨127, 159431618723840⟩,
    ⟨383, 27663884353560⟩,
    ⟨895, 12095181563914⟩,
    ⟨1663, 161091338412306⟩,
    ⟨2175, 2882466492194488320⟩,
    ⟨3199, 5629783007364374⟩,
    ⟨4991, 167822105813258⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets15 : Array (List HardSummary) := #[
  [
    ⟨1144, 7149908365073280030⟩,
    ⟨5496, 8686693566026277150⟩,
    ⟨5752, 4149307722823296030⟩
  ],
  [
    ⟨1145, 5996973786585984030⟩,
    ⟨5497, 6455296733343310110⟩,
    ⟨5753, 6137730521191080990⟩
  ],
  [
    ⟨1146, 4158097218777738270⟩,
    ⟨5498, 6168192257098440990⟩,
    ⟨5754, 5442556364409922590⟩
  ],
  [
    ⟨1147, 3870922648666598430⟩,
    ⟨5499, 3860667132533203230⟩,
    ⟨5755, 5417224003053020190⟩
  ],
  [
    ⟨1148, 3148391789498035230⟩,
    ⟨5500, 5997058082598478110⟩,
    ⟨5756, 8686681890678236190⟩
  ],
  [
    ⟨1149, 8154776094017940510⟩,
    ⟨5501, 4147204235209662750⟩,
    ⟨5757, 8657971881140413470⟩
  ],
  [
    ⟨1150, 7149910427160898590⟩,
    ⟨5502, 4149308146414444830⟩,
    ⟨5758, 6164258461135856670⟩
  ],
  [
    ⟨1151, 8192759294463667230⟩,
    ⟨5503, 4147065142693781790⟩,
    ⟨5759, 5587797683297510430⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets15_valid :
    patternSummaryBuckets15.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets15)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets15_valid :
    hardSummaryBuckets15.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets15)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
