/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData19
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 152–159 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets19 : Array (List PatternSummary) := #[
  [
    ⟨664, 3026418952310923264⟩,
    ⟨920, 18842021536018⟩,
    ⟨1176, 6843534049017856⟩,
    ⟨1688, 1688849865067534⟩,
    ⟨4248, 3474677368994398208⟩
  ],
  [
    ⟨665, 3026561888822493184⟩,
    ⟨1433, 7697202159886⟩
  ],
  [
    ⟨154, 11540474045147392⟩,
    ⟨922, 18846319706132⟩,
    ⟨1178, 6843807853182976⟩
  ],
  [
    ⟨155, 11540474047823872⟩,
    ⟨411, 90580860297216⟩,
    ⟨667, 3170534138283819008⟩,
    ⟨923, 18850613624852⟩,
    ⟨4251, 4792392955699284992⟩,
    ⟨6555, 5077846217223168⟩,
    ⟨8603, 1297037268292895006⟩
  ],
  [
    ⟨156, 11540650138796032⟩,
    ⟨412, 92651041849344⟩,
    ⟨924, 18850614607892⟩,
    ⟨2204, 3458919167006605312⟩,
    ⟨4252, 4792392955732708352⟩
  ],
  [
    ⟨413, 92771300933632⟩,
    ⟨669, 3170534140422914048⟩,
    ⟨925, 18864318447640⟩,
    ⟨1181, 7036914414649368⟩,
    ⟨1437, 7855495192854⟩,
    ⟨3997, 720585838701879562⟩,
    ⟨9885, 2892085019122682894⟩
  ],
  [
    ⟨158, 13792273862033408⟩,
    ⟨414, 92788478705664⟩,
    ⟨926, 18868344979480⟩,
    ⟨1182, 7037153875853336⟩,
    ⟨2718, 19937239311638⟩
  ],
  [
    ⟨159, 13792274680905728⟩,
    ⟨415, 92788479754240⟩,
    ⟨671, 3170679275955159040⟩,
    ⟨927, 18868596637720⟩,
    ⟨1183, 7037154932817944⟩,
    ⟨1695, 1970324887325710⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets19 : Array (List HardSummary) := #[
  [
    ⟨1176, 5456328253332679710⟩,
    ⟨5528, 6425956512181182750⟩,
    ⟨5784, 3136569989188346910⟩
  ],
  [
    ⟨1177, 2862191363117706270⟩,
    ⟨5529, 6137730534075982110⟩,
    ⟨5785, 5995919938294440990⟩
  ],
  [
    ⟨1178, 3145366082195450910⟩,
    ⟨5530, 5563521581586243870⟩,
    ⟨5786, 6136095572114334750⟩
  ],
  [
    ⟨1179, 8189454161454197790⟩,
    ⟨5531, 6136041709985521950⟩,
    ⟨5787, 3716962188409758750⟩
  ],
  [
    ⟨1180, 6172914892527528990⟩,
    ⟨5532, 5993615346033680670⟩,
    ⟨5788, 3714719184689095710⟩
  ],
  [
    ⟨1181, 7185587263740472350⟩,
    ⟨5533, 8230695039780184350⟩,
    ⟨5789, 8252649692777210910⟩
  ],
  [
    ⟨1182, 7176861672606428190⟩,
    ⟨5534, 6168183730531918110⟩,
    ⟨5790, 3713021538970690590⟩
  ],
  [
    ⟨1183, 6460844002744888350⟩,
    ⟨5535, 6453036381428179230⟩,
    ⟨5791, 8182278732413199390⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets19_valid :
    patternSummaryBuckets19.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets19)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets19_valid :
    hardSummaryBuckets19.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets19)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
