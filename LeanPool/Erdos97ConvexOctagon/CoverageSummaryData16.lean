/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData16
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 128–135 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets16 : Array (List PatternSummary) := #[
  [
    ⟨128, 212205744210176⟩,
    ⟨384, 72567773881344⟩,
    ⟨1152, 5717889964310528⟩,
    ⟨1408, 30115105822⟩,
    ⟨3968, 433752939123884294⟩,
    ⟨4224, 3458915838688493592⟩
  ],
  [
    ⟨129, 212205756809216⟩,
    ⟨385, 72569411627008⟩,
    ⟨897, 12095198339338⟩,
    ⟨1409, 30149312542⟩,
    ⟨2177, 2882514871541327872⟩
  ],
  [
    ⟨130, 212208982163456⟩,
    ⟨642, 2450119421771907072⟩,
    ⟨1410, 38957416478⟩,
    ⟨3202, 5629787302266134⟩,
    ⟨6530, 5066828804670494⟩,
    ⟨8578, 720575964103475486⟩
  ],
  [
    ⟨131, 213034672848896⟩,
    ⟨387, 74766797136896⟩,
    ⟨643, 2594073385376064512⟩,
    ⟨1155, 5910995991003156⟩,
    ⟨1411, 38990253342⟩,
    ⟨4739, 92500715070484⟩
  ],
  [
    ⟨132, 213305268502528⟩,
    ⟨900, 13194712720384⟩,
    ⟨1156, 5911253684912148⟩,
    ⟨2180, 2882517070531028992⟩,
    ⟨4484, 19932943821854⟩,
    ⟨7300, 14991020705997846⟩,
    ⟨7812, 158471503389720⟩
  ],
  [
    ⟨133, 213308510568448⟩,
    ⟨1157, 5911253689040916⟩,
    ⟨1413, 43236130846⟩,
    ⟨1669, 162885101158400⟩,
    ⟨4485, 19932943887390⟩,
    ⟨10117, 8108030482475655446⟩
  ],
  [
    ⟨134, 214138479443968⟩,
    ⟨390, 76965818295296⟩,
    ⟨646, 2594220719923569664⟩,
    ⟨1414, 47244839966⟩,
    ⟨1670, 163281783291924⟩
  ],
  [
    ⟨135, 215504279094272⟩,
    ⟨391, 76965820261376⟩,
    ⟨647, 2594227319744757760⟩,
    ⟨1159, 5911266572959764⟩,
    ⟨1671, 163298962112532⟩,
    ⟨4487, 19933027118110⟩,
    ⟨10119, 8108384237456991506⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets16 : Array (List HardSummary) := #[
  [
    ⟨1152, 4158110292926622750⟩,
    ⟨5504, 3285751713959174430⟩,
    ⟨5760, 5155452144839746590⟩
  ],
  [
    ⟨1153, 3140508291630197790⟩,
    ⟨5505, 3858839164588581150⟩,
    ⟨5761, 4149444089998402590⟩
  ],
  [
    ⟨1154, 3139947540700032030⟩,
    ⟨5506, 3284630212098842910⟩,
    ⟨5762, 7581134641813447710⟩
  ],
  [
    ⟨1155, 2851717181728189470⟩,
    ⟨5507, 6428199926608093470⟩,
    ⟨5763, 4147065159622517790⟩
  ],
  [
    ⟨1156, 5995847647167605790⟩,
    ⟨5508, 6425956922887430430⟩,
    ⟨5764, 5563522009221227550⟩
  ],
  [
    ⟨1157, 2862200039420881950⟩,
    ⟨5509, 5564643494152823070⟩,
    ⟨5765, 5128993644064465950⟩
  ],
  [
    ⟨1158, 3870992742516157470⟩,
    ⟨5510, 6137730944782229790⟩,
    ⟨5766, 8659109032603345950⟩
  ],
  [
    ⟨1159, 6175166435649285150⟩,
    ⟨5511, 5563521992292491550⟩,
    ⟨5767, 8659100210975400990⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets16_valid :
    patternSummaryBuckets16.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets16)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets16_valid :
    hardSummaryBuckets16.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets16)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
