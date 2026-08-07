/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData09
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 72–79 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets09 : Array (List PatternSummary) := #[
  [
    ⟨584, 39406498967191552⟩,
    ⟨840, 5497560441094⟩,
    ⟨1864, 10696049117193478⟩,
    ⟨2120, 1729382822000459802⟩
  ],
  [
    ⟨73, 562649300992⟩,
    ⟨585, 39406499973824512⟩,
    ⟨841, 5497560441862⟩,
    ⟨1097, 4785353782263828⟩,
    ⟨1609, 97084253405184⟩,
    ⟨1865, 10696049117323526⟩,
    ⟨3145, 5066850228715798⟩,
    ⟨6217, 92513601020166⟩
  ],
  [
    ⟨74, 564838531072⟩,
    ⟨586, 39406500036739072⟩,
    ⟨842, 5498114473996⟩,
    ⟨1610, 97174994026520⟩,
    ⟨1866, 10696049121371398⟩,
    ⟨2122, 1729382830623948828⟩,
    ⟨6218, 92515228778508⟩
  ],
  [
    ⟨587, 39406500040409088⟩,
    ⟨2123, 1729382851813572634⟩,
    ⟨2635, 13216423346204⟩
  ],
  [
    ⟨76, 573462020096⟩,
    ⟨1100, 4785362366906642⟩,
    ⟨6220, 92532676034572⟩,
    ⟨6476, 3096551162462494⟩,
    ⟨6732, 9654812157174798⟩,
    ⟨8780, 5810207023318574354⟩
  ],
  [
    ⟨589, 40533238473555968⟩,
    ⟨8781, 5810769973267817746⟩,
    ⟨9805, 2460302402738880782⟩
  ],
  [
    ⟨78, 588419497984⟩,
    ⟨590, 40533259129454592⟩,
    ⟨846, 5639295270932⟩,
    ⟨1102, 4785366667165716⟩,
    ⟨1614, 143640897922048⟩
  ],
  [
    ⟨79, 691489775872⟩,
    ⟨591, 40762057137586176⟩,
    ⟨847, 5652180172820⟩,
    ⟨1103, 4785370961084436⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets09 : Array (List HardSummary) := #[
  [
    ⟨72, 7395849338384559390⟩,
    ⟨1096, 5450925404522572830⟩,
    ⟨5448, 4147065160742396190⟩,
    ⟨5704, 3280828673173939230⟩
  ],
  [
    ⟨73, 7389091843033017630⟩,
    ⟨1097, 5162695045550730270⟩,
    ⟨5449, 3285751732007788830⟩,
    ⟨5705, 3284630093195043870⟩
  ],
  [
    ⟨74, 6166494858022759710⟩,
    ⟨1098, 5131229325436677150⟩,
    ⟨5450, 3858839182637195550⟩,
    ⟨5706, 6141095331459425310⟩
  ],
  [
    ⟨75, 6164251841467526430⟩,
    ⟨1099, 5131238018718919710⟩,
    ⟨5451, 3284630230147457310⟩,
    ⟨5707, 5600374758902522910⟩
  ],
  [
    ⟨76, 6461140884774923550⟩,
    ⟨1100, 8181864353213475870⟩,
    ⟨5452, 6141095468411838750⟩,
    ⟨5708, 6172627260742886430⟩
  ],
  [
    ⟨77, 6171789023942749470⟩,
    ⟨1101, 8184107220032056350⟩,
    ⟨5453, 6425956940936044830⟩,
    ⟨5709, 5164104614118220830⟩
  ],
  [
    ⟨78, 7681264814949346590⟩,
    ⟨1102, 7148782482630405150⟩,
    ⟨5454, 5564643512201437470⟩,
    ⟨5710, 3860651038767375390⟩
  ],
  [
    ⟨79, 7391912954117172510⟩,
    ⟨1103, 5995852285009751070⟩,
    ⟨5455, 6137730962830844190⟩,
    ⟨5711, 2852408767607792670⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets09_valid :
    patternSummaryBuckets09.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets09)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets09_valid :
    hardSummaryBuckets09.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets09)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
