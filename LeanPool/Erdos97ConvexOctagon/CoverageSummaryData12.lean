/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData12
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 96–103 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets12 : Array (List PatternSummary) := #[
  [
    ⟨96, 859006566400⟩,
    ⟨608, 45741882738794496⟩,
    ⟨2912, 1688862750426390⟩,
    ⟨6240, 96930214469898⟩,
    ⟨9824, 2463680403052134678⟩,
    ⟨10080, 7099229921754530830⟩
  ],
  [
    ⟨97, 962072731648⟩,
    ⟨609, 45810052459716608⟩,
    ⟨865, 7696583566342⟩,
    ⟨1377, 14161993233620992⟩,
    ⟨4961, 162872166973464⟩,
    ⟨6241, 96930254356492⟩,
    ⟨10081, 7099238859027825686⟩
  ],
  [
    ⟨98, 962087354368⟩,
    ⟨9826, 2463680420282138906⟩
  ],
  [
    ⟨99, 965830770688⟩,
    ⟨867, 7696583631110⟩,
    ⟨10083, 7100071048686642190⟩
  ],
  [
    ⟨100, 15393162788878⟩,
    ⟨612, 46307031730094080⟩,
    ⟨868, 9896158308618⟩,
    ⟨1380, 14711877901746176⟩,
    ⟨5220, 7047871413100826⟩,
    ⟨8804, 6958485835781054742⟩
  ],
  [
    ⟨101, 24189255811094⟩,
    ⟨613, 46373002427760640⟩,
    ⟨3941, 216172782206746894⟩,
    ⟨4197, 2882453297348881408⟩
  ],
  [
    ⟨102, 28587302322202⟩,
    ⟨614, 46377400470077440⟩,
    ⟨870, 9896175085834⟩,
    ⟨3942, 216172784362553614⟩
  ],
  [
    ⟨103, 30786325577756⟩,
    ⟨359, 603787886592⟩,
    ⟨615, 46377400472174592⟩,
    ⟨871, 9896191861002⟩,
    ⟨1127, 5154931417833472⟩,
    ⟨1383, 14724951783243776⟩,
    ⟨3943, 216172803598221590⟩,
    ⟨4967, 163281783358738⟩,
    ⟨7271, 14434390528508186⟩,
    ⟨10087, 7102323126582682646⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets12 : Array (List HardSummary) := #[
  [
    ⟨96, 6028799718126071070⟩,
    ⟨1120, 2852278069844536350⟩,
    ⟨5472, 6164806280117018910⟩,
    ⟨5728, 3292495849308349470⟩
  ],
  [
    ⟨97, 7679580362667797790⟩,
    ⟨1121, 3713030747648977950⟩,
    ⟨5473, 3867059112994464030⟩,
    ⟨5729, 3858823622709273630⟩
  ],
  [
    ⟨98, 6463393094542306590⟩,
    ⟨1122, 2851717318914370590⟩,
    ⟨5474, 5590605597368705310⟩,
    ⟨5730, 3284614670219535390⟩
  ],
  [
    ⟨99, 6459170970143304990⟩,
    ⟨1123, 5995847784353786910⟩,
    ⟨5475, 3858832585567822110⟩,
    ⟨5731, 2852269131761771550⟩
  ],
  [
    ⟨100, 5159386447612488990⟩,
    ⟨1124, 6136035516895226910⟩,
    ⟨5476, 5560702845549338910⟩,
    ⟨5732, 7148705516495692830⟩
  ],
  [
    ⟨101, 8257725703402302750⟩,
    ⟨1125, 5131169850038184990⟩,
    ⟨5477, 3292858430246150430⟩,
    ⟨5733, 7146462512775029790⟩
  ],
  [
    ⟨102, 7176861793085041950⟩,
    ⟨1126, 5991922527842626590⟩,
    ⟨5478, 6139406481649885470⟩,
    ⟨5734, 7148705379593610270⟩
  ],
  [
    ⟨103, 6451356316910234910⟩,
    ⟨1127, 5130609099108019230⟩,
    ⟨5479, 3284614683104436510⟩,
    ⟨5735, 7146462375872947230⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets12_valid :
    patternSummaryBuckets12.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets12)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets12_valid :
    hardSummaryBuckets12.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets12)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
