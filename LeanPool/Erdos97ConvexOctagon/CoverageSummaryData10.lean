/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData10
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 80–87 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets10 : Array (List PatternSummary) := #[
  [
    ⟨80, 691500285952⟩,
    ⟨1104, 4785370962067476⟩,
    ⟨1616, 143661052471296⟩
  ],
  [
    ⟨81, 694190866432⟩,
    ⟨1105, 4785385200680984⟩,
    ⟨1361, 13601104864501760⟩,
    ⟨2385, 38957286686⟩,
    ⟨4177, 2594224018553307148⟩,
    ⟨6225, 92646741796114⟩,
    ⟨9809, 2460302415573975318⟩
  ],
  [
    ⟨82, 695795318784⟩,
    ⟨1106, 4785389227212824⟩,
    ⟨3154, 5066867693602842⟩,
    ⟨4178, 2594232836036821012⟩,
    ⟨6226, 92663922581778⟩
  ],
  [
    ⟨83, 698502610944⟩,
    ⟨595, 41096179823460352⟩,
    ⟨851, 6597642824704⟩,
    ⟨1107, 4785389478871064⟩,
    ⟨1363, 13601242303455232⟩,
    ⟨4179, 2594232836037804052⟩
  ],
  [
    ⟨84, 704374678528⟩,
    ⟨596, 41658863502491648⟩,
    ⟨2388, 38957354014⟩,
    ⟨3412, 9650414110664714⟩,
    ⟨4180, 2595975540491969536⟩,
    ⟨4692, 88102670591250⟩
  ],
  [
    ⟨85, 707126099968⟩,
    ⟨597, 41659121200529408⟩,
    ⟨1365, 13603312483958784⟩,
    ⟨2133, 2450169303528563712⟩,
    ⟨6485, 3377726586094878⟩,
    ⟨8533, 14637008314066186⟩
  ],
  [
    ⟨598, 41659138376204288⟩,
    ⟨1622, 145860111892480⟩,
    ⟨2902, 1688849915331854⟩,
    ⟨4182, 2603859038865220608⟩,
    ⟨8790, 6954834357664164110⟩
  ],
  [
    ⟨87, 721565515776⟩,
    ⟨599, 41659138379350016⟩,
    ⟨1623, 145877225177088⟩,
    ⟨2903, 1688849915333646⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets10 : Array (List HardSummary) := #[
  [
    ⟨80, 7181721629143215390⟩,
    ⟨1104, 3865150934157388830⟩,
    ⟨5456, 5563522010341105950⟩,
    ⟨5712, 6139472451290588190⟩
  ],
  [
    ⟨81, 7684084094901300510⟩,
    ⟨1105, 5131230155405552670⟩,
    ⟨5457, 3858276241273708830⟩,
    ⟨5713, 3866713884395627550⟩
  ],
  [
    ⟨82, 6459170576917474590⟩,
    ⟨1106, 3865016222508149790⟩,
    ⟨5458, 2850032866341085470⟩,
    ⟨5714, 3858832585517491230⟩
  ],
  [
    ⟨83, 7176861673663376670⟩,
    ⟨1107, 3721463984385715230⟩,
    ⟨5459, 6176842108091162910⟩,
    ⟨5715, 3284623633027752990⟩
  ],
  [
    ⟨84, 7688143357060066590⟩,
    ⟨1108, 7148773669558840350⟩,
    ⟨5460, 4149308027560976670⟩,
    ⟨5716, 2850165361737262110⟩
  ],
  [
    ⟨85, 7679699108262063390⟩,
    ⟨1109, 5419387134861143070⟩,
    ⟨5461, 3862203551316107550⟩,
    ⟨5717, 2850026269221381150⟩
  ],
  [
    ⟨86, 5164102519270944030⟩,
    ⟨1110, 5131161156755942430⟩,
    ⟨5462, 3285751595105706270⟩,
    ⟨5718, 3281946859336688670⟩
  ],
  [
    ⟨87, 8190575916684422430⟩,
    ⟨1111, 6171492125234457630⟩,
    ⟨5463, 3858839045735112990⟩,
    ⟨5719, 5560768545664066590⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets10_valid :
    patternSummaryBuckets10.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets10)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets10_valid :
    hardSummaryBuckets10.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets10)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
