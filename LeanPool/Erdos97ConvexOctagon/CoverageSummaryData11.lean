/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData11
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 88–95 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets11 : Array (List PatternSummary) := #[
  [
    ⟨88, 828928737536⟩,
    ⟨600, 42784784065232896⟩,
    ⟨1368, 13607729046224896⟩,
    ⟨2136, 2450173701575073792⟩
  ],
  [
    ⟨89, 828941336576⟩,
    ⟨601, 42785024583401472⟩,
    ⟨1369, 13607729314660352⟩,
    ⟨1625, 147334566748422⟩,
    ⟨2137, 2450178101259329536⟩,
    ⟨4441, 10995990274334⟩
  ],
  [
    ⟨602, 42785057869398016⟩,
    ⟨2138, 2450187316614979584⟩,
    ⟨9818, 2461428303765143822⟩
  ],
  [
    ⟨91, 833236369408⟩,
    ⟨603, 42785058674704384⟩,
    ⟨1115, 5066850233762816⟩,
    ⟨1371, 13607866753613824⟩,
    ⟨2907, 1688849948429326⟩,
    ⟨10075, 5810282889614484502⟩,
    ⟨10587, 3468546323312626718⟩
  ],
  [
    ⟨92, 836478435328⟩,
    ⟨604, 45249301529550848⟩,
    ⟨8796, 6955955860610753806⟩,
    ⟨9820, 2461428316851175706⟩
  ],
  [
    ⟨93, 841813640192⟩,
    ⟨605, 45251500567429120⟩,
    ⟨1629, 147337318638592⟩
  ],
  [
    ⟨94, 845101924352⟩,
    ⟨606, 45255902357356544⟩,
    ⟨862, 7696581599494⟩,
    ⟨2654, 14294207046670⟩
  ],
  [
    ⟨607, 45265656764956672⟩,
    ⟨863, 7696581600262⟩,
    ⟨1119, 5066868750567424⟩,
    ⟨1375, 14161855794667520⟩,
    ⟨1631, 148038942336000⟩,
    ⟨6239, 96912807100428⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets11 : Array (List HardSummary) := #[
  [
    ⟨88, 6028848096049900830⟩,
    ⟨1112, 3858394538300697630⟩,
    ⟨5464, 3284630093245374750⟩,
    ⟨5720, 6137154788874839070⟩
  ],
  [
    ⟨89, 7676196318743112990⟩,
    ⟨1113, 3857273036440366110⟩,
    ⟨5465, 6428199807754625310⟩,
    ⟨5721, 5560702832664437790⟩
  ],
  [
    ⟨90, 6027669437570100510⟩,
    ⟨1114, 5131229055910702110⟩,
    ⟨5466, 6141095331509756190⟩,
    ⟨5722, 5128357294206673950⟩
  ],
  [
    ⟨91, 7391345605866958110⟩,
    ⟨1115, 5131161152477752350⟩,
    ⟨5467, 5564643375299354910⟩,
    ⟨5723, 6139406481599554590⟩
  ],
  [
    ⟨92, 6026825012690300190⟩,
    ⟨1116, 5131238848687795230⟩,
    ⟨5468, 6137730825928761630⟩,
    ⟨5724, 5562954525389153310⟩
  ],
  [
    ⟨93, 7175172823803505950⟩,
    ⟨1117, 5419400209010027550⟩,
    ⟨5469, 5563521873439023390⟩,
    ⟨5725, 5166346941884851230⟩
  ],
  [
    ⟨94, 6024064411992403230⟩,
    ⟨1118, 3716956004160138270⟩,
    ⟨5470, 6141093141076435230⟩,
    ⟨5726, 5130600165303444510⟩
  ],
  [
    ⟨95, 6454720852555541790⟩,
    ⟨1119, 3857143736701578270⟩,
    ⟨5471, 5132289015213646110⟩,
    ⟨5727, 5598408814949360670⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets11_valid :
    patternSummaryBuckets11.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets11)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets11_valid :
    hardSummaryBuckets11.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets11)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
