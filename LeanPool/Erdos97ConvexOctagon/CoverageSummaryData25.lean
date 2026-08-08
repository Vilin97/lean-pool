/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData25
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 200–207 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets25 : Array (List PatternSummary) := #[
  [
    ⟨200, 2666130979403343104⟩,
    ⟨712, 5044031582667686912⟩,
    ⟨968, 26535146825728⟩,
    ⟨1736, 3659175787775246⟩,
    ⟨1992, 36592588799755264⟩,
    ⟨4296, 4938478466485452812⟩
  ],
  [
    ⟨713, 5044031582667718656⟩,
    ⟨4041, 936748724665877518⟩
  ],
  [
    ⟨714, 5080623329640054784⟩,
    ⟨970, 26568969693184⟩,
    ⟨2762, 22136264656150⟩,
    ⟨4554, 27642410641678⟩
  ],
  [
    ⟨459, 918092209217792⟩,
    ⟨715, 5081186279580812288⟩,
    ⟨1739, 3659196177842204⟩,
    ⟨4299, 4940730287689629716⟩,
    ⟨4555, 72567824149516⟩
  ],
  [
    ⟨204, 2954361355555055872⟩,
    ⟨1228, 10139696235701248⟩,
    ⟨1740, 3659214761230364⟩,
    ⟨9932, 3469392947265430550⟩,
    ⟨10444, 1442841315032714254⟩
  ],
  [
    ⟨205, 2954361355557732352⟩,
    ⟨717, 5188146774032252928⟩,
    ⟨973, 26577595793408⟩,
    ⟨1485, 19954418066710⟩,
    ⟨2253, 4938759941378296832⟩,
    ⟨6605, 5642995167264768⟩
  ],
  [
    ⟨206, 2954361531648704512⟩,
    ⟨718, 5188147633213931520⟩,
    ⟨4558, 72569395047436⟩,
    ⟨6606, 5643012146331648⟩,
    ⟨8654, 2603854640815098894⟩,
    ⟨10702, 5228698273575021824⟩
  ],
  [
    ⟨207, 2965901829600182272⟩,
    ⟨463, 1483241192226816⟩,
    ⟨4303, 4946150858537591808⟩,
    ⟨10959, 5224741857310893078⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets25 : Array (List HardSummary) := #[
  [
    ⟨712, 6022942919503668510⟩,
    ⟨1224, 6139399885039365150⟩,
    ⟨5576, 7653108657063256350⟩,
    ⟨5832, 6028513859379717150⟩
  ],
  [
    ⟨713, 5446490950458696990⟩,
    ⟨1225, 5995847646916930590⟩,
    ⟨5577, 3716962188460089630⟩,
    ⟨5833, 7607518384860226590⟩
  ],
  [
    ⟨714, 3140087327753790750⟩,
    ⟨1226, 5131169712601328670⟩,
    ⟨5578, 8227326153098584350⟩,
    ⟨5834, 7580567156377052190⟩
  ],
  [
    ⟨715, 6030757277541623070⟩,
    ⟨1227, 5991922390405770270⟩,
    ⟨5579, 6137715140914110750⟩,
    ⟨5835, 7653172303111971870⟩
  ],
  [
    ⟨716, 6028514273820960030⟩,
    ⟨1228, 5130608961671162910⟩,
    ⟨5580, 8661985203826909470⟩,
    ⟨5836, 3860514699801584670⟩
  ],
  [
    ⟨717, 3714855935957034270⟩,
    ⟨1229, 2860161297651624990⟩,
    ⟨5581, 6176848712146018590⟩,
    ⟨5837, 3284062743591183390⟩
  ],
  [
    ⟨718, 6020691094155060510⟩,
    ⟨1230, 2851717177199324190⟩,
    ⟨5582, 4157549565685981470⟩,
    ⟨5838, 3292772941797319710⟩
  ],
  [
    ⟨719, 6029347686639494430⟩,
    ⟨1231, 5995847642638740510⟩,
    ⟨5583, 3869323587580780830⟩,
    ⟨5839, 3284047350663275550⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets25_valid :
    patternSummaryBuckets25.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets25)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets25_valid :
    hardSummaryBuckets25.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets25)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
