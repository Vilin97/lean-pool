/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData23
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 184–191 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets23 : Array (List PatternSummary) := #[
  [
    ⟨440, 153934389837824⟩,
    ⟨696, 4035383598751154176⟩,
    ⟨1208, 9647115026441216⟩,
    ⟨1464, 13194965286940⟩,
    ⟨2744, 21032457085974⟩,
    ⟨4280, 4936789616540910854⟩
  ],
  [
    ⟨697, 4729273289459892224⟩,
    ⟨4281, 4937071092621265920⟩
  ],
  [
    ⟨442, 159034060570624⟩,
    ⟨698, 4755801206516007936⟩,
    ⟨4794, 143640897855750⟩
  ],
  [
    ⟨187, 47287796098400256⟩,
    ⟨443, 159054181695488⟩,
    ⟨8891, 83602348138774⟩
  ],
  [
    ⟨188, 47288517641895936⟩,
    ⟨1212, 9649315152685056⟩,
    ⟨1724, 3096538276446490⟩
  ],
  [
    ⟨701, 4793518853395185664⟩,
    ⟨1213, 9649315656001536⟩,
    ⟨2749, 21033025284122⟩
  ],
  [
    ⟨190, 49539595912609792⟩,
    ⟨702, 4794644756544094208⟩,
    ⟨958, 23111221182484⟩,
    ⟨1214, 9649315689539584⟩,
    ⟨1470, 14294204818702⟩
  ],
  [
    ⟨191, 49539598853865472⟩,
    ⟨447, 161224482398208⟩,
    ⟨703, 4796897386326654976⟩,
    ⟨959, 23111222165524⟩,
    ⟨1215, 9649315689553920⟩,
    ⟨1983, 15762908812673024⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets23 : Array (List HardSummary) := #[
  [
    ⟨696, 3723520191431927070⟩,
    ⟨1208, 3136570097621560350⟩,
    ⟨5560, 4149307752687264030⟩,
    ⟨5816, 8659170047632204830⟩
  ],
  [
    ⟨697, 3718236806367110430⟩,
    ⟨1209, 2849465621376691230⟩,
    ⟨5561, 3862203276442394910⟩,
    ⟨5817, 8659093382465971230⟩
  ],
  [
    ⟨698, 8697799490038621470⟩,
    ⟨1210, 6172613626560015390⟩,
    ⟨5562, 4147064748966600990⟩,
    ⟨5818, 6460859423606891550⟩
  ],
  [
    ⟨699, 7688164141790618910⟩,
    ⟨1211, 6171492124699683870⟩,
    ⟨5563, 3858838770861400350⟩,
    ⟨5819, 7609207234720097310⟩
  ],
  [
    ⟨700, 8696888256942531870⟩,
    ⟨1212, 3858394537765923870⟩,
    ⟨5564, 3284629818371662110⟩,
    ⟨5820, 3870997164017771550⟩
  ],
  [
    ⟨701, 8693858840599553310⟩,
    ⟨1213, 2857909737550801950⟩,
    ⟨5565, 6428199532880912670⟩,
    ⟨5821, 3294536386179425310⟩
  ],
  [
    ⟨702, 8693789841949943070⟩,
    ⟨1214, 2849465617098501150⟩,
    ⟨5566, 6141095056636043550⟩,
    ⟨5822, 2862190847721661470⟩
  ],
  [
    ⟨703, 3141767489127671070⟩,
    ⟨1215, 2860161430275517470⟩,
    ⟨5567, 6425956529160249630⟩,
    ⟨5823, 3285751593451054110⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets23_valid :
    patternSummaryBuckets23.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets23)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets23_valid :
    hardSummaryBuckets23.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets23)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
