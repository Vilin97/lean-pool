/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData17
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 136–143 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets17 : Array (List PatternSummary) := #[
  [
    ⟨136, 215507567378432⟩,
    ⟨648, 2594236817460953088⟩,
    ⟨2440, 3298621531150⟩,
    ⟨4488, 19933043895326⟩,
    ⟨5000, 1688850201592094⟩,
    ⟨6024, 21062857924870⟩
  ],
  [
    ⟨137, 216346092634112⟩,
    ⟨393, 76965820391424⟩,
    ⟨649, 2738188573443531776⟩
  ],
  [
    ⟨394, 79166481393664⟩,
    ⟨650, 2738188573451789312⟩,
    ⟨906, 13349632344064⟩,
    ⟨1418, 55835231518⟩
  ],
  [
    ⟨139, 219902338662400⟩,
    ⟨651, 2738188573451887616⟩,
    ⟨907, 13366277439488⟩,
    ⟨1163, 6755452395192320⟩,
    ⟨2443, 3299158270222⟩,
    ⟨4747, 92638157079826⟩,
    ⟨7307, 15762784721592594⟩
  ],
  [
    ⟨140, 220761319014400⟩,
    ⟨396, 79613392846848⟩,
    ⟨652, 2738188573451919360⟩,
    ⟨1164, 6755684284647424⟩,
    ⟨2188, 2898295061584281600⟩,
    ⟨4236, 3458923445398011904⟩,
    ⟨7308, 15762793317859348⟩
  ],
  [
    ⟨397, 81364967778304⟩,
    ⟨2189, 2993135636329791488⟩,
    ⟨4493, 19963009638686⟩,
    ⟨8333, 11331568246268190⟩
  ],
  [
    ⟨142, 228698432208896⟩,
    ⟨398, 81365471094784⟩,
    ⟨654, 2738333708976169984⟩,
    ⟨1166, 6755717570643968⟩,
    ⟨1422, 6597072399630⟩,
    ⟨1678, 167682787770392⟩,
    ⟨2190, 2999759093838643200⟩
  ],
  [
    ⟨143, 228701908238336⟩,
    ⟨911, 14293737668620⟩,
    ⟨1423, 6597072464910⟩,
    ⟨1679, 167716879073304⟩,
    ⟨5263, 9649314666138638⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets17 : Array (List HardSummary) := #[
  [
    ⟨1160, 3871005816665041950⟩,
    ⟨5512, 4145376318603321630⟩,
    ⟨5768, 8659093639675438110⟩
  ],
  [
    ⟨1161, 3726892827612441630⟩,
    ⟨5513, 5591731479260094750⟩,
    ⟨5769, 4149307752636933150⟩
  ],
  [
    ⟨1162, 4158040199043640350⟩,
    ⟨5514, 4147062943704080670⟩,
    ⟨5770, 6137730551004718110⟩
  ],
  [
    ⟨1163, 3866783692266040350⟩,
    ⟨5515, 6137799802251567390⟩,
    ⟨5771, 8686677509794882590⟩
  ],
  [
    ⟨1164, 3722670703213440030⟩,
    ⟨5516, 8401838035908092190⟩,
    ⟨5772, 7608079273227248670⟩
  ],
  [
    ⟨1165, 4153385690690841630⟩,
    ⟨5517, 8661430669641703710⟩,
    ⟨5773, 7676198412520842270⟩
  ],
  [
    ⟨1166, 5420582032932695070⟩,
    ⟨5518, 8230703861408129310⟩,
    ⟨5774, 3717098525771228190⟩
  ],
  [
    ⟨1167, 4153242217308318750⟩,
    ⟨5519, 8229582359547797790⟩,
    ⟨5775, 7581128044744074270⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets17_valid :
    patternSummaryBuckets17.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets17)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets17_valid :
    hardSummaryBuckets17.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets17)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
