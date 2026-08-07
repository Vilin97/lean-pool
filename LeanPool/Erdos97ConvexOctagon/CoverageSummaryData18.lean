/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData18
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 144–151 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets18 : Array (List PatternSummary) := #[
  [
    ⟨144, 3940649673949198⟩,
    ⟨400, 81365504647168⟩,
    ⟨656, 2882303764279590912⟩,
    ⟨4496, 19980188459294⟩,
    ⟨7056, 11821950135512326⟩,
    ⟨7312, 15762891381735436⟩
  ],
  [
    ⟨145, 6192449487634454⟩,
    ⟨401, 83564031377408⟩,
    ⟨657, 2882304486024413184⟩,
    ⟨913, 14294207430668⟩,
    ⟨1169, 6755726198833152⟩,
    ⟨1681, 167727879684096⟩,
    ⟨2193, 3026577977501548544⟩,
    ⟨7313, 15762908789104906⟩
  ],
  [
    ⟨146, 7318349394477082⟩,
    ⟨914, 14294255730700⟩,
    ⟨1682, 167819689852952⟩,
    ⟨4242, 3470253037820313600⟩,
    ⟨7314, 15762908828991500⟩
  ],
  [
    ⟨147, 7881299347898396⟩,
    ⟨403, 83564566151168⟩,
    ⟨659, 2882457693156016128⟩,
    ⟨1171, 6755727004663808⟩,
    ⟨2451, 3320013005078⟩,
    ⟨4243, 3472436674623987712⟩,
    ⟨4499, 19980523413790⟩
  ],
  [
    ⟨148, 9851624187166720⟩,
    ⟨660, 2882471608839045120⟩,
    ⟨1172, 6834737955995648⟩,
    ⟨2452, 3320013005846⟩,
    ⟨2964, 2533275881131022⟩
  ],
  [
    ⟨149, 9851624772075520⟩,
    ⟨917, 18833434804244⟩
  ],
  [
    ⟨150, 9851774508728320⟩,
    ⟨406, 88390434291712⟩,
    ⟨918, 18834253676568⟩,
    ⟨1174, 6835011760160768⟩,
    ⟨1430, 7696631737358⟩
  ],
  [
    ⟨151, 10414574138303744⟩,
    ⟨407, 88409485869056⟩,
    ⟨663, 3026418952310892544⟩,
    ⟨3735, 11348099792371736⟩,
    ⟨6551, 5073464481836032⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets18 : Array (List HardSummary) := #[
  [
    ⟨1168, 3722585502941015070⟩,
    ⟨5520, 8371515816107761950⟩,
    ⟨5776, 6137724364641592350⟩
  ],
  [
    ⟨1169, 7149895188114140190⟩,
    ⟨5521, 4149307735708197150⟩,
    ⟨5777, 5563515412151854110⟩
  ],
  [
    ⟨1170, 5420513034283084830⟩,
    ⟨5522, 3862203259463328030⟩,
    ⟨5778, 5559643761362396190⟩
  ],
  [
    ⟨1171, 5132287056177884190⟩,
    ⟨5523, 4147064731987534110⟩,
    ⟨5779, 5559574762712785950⟩
  ],
  [
    ⟨1172, 4158101616623447070⟩,
    ⟨5524, 3858838753882333470⟩,
    ⟨5780, 3138394620144706590⟩
  ],
  [
    ⟨1173, 4158101496834124830⟩,
    ⟨5525, 3284629801392595230⟩,
    ⟨5781, 5417216306472084510⟩
  ],
  [
    ⟨1174, 4158097115967482910⟩,
    ⟨5526, 6428199515901845790⟩,
    ⟨5782, 3140501816999470110⟩
  ],
  [
    ⟨1175, 7185710407163735070⟩,
    ⟨5527, 6141095039656976670⟩,
    ⟨5783, 3138258813278807070⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets18_valid :
    patternSummaryBuckets18.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets18)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets18_valid :
    hardSummaryBuckets18.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets18)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
