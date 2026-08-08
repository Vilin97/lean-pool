/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData08
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 64–71 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets08 : Array (List PatternSummary) := #[
  [
    ⟨64, 416611852544⟩,
    ⟨832, 3299122094346⟩,
    ⟨1088, 3456866238070784⟩,
    ⟨6464, 2834705594477568⟩
  ],
  [
    ⟨577, 38280600134090752⟩,
    ⟨833, 3299122096138⟩,
    ⟨1345, 13583787556364288⟩,
    ⟨7233, 13593708930801946⟩,
    ⟨7745, 97049658853638⟩
  ],
  [
    ⟨578, 38281459315769344⟩,
    ⟨1602, 92775593869332⟩,
    ⟨2114, 1441152469179039772⟩
  ],
  [
    ⟨67, 420913217536⟩,
    ⟨579, 38500502916300800⟩,
    ⟨1091, 3659174785843212⟩,
    ⟨5187, 6755679788338206⟩,
    ⟨5699, 37154697022980362⟩,
    ⟨8771, 5801762812669790494⟩
  ],
  [
    ⟨68, 422550962176⟩,
    ⟨836, 3448858747154⟩,
    ⟨2884, 1407376011905038⟩,
    ⟨4164, 2594218521479752704⟩
  ],
  [
    ⟨69, 429496755200⟩,
    ⟨1093, 3659175792476172⟩,
    ⟨1605, 96930238038016⟩,
    ⟨6469, 3096246224437534⟩
  ],
  [
    ⟨838, 5497560311046⟩,
    ⟨1606, 97038091943960⟩,
    ⟨5702, 37154718414455058⟩
  ],
  [
    ⟨71, 446676625408⟩,
    ⟨327, 293472829440⟩,
    ⟨583, 38843550040899584⟩,
    ⟨839, 5497560376582⟩,
    ⟨8775, 5802888696483022110⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets08 : Array (List HardSummary) := #[
  [
    ⟨64, 8400275203023187230⟩,
    ⟨1088, 6459722501419330590⟩,
    ⟨5440, 4155289489179336990⟩,
    ⟨5696, 5442556895958328350⟩
  ],
  [
    ⟨65, 6166495397074709790⟩,
    ⟨1089, 4145503412625239070⟩,
    ⟨5441, 3290611554863735070⟩,
    ⟨5697, 3150432631065338910⟩
  ],
  [
    ⟨66, 5157689080778599710⟩,
    ⟨1090, 3145018612410117150⟩,
    ⟨5442, 6141164599685341470⟩,
    ⟨5698, 3150423809437393950⟩
  ],
  [
    ⟨67, 5162203559574908190⟩,
    ⟨1091, 3136574491957816350⟩,
    ⟨5443, 3867564906395132190⟩,
    ⟨5699, 3150417238137431070⟩
  ],
  [
    ⟨68, 5442550540468235550⟩,
    ⟨1092, 6163132298061573150⟩,
    ⟨5444, 5417224136780079390⟩,
    ⟨5700, 6141161301150458910⟩
  ],
  [
    ⟨69, 5155446064223366430⟩,
    ⟨1093, 5131176447107558430⟩,
    ⟨5445, 3150353454651859230⟩,
    ⟨5701, 3866720481465000990⟩
  ],
  [
    ⟨70, 5442549445251575070⟩,
    ⟨1094, 2852407912913464350⟩,
    ⟨5446, 3858978275153076510⟩,
    ⟨5702, 3858839182586864670⟩
  ],
  [
    ⟨71, 5155444969006705950⟩,
    ⟨1095, 5446477729664363550⟩,
    ⟨5447, 3862203688218190110⟩,
    ⟨5703, 5564643512151106590⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets08_valid :
    patternSummaryBuckets08.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets08)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets08_valid :
    hardSummaryBuckets08.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets08)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
