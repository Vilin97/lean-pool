/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData20
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryDataTypes

/-! # Lightweight coverage summaries, buckets 160–167 -/

namespace Erdos97Octagon.RawIncidence

/-- Lightweight monotone-obstruction summaries for this hash-bucket group. -/
def patternSummaryBuckets20 : Array (List PatternSummary) := #[
  [
    ⟨160, 36873221957681152⟩,
    ⟨416, 97068139937792⟩,
    ⟨672, 3170683671261216768⟩,
    ⟨1184, 7037183940624408⟩,
    ⟨8096, 9570170740698136⟩
  ],
  [
    ⟨161, 36873224146911232⟩,
    ⟨417, 97171219152896⟩,
    ⟨1185, 7037184745930776⟩,
    ⟨8097, 9570189742140436⟩
  ],
  [
    ⟨162, 36873784589811712⟩,
    ⟨418, 97205042020352⟩,
    ⟨674, 3458765218206711808⟩,
    ⟨1186, 9576746282279936⟩,
    ⟨1442, 10995720269070⟩,
    ⟨2466, 5497610644494⟩
  ],
  [
    ⟨163, 37017257972334592⟩,
    ⟨419, 97205310455808⟩,
    ⟨675, 3458765238327836672⟩,
    ⟨1187, 9576746284246016⟩,
    ⟨1443, 10995737046030⟩,
    ⟨1955, 14073899159413010⟩,
    ⟨2467, 5497610710030⟩,
    ⟨4003, 723109218424504586⟩,
    ⟨4771, 97178483712266⟩
  ],
  [
    ⟨420, 142936522269696⟩,
    ⟨1444, 10995753821454⟩
  ],
  [
    ⟨165, 37436174133886976⟩,
    ⟨677, 3458927241552986112⟩,
    ⟨8613, 1441172359171615758⟩
  ],
  [
    ⟨166, 37436743133167616⟩,
    ⟨678, 3458931642540752896⟩,
    ⟨1190, 9581145431762944⟩,
    ⟨1702, 1970621189734678⟩,
    ⟨2470, 5497644786702⟩,
    ⟨4262, 4793237378406007046⟩,
    ⟨6566, 5348024647172382⟩
  ],
  [
    ⟨167, 37582406949011456⟩,
    ⟨423, 145135545525248⟩,
    ⟨935, 19954421212160⟩,
    ⟨5031, 2814751177523486⟩,
    ⟨6567, 5348025967395102⟩
  ]
]

/-- Lightweight exact-table summaries for this hash-bucket group. -/
def hardSummaryBuckets20 : Array (List HardSummary) := #[
  [
    ⟨672, 8697238970799187230⟩,
    ⟨1184, 4146624913950796830⟩,
    ⟨5536, 5591722952693571870⟩,
    ⟨5792, 8155327640832107550⟩
  ],
  [
    ⟨673, 8266578970781902110⟩,
    ⟨1185, 4145503412090465310⟩,
    ⟨5537, 7825369142209470750⟩,
    ⟨5793, 6137715128029209630⟩
  ],
  [
    ⟨674, 8697232399499224350⟩,
    ⟨1186, 5420580933421132830⟩,
    ⟨5538, 4149447388533285150⟩,
    ⟨5794, 5563506175539471390⟩
  ],
  [
    ⟨675, 8689072911311136030⟩,
    ⟨1187, 5420513029988183070⟩,
    ⟨5539, 7797307423927230750⟩,
    ⟨5795, 6136026303938749470⟩
  ],
  [
    ⟨676, 6455284343629374750⟩,
    ⟨1188, 3870997140361866270⟩,
    ⟨5540, 3281954687505588510⟩,
    ⟨5796, 8661431066944988190⟩
  ],
  [
    ⟨677, 8688506675741287710⟩,
    ⟨1189, 4158031522740464670⟩,
    ⟨5541, 8659170591530737950⟩,
    ⟨5797, 3726877582424663070⟩
  ],
  [
    ⟨678, 6024071250642167070⟩,
    ⟨1190, 2860165828355189790⟩,
    ⟨5542, 5563591007921168670⟩,
    ⟨5798, 3726822607682135070⟩
  ],
  [
    ⟨679, 6031614906202809630⟩,
    ⟨1191, 8153654609119964190⟩,
    ⟨5543, 4149308163393511710⟩,
    ⟨5799, 8661345306346644510⟩
  ]
]

/-- Every pattern summary in this shard resolves to a valid obstruction entry. -/
theorem patternSummaryBuckets20_valid :
    patternSummaryBuckets20.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB patternBuckets20)) = true := by
  rfl

/-- Every hard summary in this shard resolves to a valid exact-table entry. -/
theorem hardSummaryBuckets20_valid :
    hardSummaryBuckets20.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB hardBuckets20)) = true := by
  rfl

end Erdos97Octagon.RawIncidence
