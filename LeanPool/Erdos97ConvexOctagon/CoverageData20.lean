/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 160–167 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets20 : Array (List PatternEntry) := #[
  [
    { origin := 160
      mask := 36873221957681152
      certificate := .sharedThree 2 6 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 416
      mask := 97068139937792
      certificate := .k4 3 [3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 672
      mask := 3170683671261216768
      certificate := .k4 2 [2, 7, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1184
      mask := 7037183940624408
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2464
      mask := 3479208730906
      certificate := .k4 0 [0, 1, 3, 5, 4] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8096
      mask := 9570170740698136
      certificate := .k4 0 [0, 3, 4, 1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 161
      mask := 36873224146911232
      certificate := .sharedThree 3 6 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 417
      mask := 97171219152896
      certificate := .k4 3 [3, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1185
      mask := 7037184745930776
      certificate := .k4 0 [0, 3, 6, 4] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2209
      mask := 3458980980179599360
      certificate := .k4 2 [2, 5, 7, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8097
      mask := 9570189742140436
      certificate := .k4 0 [0, 2, 4, 1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 162
      mask := 36873784589811712
      certificate := .sharedThree 4 6 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 418
      mask := 97205042020352
      certificate := .k4 3 [3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 674
      mask := 3458765218206711808
      certificate := .k4 2 [2, 4, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1186
      mask := 9576746282279936
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1442
      mask := 10995720269070
      certificate := .k4 0 [0, 1, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2466
      mask := 5497610644494
      certificate := .k4 0 [0, 2, 3, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 163
      mask := 37017257972334592
      certificate := .sharedThree 5 6 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 419
      mask := 97205310455808
      certificate := .k4 3 [3, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 675
      mask := 3458765238327836672
      certificate := .k4 3 [3, 4, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1187
      mask := 9576746284246016
      certificate := .k4 1 [1, 5, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1443
      mask := 10995737046030
      certificate := .k4 0 [0, 3, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1955
      mask := 14073899159413010
      certificate := .k4 0 [0, 1, 4, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2467
      mask := 5497610710030
      certificate := .k4 0 [0, 3, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4003
      mask := 723109218424504586
      certificate := .k4 0 [0, 1, 7, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4771
      mask := 97178483712266
      certificate := .k4 0 [0, 1, 3, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 420
      mask := 142936522269696
      certificate := .k4 1 [1, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1444
      mask := 10995753821454
      certificate := .k4 0 [0, 1, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5540
      mask := 12738941803307278
      certificate := .k4 0 [0, 1, 3, 5, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 165
      mask := 37436174133886976
      certificate := .sharedThree 3 6 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 677
      mask := 3458927241552986112
      certificate := .k4 2 [2, 5, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2469
      mask := 5497644785934
      certificate := .k4 0 [0, 1, 3, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3237
      mask := 5656078474805248
      certificate := .k4 2 [2, 4, 6, 5, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6053
      mask := 22170623478814
      certificate := .k4 0 [0, 2, 1, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8613
      mask := 1441172359171615758
      certificate := .k4 0 [0, 2, 7, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 166
      mask := 37436743133167616
      certificate := .sharedThree 4 6 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 678
      mask := 3458931642540752896
      certificate := .k4 3 [3, 5, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1190
      mask := 9581145431762944
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1702
      mask := 1970621189734678
      certificate := .k4 0 [0, 1, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2470
      mask := 5497644786702
      certificate := .k4 0 [0, 3, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2726
      mask := 19954418262294
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4262
      mask := 4793237378406007046
      certificate := .k4 0 [0, 1, 2, 7, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4518
      mask := 22162336055310
      certificate := .k4 0 [0, 2, 5, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6566
      mask := 5348024647172382
      certificate := .k4 0 [0, 1, 3, 6, 2] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 167
      mask := 37582406949011456
      certificate := .sharedThree 5 6 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 423
      mask := 145135545525248
      certificate := .k4 1 [1, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 935
      mask := 19954421212160
      certificate := .k4 1 [1, 5, 4, 2] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1191
      mask := 9581145935079424
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4263
      mask := 4793237378406007814
      certificate := .k4 0 [0, 2, 1, 7, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5031
      mask := 2814751177523486
      certificate := .k4 0 [0, 1, 2, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6567
      mask := 5348025967395102
      certificate := .k4 0 [0, 1, 2, 6, 3] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6823
      mask := 10205692704203030
      certificate := .k4 0 [0, 1, 5, 6, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets20 : Array (List HardEntry) := #[
  [
    { origin := 672
      code := 8697238970799187230
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 6, 5, 7] 1 0 2 5 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1184
      code := 4146624913950796830
      certificate := .residual 1003398607615937
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5536
      code := 5591722952693571870
      certificate := .residual 3915951698029065
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5792
      code := 8155327640832107550
      certificate := .residual 4325651870951826
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 673
      code := 8266578970781902110
      certificate := .residual 3918852948510086
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1185
      code := 4145503412090465310
      certificate := .residual 760926224276404
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5537
      code := 7825369142209470750
      certificate := .residual 269647263941104
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5793
      code := 6137715128029209630
      certificate := .residual 4176650863957269
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 674
      code := 8697232399499224350
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 2 1 5 6 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1186
      code := 5420580933421132830
      certificate := .residual 3917860810886405
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5538
      code := 4149447388533285150
      certificate := .residual 4349966758980866
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5794
      code := 5563506175539471390
      certificate := .residual 4171148998268449
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 675
      code := 8689072911311136030
      certificate := .residual 1201555500719955
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1187
      code := 5420513029988183070
      certificate := .residual 1231054804926242
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5539
      code := 7797307423927230750
      certificate := .residual 3364804307463426
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5795
      code := 6136026303938749470
      certificate := .residual 2470976698174545
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 676
      code := 6455284343629374750
      certificate := .residual 4278889880649894
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1188
      code := 3870997140361866270
      certificate := .residual 4347907321983243
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5540
      code := 3281954687505588510
      certificate := .residual 279504846112240
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5796
      code := 8661431066944988190
      certificate := .residual 3349285244307860
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 677
      code := 8688506675741287710
      certificate := .hubPentagon 0 [0, 1, 2, 4, 5, 6, 3, 7] 0 1 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1189
      code := 4158031522740464670
      certificate := .residual 3546628365007392
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5541
      code := 8659170591530737950
      certificate := .residual 261946920715760
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5797
      code := 3726877582424663070
      certificate := .residual 3323309281970835
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 678
      code := 6024071250642167070
      certificate := .residual 4403974365339923
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1190
      code := 2860165828355189790
      certificate := .residual 1261222955753265
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5542
      code := 5563591007921168670
      certificate := .residual 3793753402863874
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5798
      code := 3726822607682135070
      certificate := .residual 3280015953037716
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 679
      code := 6031614906202809630
      certificate := .residual 4403974365339924
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1191
      code := 8153654609119964190
      certificate := .residual 1252428892774196
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5543
      code := 4149308163393511710
      certificate := .residual 4231787769637570
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5799
      code := 8661345306346644510
      certificate := .residual 3254039990700691
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
