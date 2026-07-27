/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 64–71 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets08 : Array (List PatternEntry) := #[
  [
    { origin := 64
      mask := 416611852544
      certificate := .sharedThree 1 4 0 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 320
      mask := 189586210816
      certificate := .k4 2 [2, 3, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 832
      mask := 3299122094346
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1088
      mask := 3456866238070784
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2112
      mask := 1441152460587663382
      certificate := .k4 0 [0, 4, 7, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2368
      mask := 25821318174
      certificate := .k4 0 [0, 3, 1, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6464
      mask := 2834705594477568
      certificate := .k4 1 [1, 5, 6, 4, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10560
      mask := 2896025952265109534
      certificate := .k4 0 [0, 2, 3, 7, 5, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 321
      mask := 189787537408
      certificate := .k4 2 [2, 4, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 577
      mask := 38280600134090752
      certificate := .k4 2 [2, 3, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 833
      mask := 3299122096138
      certificate := .k4 0 [0, 3, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1345
      mask := 13583787556364288
      certificate := .k4 1 [1, 5, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1601
      mask := 92687276441600
      certificate := .k4 2 [2, 4, 5, 3] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2113
      mask := 1441152464884138012
      certificate := .k4 0 [0, 2, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3137
      mask := 5066833049765142
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4417
      mask := 6635728150814
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7233
      mask := 13593708930801946
      certificate := .k4 0 [0, 1, 5, 6, 4] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7745
      mask := 97049658853638
      certificate := .k4 0 [0, 1, 2, 3, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9793
      mask := 2450116668748891166
      certificate := .k4 0 [0, 3, 4, 5, 7, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 578
      mask := 38281459315769344
      certificate := .k4 3 [3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1090
      mask := 3659174785384460
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1346
      mask := 13585720298962944
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1602
      mask := 92775593869332
      certificate := .k4 0 [0, 2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2114
      mask := 1441152469179039772
      certificate := .k4 0 [0, 4, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 67
      mask := 420913217536
      certificate := .sharedThree 2 4 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 579
      mask := 38500502916300800
      certificate := .k4 3 [3, 5, 6] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1091
      mask := 3659174785843212
      certificate := .k4 0 [0, 3, 2, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3139
      mask := 5066837344732182
      certificate := .k4 0 [0, 2, 4, 6, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5187
      mask := 6755679788338206
      certificate := .k4 0 [0, 4, 6, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5699
      mask := 37154697022980362
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8771
      mask := 5801762812669790494
      certificate := .k4 0 [0, 1, 2, 6, 7, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 68
      mask := 422550962176
      certificate := .sharedThree 3 4 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 836
      mask := 3448858747154
      certificate := .k4 0 [0, 1, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1348
      mask := 13585995174772736
      certificate := .k4 2 [2, 4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2116
      mask := 1441152486357860380
      certificate := .k4 0 [0, 4, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2628
      mask := 13194729358606
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2884
      mask := 1407376011905038
      certificate := .k4 0 [0, 2, 3, 6, 1] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4164
      mask := 2594218521479752704
      certificate := .k4 1 [1, 2, 3, 7, 5] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 69
      mask := 429496755200
      certificate := .sharedThree 1 4 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1093
      mask := 3659175792476172
      certificate := .k4 0 [0, 3, 6, 2] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1605
      mask := 96930238038016
      certificate := .k4 2 [2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5189
      mask := 6755679788990494
      certificate := .k4 0 [0, 4, 6, 3, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6469
      mask := 3096246224437534
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6725
      mask := 9650413557214222
      certificate := .k4 0 [0, 2, 1, 6, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 70
      mask := 431174451200
      certificate := .sharedThree 3 4 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 838
      mask := 5497560311046
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1094
      mask := 3659175838679052
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1606
      mask := 97038091943960
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4422
      mask := 6648613052702
      certificate := .k4 0 [0, 1, 5, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5702
      mask := 37154718414455058
      certificate := .k4 0 [0, 1, 4, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 71
      mask := 446676625408
      certificate := .sharedThree 1 4 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 327
      mask := 293472829440
      certificate := .k4 2 [2, 3, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 583
      mask := 38843550040899584
      certificate := .k4 1 [1, 6, 3] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 839
      mask := 5497560376582
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1607
      mask := 97072183246872
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6471
      mask := 3096277630992646
      certificate := .k4 0 [0, 1, 6, 3, 4, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8775
      mask := 5802888696483022110
      certificate := .k4 0 [0, 1, 3, 6, 7, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets08 : Array (List HardEntry) := #[
  [
    { origin := 64
      code := 8400275203023187230
      certificate := .residual 779325855812563
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1088
      code := 6459722501419330590
      certificate := .residual 933047028627393
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5440
      code := 4155289489179336990
      certificate := .residual 4346960281807369
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5696
      code := 5442556895958328350
      certificate := .residual 3512536927900454
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 65
      code := 6166495397074709790
      certificate := .residual 4277794395533350
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1089
      code := 4145503412625239070
      certificate := .residual 760926224276401
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5441
      code := 3290611554863735070
      certificate := .residual 4346960281807368
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5697
      code := 3150432631065338910
      certificate := .residual 1755733957075168
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 66
      code := 5157689080778599710
      certificate := .residual 4411569478585472
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1090
      code := 3145018612410117150
      certificate := .residual 3363706943147269
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5442
      code := 6141164599685341470
      certificate := .residual 3795812839861506
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5698
      code := 3150423809437393950
      certificate := .residual 3361557312056832
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 67
      code := 5162203559574908190
      certificate := .residual 4403871017683984
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1091
      code := 3136574491957816350
      certificate := .residual 1231190103736098
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5443
      code := 3867564906395132190
      certificate := .residual 3303231626947842
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5699
      code := 3150417238137431070
      certificate := .residual 2949724398752550
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 68
      code := 5442550540468235550
      certificate := .residual 3919108499073160
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1092
      code := 6163132298061573150
      certificate := .residual 2053936852036272
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5444
      code := 5417224136780079390
      certificate := .residual 271808235357680
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5700
      code := 6141161301150458910
      certificate := .residual 3795692580776327
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 69
      code := 5155446064223366430
      certificate := .residual 3919108499073161
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1093
      code := 5131176447107558430
      certificate := .residual 746442617330594
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5445
      code := 3150353454651859230
      certificate := .residual 263029311194608
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5701
      code := 3866720481465000990
      certificate := .residual 3303111367862663
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 70
      code := 5442549445251575070
      certificate := .residual 3919108499073162
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1094
      code := 2852407912913464350
      certificate := .residual 4317250646643985
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5446
      code := 3858978275153076510
      certificate := .residual 4347907321983234
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5702
      code := 3858839182586864670
      certificate := .residual 277870066581746
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 71
      code := 5155444969006705950
      certificate := .residual 3124964257345960
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1095
      code := 5446477729664363550
      certificate := .residual 316422467528945
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5447
      code := 3862203688218190110
      certificate := .residual 1479389748428370
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5703
      code := 5564643512151106590
      certificate := .residual 1755733957075169
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
