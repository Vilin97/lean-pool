/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 128–135 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets16 : Array (List PatternEntry) := #[
  [
    { origin := 128
      mask := 212205744210176
      certificate := .sharedThree 1 5 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 384
      mask := 72567773881344
      certificate := .k4 1 [1, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 640
      mask := 2450105531858288640
      certificate := .k4 2 [2, 5, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1152
      mask := 5717889964310528
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1408
      mask := 30115105822
      certificate := .k4 0 [0, 3, 4, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3968
      mask := 433752939123884294
      certificate := .k4 0 [0, 1, 7, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4224
      mask := 3458915838688493592
      certificate := .k4 0 [0, 3, 4, 7, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5504
      mask := 11898967217405952
      certificate := .k4 2 [2, 4, 5, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 129
      mask := 212205756809216
      certificate := .sharedThree 2 5 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 385
      mask := 72569411627008
      certificate := .k4 1 [1, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 897
      mask := 12095198339338
      certificate := .k4 0 [0, 1, 5, 3] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1153
      mask := 5717889967456256
      certificate := .k4 2 [2, 6, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1409
      mask := 30149312542
      certificate := .k4 0 [0, 3, 4, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1921
      mask := 12384900118897664
      certificate := .k4 1 [1, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2177
      mask := 2882514871541327872
      certificate := .k4 1 [1, 3, 7, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5249
      mask := 9644916001557518
      certificate := .k4 0 [0, 2, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 130
      mask := 212208982163456
      certificate := .sharedThree 3 5 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 642
      mask := 2450119421771907072
      certificate := .k4 4 [4, 5, 7] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1154
      mask := 5910995990020116
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1410
      mask := 38957416478
      certificate := .k4 0 [0, 2, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3202
      mask := 5629787302266134
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4994
      mask := 167830723103744
      certificate := .k4 1 [1, 2, 3, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6530
      mask := 5066828804670494
      certificate := .k4 0 [0, 3, 4, 6, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8578
      mask := 720575964103475486
      certificate := .k4 0 [0, 1, 4, 7, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 131
      mask := 213034672848896
      certificate := .sharedThree 4 5 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 387
      mask := 74766797136896
      certificate := .k4 1 [1, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 643
      mask := 2594073385376064512
      certificate := .k4 1 [1, 2, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1155
      mask := 5910995991003156
      certificate := .k4 0 [0, 4, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1411
      mask := 38990253342
      certificate := .k4 0 [0, 1, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4739
      mask := 92500715070484
      certificate := .k4 0 [0, 2, 4, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8579
      mask := 720575968599703838
      certificate := .k4 0 [0, 1, 2, 7, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 132
      mask := 213305268502528
      certificate := .sharedThree 2 5 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 900
      mask := 13194712720384
      certificate := .k4 1 [1, 2, 5, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1156
      mask := 5911253684912148
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1924
      mask := 12385346529001472
      certificate := .k4 2 [2, 3, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2180
      mask := 2882517070531028992
      certificate := .k4 1 [1, 5, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4484
      mask := 19932943821854
      certificate := .k4 0 [0, 2, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4996
      mask := 1688850151260446
      certificate := .k4 0 [0, 1, 3, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7300
      mask := 14991020705997846
      certificate := .k4 0 [0, 4, 6, 5, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7812
      mask := 158471503389720
      certificate := .k4 0 [0, 3, 4, 2, 5, 1] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 133
      mask := 213308510568448
      certificate := .sharedThree 3 5 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 645
      mask := 2594074089751576576
      certificate := .k4 2 [2, 4, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1157
      mask := 5911253689040916
      certificate := .k4 0 [0, 4, 6, 2] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1413
      mask := 43236130846
      certificate := .k4 0 [0, 2, 3, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1669
      mask := 162885101158400
      certificate := .k4 2 [2, 3, 4, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4485
      mask := 19932943887390
      certificate := .k4 0 [0, 4, 5, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10117
      mask := 8108030482475655446
      certificate := .k4 0 [0, 1, 5, 7, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 134
      mask := 214138479443968
      certificate := .sharedThree 4 5 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 390
      mask := 76965818295296
      certificate := .k4 1 [1, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 646
      mask := 2594220719923569664
      certificate := .k4 1 [1, 5, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1158
      mask := 5911266569814036
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1414
      mask := 47244839966
      certificate := .k4 0 [0, 2, 4, 1] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1670
      mask := 163281783291924
      certificate := .k4 0 [0, 2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 135
      mask := 215504279094272
      certificate := .sharedThree 1 5 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 391
      mask := 76965820261376
      certificate := .k4 1 [1, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 647
      mask := 2594227319744757760
      certificate := .k4 3 [3, 5, 7] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1159
      mask := 5911266572959764
      certificate := .k4 0 [0, 2, 6, 4] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1415
      mask := 47345893406
      certificate := .k4 0 [0, 2, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1671
      mask := 163298962112532
      certificate := .k4 0 [0, 2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3207
      mask := 5629800186184982
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4487
      mask := 19933027118110
      certificate := .k4 0 [0, 3, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10119
      mask := 8108384237456991506
      certificate := .k4 0 [0, 1, 4, 7, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets16 : Array (List HardEntry) := #[
  [
    { origin := 1152
      code := 4158110292926622750
      certificate := .residual 3363586684062080
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5504
      code := 3285751713959174430
      certificate := .residual 2675625636094546
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5760
      code := 5155452144839746590
      certificate := .residual 4066690847019814
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1153
      code := 3140508291630197790
      certificate := .residual 2924577021592353
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5505
      code := 3858839164588581150
      certificate := .residual 1620245215911506
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5761
      code := 4149444089998402590
      certificate := .residual 4349846499895687
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1154
      code := 3139947540700032030
      certificate := .residual 2927914223747861
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5506
      code := 3284630212098842910
      certificate := .residual 3668475211310791
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5762
      code := 7581134641813447710
      certificate := .residual 3364684048378247
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1155
      code := 2851717181728189470
      certificate := .residual 195669169027698
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5507
      code := 6428199926608093470
      certificate := .residual 3668990170121922
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5763
      code := 4147065159622517790
      certificate := .residual 1747075244286177
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1156
      code := 5995847647167605790
      certificate := .residual 1180591036317281
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5508
      code := 6425956922887430430
      certificate := .residual 3475132492523333
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5764
      code := 5563522009221227550
      certificate := .residual 269091065348338
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1157
      code := 2862200039420881950
      certificate := .residual 712148126415824
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5509
      code := 5564643494152823070
      certificate := .residual 4090947459234498
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5765
      code := 5128993644064465950
      certificate := .residual 1077621191612339
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1158
      code := 3870992742516157470
      certificate := .residual 1202805157281616
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5510
      code := 6137730944782229790
      certificate := .residual 3035521571474114
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5766
      code := 8659109032603345950
      certificate := .residual 1747075244286176
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1159
      code := 6175166435649285150
      certificate := .residual 349065324160112
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5511
      code := 5563521992292491550
      certificate := .residual 2306430243652197
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5767
      code := 8659100210975400990
      certificate := .residual 3299984631541248
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
