/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 80–87 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets10 : Array (List PatternEntry) := #[
  [
    { origin := 80
      mask := 691500285952
      certificate := .sharedThree 2 4 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 336
      mask := 319203330048
      certificate := .k4 1 [1, 3, 4] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1104
      mask := 4785370962067476
      certificate := .k4 0 [0, 4, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1616
      mask := 143661052471296
      certificate := .k4 1 [1, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3152
      mask := 5066867458720026
      certificate := .k4 0 [0, 1, 3, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6736
      mask := 9658256168534294
      certificate := .k4 0 [0, 1, 2, 6, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 81
      mask := 694190866432
      certificate := .sharedThree 3 4 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 849
      mask := 5656475074580
      certificate := .k4 0 [0, 4, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1105
      mask := 4785385200680984
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1361
      mask := 13601104864501760
      certificate := .k4 1 [1, 5, 4, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2385
      mask := 38957286686
      certificate := .k4 0 [0, 1, 2, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4177
      mask := 2594224018553307148
      certificate := .k4 0 [0, 3, 2, 7, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6225
      mask := 92646741796114
      certificate := .k4 0 [0, 1, 4, 2, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8785
      mask := 6954280203802722582
      certificate := .k4 0 [0, 1, 2, 6, 7, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9809
      mask := 2460302415573975318
      certificate := .k4 0 [0, 1, 4, 7, 5, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 82
      mask := 695795318784
      certificate := .sharedThree 2 4 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 338
      mask := 327564132352
      certificate := .k4 2 [2, 3, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 850
      mask := 6597640858624
      certificate := .k4 1 [1, 2, 3, 5] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1106
      mask := 4785389227212824
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2386
      mask := 38957288478
      certificate := .k4 0 [0, 2, 4, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3154
      mask := 5066867693602842
      certificate := .k4 0 [0, 3, 4, 6, 1] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4178
      mask := 2594232836036821012
      certificate := .k4 0 [0, 2, 4, 7, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6226
      mask := 92663922581778
      certificate := .k4 0 [0, 1, 4, 2, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9298
      mask := 9658282239673614
      certificate := .k4 0 [0, 1, 2, 6, 5, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 83
      mask := 698502610944
      certificate := .sharedThree 3 4 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 339
      mask := 327765458944
      certificate := .k4 2 [2, 4, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 595
      mask := 41096179823460352
      certificate := .k4 1 [1, 6, 4] 1 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 851
      mask := 6597642824704
      certificate := .k4 1 [1, 3, 5, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1107
      mask := 4785389478871064
      certificate := .k4 0 [0, 4, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1363
      mask := 13601242303455232
      certificate := .k4 1 [1, 5, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2387
      mask := 38957352222
      certificate := .k4 0 [0, 1, 4, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4179
      mask := 2594232836037804052
      certificate := .k4 0 [0, 4, 2, 7, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7251
      mask := 14074028014773526
      certificate := .k4 0 [0, 1, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 84
      mask := 704374678528
      certificate := .sharedThree 1 4 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 340
      mask := 327831519232
      certificate := .k4 2 [2, 3, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 596
      mask := 41658863502491648
      certificate := .k4 2 [2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2388
      mask := 38957354014
      certificate := .k4 0 [0, 4, 3, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3412
      mask := 9650414110664714
      certificate := .k4 0 [0, 3, 5, 6, 1] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4180
      mask := 2595975540491969536
      certificate := .k4 1 [1, 5, 6, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4692
      mask := 88102670591250
      certificate := .k4 0 [0, 1, 4, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5716
      mask := 39406498916992266
      certificate := .k4 0 [0, 1, 3, 2, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 85
      mask := 707126099968
      certificate := .sharedThree 3 4 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 597
      mask := 41659121200529408
      certificate := .k4 2 [2, 6, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 853
      mask := 6597674413056
      certificate := .k4 1 [1, 2, 5, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1365
      mask := 13603312483958784
      certificate := .k4 2 [2, 5, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2133
      mask := 2450169303528563712
      certificate := .k4 1 [1, 2, 7, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4693
      mask := 88102670656532
      certificate := .k4 0 [0, 2, 4, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6485
      mask := 3377726586094878
      certificate := .k4 0 [0, 1, 3, 6, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8533
      mask := 14637008314066186
      certificate := .k4 0 [0, 1, 3, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 598
      mask := 41659138376204288
      certificate := .k4 2 [2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1622
      mask := 145860111892480
      certificate := .k4 2 [2, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2390
      mask := 38990449694
      certificate := .k4 0 [0, 2, 4, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2902
      mask := 1688849915331854
      certificate := .k4 0 [0, 1, 3, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4182
      mask := 2603859038865220608
      certificate := .k4 1 [1, 6, 5, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5462
      mask := 11347141511348250
      certificate := .k4 0 [0, 3, 6, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8790
      mask := 6954834357664164110
      certificate := .k4 0 [0, 1, 2, 6, 7, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 87
      mask := 721565515776
      certificate := .sharedThree 2 4 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 599
      mask := 41659138379350016
      certificate := .k4 2 [2, 6, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1367
      mask := 13603449922912256
      certificate := .k4 2 [2, 5, 6, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1623
      mask := 145877225177088
      certificate := .k4 2 [2, 4, 5, 3] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2903
      mask := 1688849915333646
      certificate := .k4 0 [0, 3, 1, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4439
      mask := 10995923231006
      certificate := .k4 0 [0, 1, 2, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5719
      mask := 40532675832038420
      certificate := .k4 0 [0, 2, 4, 1, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7255
      mask := 14074040900723974
      certificate := .k4 0 [0, 1, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets10 : Array (List HardEntry) := #[
  [
    { origin := 80
      code := 7181721629143215390
      certificate := .residual 1434001270554048
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1104
      code := 3865150934157388830
      certificate := .residual 2466098654466387
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5456
      code := 5563522010341105950
      certificate := .residual 4161314055964354
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5712
      code := 6139472451290588190
      certificate := .residual 3280015953037714
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 81
      code := 7684084094901300510
      certificate := .residual 1434003178962368
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1105
      code := 5131230155405552670
      certificate := .residual 2277607609955554
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5457
      code := 3858276241273708830
      certificate := .residual 1440236054166562
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5713
      code := 3866713884395627550
      certificate := .residual 3772597165951378
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 82
      code := 6459170576917474590
      certificate := .residual 3911410038171666
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1106
      code := 3865016222508149790
      certificate := .residual 2457440067492148
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5458
      code := 2850032866341085470
      certificate := .residual 2487797850035234
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5714
      code := 3858832585517491230
      certificate := .residual 3685168810169621
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 83
      code := 7176861673663376670
      certificate := .residual 4403991276775442
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1107
      code := 3721463984385715230
      certificate := .residual 2762492304913601
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5459
      code := 6176842108091162910
      certificate := .residual 4409479976808706
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5715
      code := 3284623633027752990
      certificate := .residual 3678569492256289
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 84
      code := 7688143357060066590
      certificate := .residual 4411569478585476
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1108
      code := 7148773669558840350
      certificate := .residual 2448646004513073
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5460
      code := 4149308027560976670
      certificate := .residual 3527982536284866
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5716
      code := 2850165361737262110
      certificate := .residual 1977298036649044
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 85
      code := 7679699108262063390
      certificate := .residual 4411569478585473
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1109
      code := 5419387134861143070
      certificate := .residual 2969521916484257
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5461
      code := 3862203551316107550
      certificate := .residual 4046724067059525
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5717
      code := 2850026269221381150
      certificate := .residual 1977298036649041
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 86
      code := 5164102519270944030
      certificate := .residual 138097067231088
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1110
      code := 5131161156755942430
      certificate := .residual 2972874238990997
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5462
      code := 3285751595105706270
      certificate := .residual 4161451237492418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5718
      code := 3281946859336688670
      certificate := .residual 4325651870951825
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 87
      code := 8190575916684422430
      certificate := .residual 3918988239981700
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1111
      code := 6171492125234457630
      certificate := .residual 822483828394929
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5463
      code := 3858839045735112990
      certificate := .residual 3106025427053250
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5719
      code := 5560768545664066590
      certificate := .residual 3271220128164242
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
