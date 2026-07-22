/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 72–79 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets09 : Array (List PatternEntry) := #[
  [
    { origin := 584
      mask := 39406498967191552
      certificate := .k4 2 [2, 3, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 840
      mask := 5497560441094
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1352
      mask := 13590411738087424
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1864
      mask := 10696049117193478
      certificate := .k4 0 [0, 1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2120
      mask := 1729382822000459802
      certificate := .k4 0 [0, 4, 7, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 73
      mask := 562649300992
      certificate := .sharedThree 2 4 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 585
      mask := 39406499973824512
      certificate := .k4 2 [2, 6, 3] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 841
      mask := 5497560441862
      certificate := .k4 0 [0, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1097
      mask := 4785353782263828
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1609
      mask := 97084253405184
      certificate := .k4 2 [2, 4, 3, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1865
      mask := 10696049117323526
      certificate := .k4 0 [0, 1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3145
      mask := 5066850228715798
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4425
      mask := 7735538101270
      certificate := .k4 0 [0, 4, 3, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6217
      mask := 92513601020166
      certificate := .k4 0 [0, 1, 2, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 74
      mask := 564838531072
      certificate := .sharedThree 3 4 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 330
      mask := 300653102080
      certificate := .k4 1 [1, 2, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 586
      mask := 39406500036739072
      certificate := .k4 2 [2, 3, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 842
      mask := 5498114473996
      certificate := .k4 0 [0, 2, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1098
      mask := 4785355135909912
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1610
      mask := 97174994026520
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1866
      mask := 10696049121371398
      certificate := .k4 0 [0, 1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2122
      mask := 1729382830623948828
      certificate := .k4 0 [0, 4, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6218
      mask := 92515228778508
      certificate := .k4 0 [0, 2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6474
      mask := 3096526533968146
      certificate := .k4 0 [0, 1, 6, 3, 2, 4] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 587
      mask := 39406500040409088
      certificate := .k4 2 [2, 6, 3] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2123
      mask := 1729382851813572634
      certificate := .k4 0 [0, 3, 7, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2635
      mask := 13216423346204
      certificate := .k4 0 [0, 4, 2, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 76
      mask := 573462020096
      certificate := .sharedThree 3 4 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1100
      mask := 4785362366906642
      certificate := .k4 0 [0, 1, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1612
      mask := 142939274224640
      certificate := .k4 1 [1, 2, 5, 3] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2124
      mask := 1729382856091762714
      certificate := .k4 0 [0, 4, 7, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6220
      mask := 92532676034572
      certificate := .k4 0 [0, 2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6476
      mask := 3096551162462494
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6732
      mask := 9654812157174798
      certificate := .k4 0 [0, 3, 5, 6, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8780
      mask := 5810207023318574354
      certificate := .k4 0 [0, 1, 4, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10060
      mask := 5802888675058715678
      certificate := .k4 0 [0, 2, 4, 1, 7, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 333
      mask := 310652698624
      certificate := .k4 2 [2, 3, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 589
      mask := 40533238473555968
      certificate := .k4 2 [2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8781
      mask := 5810769973267817746
      certificate := .k4 0 [0, 1, 4, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9805
      mask := 2460302402738880782
      certificate := .k4 0 [0, 1, 3, 7, 5, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 78
      mask := 588419497984
      certificate := .sharedThree 2 4 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 590
      mask := 40533259129454592
      certificate := .k4 3 [3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 846
      mask := 5639295270932
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1102
      mask := 4785366667165716
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1614
      mask := 143640897922048
      certificate := .k4 1 [1, 2, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 79
      mask := 691489775872
      certificate := .sharedThree 1 4 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 591
      mask := 40762057137586176
      certificate := .k4 4 [4, 5, 6] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 847
      mask := 5652180172820
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1103
      mask := 4785370961084436
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1359
      mask := 13599070929027072
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5199
      mask := 6755701180465182
      certificate := .k4 0 [0, 3, 6, 4, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets09 : Array (List HardEntry) := #[
  [
    { origin := 72
      code := 7395849338384559390
      certificate := .residual 1988157039375808
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1096
      code := 5450925404522572830
      certificate := .residual 4346719763574277
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5448
      code := 4147065160742396190
      certificate := .residual 2183194900947538
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5704
      code := 3280828673173939230
      certificate := .residual 1007254448117683
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 73
      code := 7389091843033017630
      certificate := .residual 129319945053040
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1097
      code := 5162695045550730270
      certificate := .residual 2508035153971762
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5449
      code := 3285751732007788830
      certificate := .residual 4161210715195079
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5705
      code := 3284630093195043870
      certificate := .residual 1755613694320865
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 74
      code := 6166494858022759710
      certificate := .residual 2059470678193712
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1098
      code := 5131229325436677150
      certificate := .residual 3262818903856402
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5450
      code := 3858839182637195550
      certificate := .residual 4349155010119820
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5706
      code := 6141095331459425310
      certificate := .residual 277990329336050
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 75
      code := 6164251841467526430
      certificate := .residual 620939081163744
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1099
      code := 5131238018718919710
      certificate := .residual 837909096354738
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5451
      code := 3284630230147457310
      certificate := .residual 2675488465555026
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5707
      code := 5600374758902522910
      certificate := .residual 936902869129139
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 76
      code := 6461140884774923550
      certificate := .residual 1202434926124884
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1100
      code := 8181864353213475870
      certificate := .residual 1346467693059776
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5452
      code := 6141095468411838750
      certificate := .residual 3668975137729218
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5708
      code := 6172627260742886430
      certificate := .residual 4403716935715217
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 77
      code := 6171789023942749470
      certificate := .residual 2077096158814771
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1101
      code := 8184107220032056350
      certificate := .residual 3902339872237968
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5453
      code := 6425956940936044830
      certificate := .residual 2965170007136962
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5709
      code := 5164104614118220830
      certificate := .residual 2468796906851412
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 78
      code := 7681264814949346590
      certificate := .residual 1202449987870548
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1102
      code := 7148782482630405150
      certificate := .residual 1394214353296690
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5454
      code := 5564643512201437470
      certificate := .residual 1752426831602277
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5710
      code := 3860651038767375390
      certificate := .residual 4334447695825297
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 79
      code := 7391912954117172510
      certificate := .residual 2077111220560435
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1103
      code := 5995852285009751070
      certificate := .residual 1835341575158225
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5455
      code := 6137730962830844190
      certificate := .residual 4046707148285765
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5711
      code := 2852408767607792670
      certificate := .residual 2469879245950036
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
