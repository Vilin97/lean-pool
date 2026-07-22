/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 16–23 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets02 : Array (List PatternEntry) := #[
  [
    { origin := 272
      mask := 1178749952
      certificate := .k4 1 [1, 2, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 784
      mask := 12886017302
      certificate := .k4 0 [0, 1, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1040
      mask := 2533555322224664
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1296
      mask := 11338164476078080
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1552
      mask := 76965818230022
      certificate := .k4 0 [0, 1, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6416
      mask := 1708821463985152
      certificate := .k4 1 [1, 5, 6, 4, 2] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 17
      mask := 14737408
      certificate := .sharedThree 1 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 273
      mask := 1179143168
      certificate := .k4 1 [1, 3, 2] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 529
      mask := 11901113859074048
      certificate := .k4 1 [1, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1041
      mask := 2533585386995736
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1553
      mask := 76965818360070
      certificate := .k4 0 [0, 1, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2321
      mask := 5850670421308866560
      certificate := .k4 4 [4, 6, 7, 5] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 18
      mask := 369098774
      certificate := .sharedThree 0 3 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 274
      mask := 1179272192
      certificate := .k4 1 [1, 2, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 530
      mask := 12384899586064384
      certificate := .k4 2 [2, 3, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 786
      mask := 12886082838
      certificate := .k4 0 [0, 1, 4, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1042
      mask := 2533589413527576
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1298
      mask := 11338165012948992
      certificate := .k4 1 [1, 3, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2322
      mask := 5882142704703373312
      certificate := .k4 4 [4, 5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3602
      mask := 10487141910012934
      certificate := .k4 0 [0, 2, 6, 5, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4626
      mask := 79165397296394
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10002
      mask := 4945031556302507278
      certificate := .k4 0 [0, 1, 2, 7, 6, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 19
      mask := 589496320
      certificate := .sharedThree 2 3 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1043
      mask := 2533589665185816
      certificate := .k4 0 [0, 4, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1811
      mask := 9644916636412928
      certificate := .k4 1 [1, 3, 6, 5] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2067
      mask := 504403158358425614
      certificate := .k4 0 [0, 3, 2, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2835
      mask := 27539885064220
      certificate := .k4 0 [0, 2, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3091
      mask := 3404518373457920
      certificate := .k4 2 [2, 3, 6, 5, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3859
      mask := 13598923026482176
      certificate := .k4 1 [1, 2, 4, 5, 6] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4627
      mask := 79165397361676
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5139
      mask := 5348342721216534
      certificate := .k4 0 [0, 2, 3, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7187
      mask := 13586944357508118
      certificate := .k4 0 [0, 2, 4, 1, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 20
      mask := 620766464
      certificate := .sharedThree 1 3 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 532
      mask := 12384900655611904
      certificate := .k4 2 [2, 3, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 788
      mask := 13170116890
      certificate := .k4 0 [0, 1, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1044
      mask := 2814749872114688
      certificate := .k4 1 [1, 2, 3, 6] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4116
      mask := 1729401672863580184
      certificate := .k4 0 [0, 3, 7, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4372
      mask := 6958853218688327680
      certificate := .k4 1 [1, 6, 7, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4628
      mask := 79166464814092
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10772
      mask := 6954279246022396958
      certificate := .k4 0 [0, 2, 4, 5, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1301
      mask := 11338611924402176
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3861
      mask := 13598941576710144
      certificate := .k4 1 [1, 3, 4, 5, 6] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8725
      mask := 4936508141846675742
      certificate := .k4 0 [0, 1, 3, 6, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10773
      mask := 6954279246105693214
      certificate := .k4 0 [0, 3, 4, 5, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 22
      mask := 825294848
      certificate := .sharedThree 2 3 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 534
      mask := 12459667443679232
      certificate := .k4 3 [3, 6, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 790
      mask := 13186894106
      certificate := .k4 0 [0, 1, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1046
      mask := 2814750912302080
      certificate := .k4 1 [1, 2, 6, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2070
      mask := 504403179749900310
      certificate := .k4 0 [0, 4, 2, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2326
      mask := 5947003903903006720
      certificate := .k4 3 [3, 6, 7, 4] 1 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2582
      mask := 10995670526990
      certificate := .k4 0 [0, 2, 3, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4630
      mask := 79166498366476
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6934
      mask := 11259000233025802
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 23
      mask := 1128464384
      certificate := .sharedThree 2 3 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 535
      mask := 12464063819284480
      certificate := .k4 2 [2, 6, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1303
      mask := 11340363499331584
      certificate := .k4 1 [1, 5, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2071
      mask := 504403720914665494
      certificate := .k4 0 [0, 2, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2583
      mask := 10995687302414
      certificate := .k4 0 [0, 1, 2, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4375
      mask := 6960533539548823552
      certificate := .k4 3 [3, 5, 7, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5655
      mask := 14636977964147732
      certificate := .k4 0 [0, 2, 4, 1, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6423
      mask := 1970364900983070
      certificate := .k4 0 [0, 1, 4, 6, 3] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7703
      mask := 79186873181208
      certificate := .k4 0 [0, 3, 4, 5, 2, 1] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8727
      mask := 4936508180216168734
      certificate := .k4 0 [0, 1, 4, 6, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets02 : Array (List HardEntry) := #[
  [
    { origin := 16
      code := 7397963681003285790
      certificate := .residual 3918988239981699
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 784
      code := 8693728118512968990
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 6, 7] 0 1 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1040
      code := 6136111352343260190
      certificate := .residual 3045388487022112
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1296
      code := 5420526107913907230
      certificate := .residual 257256841594482
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5392
      code := 8369814334206501150
      certificate := .residual 191580323985904
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5648
      code := 3858838770326626590
      certificate := .residual 4091069608319682
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 17
      code := 7688989032892673310
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 5 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 785
      code := 5996980126964409630
      certificate := .residual 712033508203473
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1041
      code := 8184531214588800030
      certificate := .residual 1805483491652404
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1297
      code := 5132295748942064670
      certificate := .residual 3489747765103381
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5393
      code := 3865932820079304990
      certificate := .residual 3361812862682632
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5649
      code := 6428199532346138910
      certificate := .residual 2675518563356242
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 18
      code := 5445915077183089950
      certificate := .residual 4411689737676928
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 786
      code := 8693858838493881630
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 6 5 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1042
      code := 7175740291220597790
      certificate := .residual 2049895082094273
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1298
      code := 5130613496151567390
      certificate := .residual 3486425606329121
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5394
      code := 3289480863868903710
      certificate := .residual 3361812862682633
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5650
      code := 6141095056101269790
      certificate := .residual 3035311114012359
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 19
      code := 7391473148990926110
      certificate := .residual 4411689737676929
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 787
      code := 4154163606945096990
      certificate := .residual 1978746867214544
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1043
      code := 5419468377941437470
      certificate := .residual 1823071514850097
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1299
      code := 6454719482227092510
      certificate := .residual 2983541482437160
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5395
      code := 7793362241094017310
      certificate := .residual 191582203091440
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5651
      code := 6425956528625475870
      certificate := .residual 3363992558602380
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 20
      code := 6464014315383041310
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 7, 6] 0 1 2 4 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 788
      code := 3726884181390746910
      certificate := .residual 157979233573617
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1044
      code := 8180738470737177630
      certificate := .residual 1839048902310592
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1300
      code := 6024062767859788830
      certificate := .residual 4409479976808714
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5396
      code := 5600390815133917470
      certificate := .residual 4409615268393218
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5652
      code := 5564643099890868510
      certificate := .residual 1620093009165906
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 21
      code := 6168179867137486110
      certificate := .residual 3911289779080211
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 789
      code := 8230765558615860510
      certificate := .residual 1159119080898018
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1045
      code := 6460014971478174750
      certificate := .residual 3487524849550112
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1301
      code := 2852284528975703070
      certificate := .residual 1765399672906577
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5397
      code := 3284769712112328990
      certificate := .residual 4348042613567746
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5653
      code := 6137730550520275230
      certificate := .residual 2042461542408786
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 22
      code := 5450438317695970590
      certificate := .residual 4403991276775440
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 790
      code := 6460859425737565470
      certificate := .residual 1244713473302322
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1046
      code := 7184465745452559390
      certificate := .residual 3794595216460161
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1302
      code := 3139951938027678750
      certificate := .residual 266035765757554
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5398
      code := 6455296734412857630
      certificate := .residual 4408397645048329
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5654
      code := 6425393587261989150
      certificate := .residual 1442160232545314
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 23
      code := 6170945011122842910
      certificate := .residual 4403991276775441
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 791
      code := 7688024503822214430
      certificate := .residual 3253902820010640
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1047
      code := 7175740154318515230
      certificate := .residual 3795707613169029
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1303
      code := 5996977927222225950
      certificate := .residual 1743538842297953
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5399
      code := 6168192258167988510
      certificate := .residual 4408397645048328
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5655
      code := 6425941135697568030
      certificate := .residual 2488068499035170
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
