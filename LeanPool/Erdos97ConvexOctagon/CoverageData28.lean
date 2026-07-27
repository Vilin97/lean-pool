/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 224–231 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets28 : Array (List PatternEntry) := #[
  [
    { origin := 480
      mask := 5910974516232212
      certificate := .k4 0 [0, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 736
      mask := 5764608385517355008
      certificate := .k4 3 [3, 4, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 992
      mask := 844712692957458
      certificate := .k4 0 [0, 1, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1504
      mask := 22157738508310
      certificate := .k4 0 [0, 4, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1760
      mask := 5348025916473626
      certificate := .k4 0 [0, 1, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3040
      mask := 3096225889404166
      certificate := .k4 0 [0, 1, 6, 3, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5856
      mask := 7885845176606
      certificate := .k4 0 [0, 1, 3, 5, 4] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7392
      mask := 2450116690172936470
      certificate := .k4 0 [0, 1, 2, 7, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 225
      mask := 5836665117077471232
      certificate := .sharedThree 2 7 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 481
      mask := 5911270863667220
      certificate := .k4 0 [0, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1505
      mask := 22162034982940
      certificate := .k4 0 [0, 2, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6369
      mask := 167300076470284
      certificate := .k4 0 [0, 2, 3, 4, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7393
      mask := 2450116707402940698
      certificate := .k4 0 [0, 1, 3, 7, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7905
      mask := 2814772334054430
      certificate := .k4 0 [0, 3, 4, 6, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9953
      mask := 4800911969620754702
      certificate := .k4 0 [0, 1, 3, 7, 6, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10977
      mask := 5801782698419233806
      certificate := .k4 0 [0, 2, 3, 6, 7, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 226
      mask := 5836665118431117312
      certificate := .sharedThree 3 7 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 482
      mask := 7036875776720920
      certificate := .k4 0 [0, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 738
      mask := 5806265819601043456
      certificate := .k4 2 [2, 6, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 994
      mask := 1407374887830790
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1506
      mask := 22166329884700
      certificate := .k4 0 [0, 4, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2018
      mask := 38843548983935242
      certificate := .k4 0 [0, 1, 3, 6] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4066
      mask := 1301822600510488850
      certificate := .k4 0 [0, 1, 7, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 227
      mask := 5836754177514012672
      certificate := .sharedThree 5 7 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 483
      mask := 7037187950379032
      certificate := .k4 0 [0, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 739
      mask := 5807391722983915520
      certificate := .k4 3 [3, 6, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 995
      mask := 1407374887896326
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1507
      mask := 22179213803548
      certificate := .k4 0 [0, 2, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2019
      mask := 38843549047343104
      certificate := .k4 1 [1, 3, 6, 2] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6115
      mask := 27629524823070
      certificate := .k4 0 [0, 2, 4, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6627
      mask := 6755684000597278
      certificate := .k4 0 [0, 1, 3, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 228
      mask := 7061644215723360256
      certificate := .sharedThree 2 7 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 484
      mask := 9362341510537472
      certificate := .k4 1 [1, 5, 6] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 996
      mask := 1407374887960838
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1508
      mask := 22183508705308
      certificate := .k4 0 [0, 4, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2788
      mask := 23231478309910
      certificate := .k4 0 [0, 2, 4, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6884
      mask := 10224358634037526
      certificate := .k4 0 [0, 1, 5, 6, 2] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8676
      mask := 2882519267964773642
      certificate := .k4 0 [0, 1, 3, 2, 7, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 229
      mask := 7061644217361104896
      certificate := .sharedThree 3 7 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 997
      mask := 1407374887961606
      certificate := .k4 0 [0, 2, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1253
      mask := 10210064979877888
      certificate := .k4 1 [1, 5, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3813
      mask := 13584887067975954
      certificate := .k4 0 [0, 1, 5, 6, 4] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4325
      mask := 5227069485072015360
      certificate := .k4 1 [1, 6, 7, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7909
      mask := 2814772417544478
      certificate := .k4 0 [0, 1, 4, 6, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9957
      mask := 4800911982455849238
      certificate := .k4 0 [0, 1, 4, 7, 6, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 230
      mask := 7061644636623732736
      certificate := .sharedThree 4 7 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 486
      mask := 9368940207669248
      certificate := .k4 3 [3, 5, 6] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 998
      mask := 1407375978856460
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2278
      mask := 5225864420898393088
      certificate := .k4 1 [1, 6, 7, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2790
      mask := 23231480340758
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4582
      mask := 74766847405068
      certificate := .k4 0 [0, 2, 3, 5, 1] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8422
      mask := 12384938974405906
      certificate := .k4 0 [0, 1, 4, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8678
      mask := 2892085019222754318
      certificate := .k4 0 [0, 3, 7, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10982
      mask := 5809715571966682382
      certificate := .k4 0 [0, 1, 2, 3, 4, 7, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 231
      mask := 7205759403792819200
      certificate := .sharedThree 1 7 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 487
      mask := 9378151285129216
      certificate := .k4 4 [4, 5, 6] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 743
      mask := 5908723544333795328
      certificate := .k4 1 [1, 7, 4] 1 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1511
      mask := 23089831739420
      certificate := .k4 0 [0, 3, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2279
      mask := 5228775928426921984
      certificate := .k4 3 [3, 5, 7, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2791
      mask := 23231480341526
      certificate := .k4 0 [0, 4, 5, 2, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4071
      mask := 1310636148279795712
      certificate := .k4 1 [1, 7, 4, 5, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4327
      mask := 5228776099688742912
      certificate := .k4 3 [3, 4, 7, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets28 : Array (List HardEntry) := #[
  [
    { origin := 736
      code := 5997049396192830750
      certificate := .residual 712033508203476
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 992
      code := 3714296387598904350
      certificate := .residual 1836423914256852
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1248
      code := 5420526108164582430
      certificate := .residual 4411674705290508
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5600
      code := 8688942511618187550
      certificate := .residual 340011981866480
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 737
      code := 6427699539260171550
      certificate := .residual 2218913724493875
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 993
      code := 7181504760096844830
      certificate := .residual 3302014003546500
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1249
      code := 5993052807863823390
      certificate := .residual 4240219047359687
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5601
      code := 8373204691001729310
      certificate := .residual 332317275857392
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 738
      code := 3723449702902621470
      certificate := .residual 712048544259028
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 994
      code := 2858049375519206430
      certificate := .residual 3361692603540993
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1250
      code := 5418843855374085150
      certificate := .residual 988043092366290
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5602
      code := 8230703860873355550
      certificate := .residual 3300089858189832
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 739
      code := 4154099845969962270
      certificate := .residual 2218928760549427
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 995
      code := 3149291443405286430
      certificate := .residual 2702633194729776
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1251
      code := 5132295749192739870
      certificate := .residual 1985458739798690
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5603
      code := 8229582359013024030
      certificate := .residual 3300089858189833
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 740
      code := 5420597722209281310
      certificate := .residual 711896337513428
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 996
      code := 2851856819445918750
      certificate := .residual 4346975314200066
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1252
      code := 6463392430482877470
      certificate := .residual 348930032675952
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5604
      code := 8401831412735074590
      certificate := .residual 3917860810886402
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 741
      code := 6425447996138415390
      certificate := .residual 2773067585007667
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 997
      code := 3714296126629309470
      certificate := .residual 2122159506911923
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1253
      code := 4158110309638302750
      certificate := .residual 4347907321983241
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5605
      code := 4149307735173423390
      certificate := .residual 1549863436361298
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 742
      code := 3149240895737652510
      certificate := .residual 711911373568980
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 998
      code := 3140070685995002910
      certificate := .residual 3323205934277266
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1254
      code := 3725771342480501790
      certificate := .residual 4347907321983240
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5606
      code := 3862203258928554270
      certificate := .residual 3303381950818444
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 743
      code := 4154091169666786590
      certificate := .residual 2773082621063219
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 999
      code := 2851840327023160350
      certificate := .residual 4346855055058439
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1255
      code := 3870935739527162910
      certificate := .residual 333533078752496
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5607
      code := 4147064731452760350
      certificate := .residual 3105559389562567
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
