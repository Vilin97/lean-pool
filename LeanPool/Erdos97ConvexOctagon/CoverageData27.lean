/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 216–223 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets27 : Array (List PatternEntry) := #[
  [
    { origin := 216
      mask := 4971973988617045248
      certificate := .sharedThree 1 7 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 472
      mask := 3659174702022668
      certificate := .k4 0 [0, 2, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 728
      mask := 5476377148036481024
      certificate := .k4 2 [2, 3, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 984
      mask := 844424934539526
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1240
      mask := 10205666931270656
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6616
      mask := 5911253734149150
      certificate := .k4 0 [0, 3, 4, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8664
      mask := 2882446721986601246
      certificate := .k4 0 [0, 1, 4, 5, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10712
      mask := 5233258674377467158
      certificate := .k4 0 [0, 1, 4, 3, 7, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10968
      mask := 5233255380138665238
      certificate := .k4 0 [0, 1, 2, 5, 6, 7, 3, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 217
      mask := 4971973989774655488
      certificate := .sharedThree 3 7 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 473
      mask := 3659175854866444
      certificate := .k4 0 [0, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 985
      mask := 844424934540294
      certificate := .k4 0 [0, 2, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1241
      mask := 10205666935333888
      certificate := .k4 1 [1, 5, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2009
      mask := 37718488702403584
      certificate := .k4 1 [1, 2, 6, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5081
      mask := 3377748312719382
      certificate := .k4 0 [0, 4, 3, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5337
      mask := 10213363514681614
      certificate := .k4 0 [0, 1, 2, 6, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5593
      mask := 13591342403823898
      certificate := .k4 0 [0, 1, 4, 6, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7385
      mask := 2450107731508691214
      certificate := .k4 0 [0, 1, 2, 7, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10969
      mask := 5233257548864359446
      certificate := .k4 0 [0, 2, 4, 5, 6, 7, 3, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 218
      mask := 4971974284969771008
      certificate := .sharedThree 4 7 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 730
      mask := 5476377150175576064
      certificate := .k4 2 [2, 3, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7386
      mask := 2450107744594723098
      certificate := .k4 0 [0, 1, 4, 7, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 219
      mask := 4972049854919344128
      certificate := .sharedThree 5 7 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 475
      mask := 4785370962132992
      certificate := .k4 2 [2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1243
      mask := 10205666935463936
      certificate := .k4 1 [1, 5, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2011
      mask := 38280597986788352
      certificate := .k4 1 [1, 2, 3, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2267
      mask := 4949456419991584768
      certificate := .k4 2 [2, 7, 6, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4315
      mask := 5226427369815952384
      certificate := .k4 1 [1, 2, 3, 7, 6] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4827
      mask := 145864339292180
      certificate := .k4 0 [0, 2, 4, 5, 3] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 732
      mask := 5513531847096664064
      certificate := .k4 3 [3, 7, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 988
      mask := 844426054222090
      certificate := .k4 0 [0, 1, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1244
      mask := 10207865954526208
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1756
      mask := 5066871703357466
      certificate := .k4 0 [0, 4, 6, 1] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2268
      mask := 4949548349470539776
      certificate := .k4 2 [2, 7, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2524
      mask := 7696665944334
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4060
      mask := 1297056080165118226
      certificate := .k4 0 [0, 1, 7, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6620
      mask := 6755679721819166
      certificate := .k4 0 [0, 2, 4, 6, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8156
      mask := 9649314918908190
      certificate := .k4 0 [0, 1, 2, 6, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10716
      mask := 5233270876129132574
      certificate := .k4 0 [0, 2, 3, 7, 6, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 221
      mask := 5260204364773523456
      certificate := .sharedThree 2 7 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 477
      mask := 4874551657758720
      certificate := .k4 4 [4, 5, 6] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 733
      mask := 5514657743728279552
      certificate := .k4 2 [2, 7, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 989
      mask := 844426054223882
      certificate := .k4 0 [0, 3, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1245
      mask := 10207865956623360
      certificate := .k4 1 [1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3037
      mask := 3096225838679054
      certificate := .k4 0 [0, 3, 6, 1, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3805
      mask := 13583796152706048
      certificate := .k4 1 [1, 2, 5, 6, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6621
      mask := 6755679721882910
      certificate := .k4 0 [0, 1, 4, 2, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8669
      mask := 2882452236657501206
      certificate := .k4 0 [0, 4, 3, 7, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10973
      mask := 5801203152944456718
      certificate := .k4 0 [0, 2, 3, 4, 7, 6, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 222
      mask := 5260204678301351936
      certificate := .sharedThree 4 7 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1758
      mask := 5348024562827542
      certificate := .k4 0 [0, 1, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2270
      mask := 5017437694924423168
      certificate := .k4 2 [2, 5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4318
      mask := 5226427662110031872
      certificate := .k4 2 [2, 3, 4, 7, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7902
      mask := 2533297361142814
      certificate := .k4 0 [0, 3, 4, 6, 2, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 223
      mask := 5260284629117566976
      certificate := .sharedThree 5 7 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 479
      mask := 5348312320311314
      certificate := .k4 0 [0, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 735
      mask := 5764608364861456384
      certificate := .k4 2 [2, 4, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2015
      mask := 38281474361786368
      certificate := .k4 2 [2, 4, 3, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6623
      mask := 6755679754980382
      certificate := .k4 0 [0, 2, 4, 1, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets27 : Array (List HardEntry) := #[
  [
    { origin := 728
      code := 3714855799054951710
      certificate := .residual 1390963566763572
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 984
      code := 5166917172072115230
      certificate := .residual 4408547969025538
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1240
      code := 5420595106814192670
      certificate := .residual 3794595216460162
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5592
      code := 6141095312926368030
      certificate := .residual 1620230179855954
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5848
      code := 5993610964347970590
      certificate := .residual 3683244631790869
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 729
      code := 3148743783336142110
      certificate := .residual 4349155010119819
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 985
      code := 6031599482976168990
      certificate := .residual 2051807927923379
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1241
      code := 3718086284181335070
      certificate := .residual 4240596747572418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5593
      code := 6425956785450574110
      certificate := .residual 2112568877968978
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5849
      code := 8227380853451842590
      certificate := .residual 1977328134450260
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 730
      code := 3714287334548071710
      certificate := .residual 2969657266674336
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 986
      code := 5450925406644956190
      certificate := .residual 3885056387080850
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1242
      code := 4146499994827975710
      certificate := .residual 3466424917571394
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5594
      code := 5564643356715966750
      certificate := .residual 3105542419408583
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5850
      code := 5993595571420062750
      certificate := .residual 1977328134450257
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 731
      code := 3722943927032505630
      certificate := .residual 4350117082851467
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 987
      code := 5162695047673113630
      certificate := .residual 4408427709883911
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1243
      code := 3141634327970933790
      certificate := .residual 4108432009574597
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5595
      code := 5563521854855635230
      certificate := .residual 2605274057106002
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5851
      code := 8181717980948259870
      certificate := .residual 4394921110841746
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 732
      code := 5454296371357574430
      certificate := .residual 1513176851365313
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 988
      code := 4158171306167331870
      certificate := .hubPentagon 0 [0, 2, 3, 4, 1, 6, 5, 7] 0 1 2 4 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1244
      code := 3714161027670174750
      certificate := .residual 2316323549827173
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5596
      code := 6428193217871274270
      certificate := .residual 1995487289734178
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5852
      code := 8154766889367168030
      certificate := .residual 3340489419434385
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 733
      code := 5452053367636911390
      certificate := .residual 1452521171082804
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 989
      code := 3871061353839160350
      certificate := .residual 4326046471266576
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1245
      code := 3139952075180436510
      certificate := .residual 3044437743228226
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5597
      code := 3292862809742434590
      certificate := .residual 1007220624218032
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5853
      code := 3858262596370621470
      certificate := .residual 4175688787612949
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 734
      code := 3140638033493648670
      certificate := .residual 1461315131301425
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 990
      code := 3141759792546278430
      certificate := .residual 4326046471266577
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1246
      code := 5996978064374983710
      certificate := .residual 2043149273854418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5598
      code := 6427636839251370270
      certificate := .residual 1380587581332514
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5854
      code := 3281810640160220190
      certificate := .residual 4171284297078305
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 735
      code := 3148734961708197150
      certificate := .residual 1836074462738768
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 991
      code := 3145370465184476190
      certificate := .residual 3340523242430867
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1247
      code := 6425391775021624350
      certificate := .residual 2747091622785106
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5599
      code := 3870928982686490910
      certificate := .residual 3301307481534722
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5855
      code := 3858256025070658590
      certificate := .residual 2470991734230097
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
