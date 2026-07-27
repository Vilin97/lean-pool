/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 8–15 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets01 : Array (List PatternEntry) := #[
  [
    { origin := 264
      mask := 573189120
      certificate := .k4 1 [1, 2, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 520
      mask := 11550371277176832
      certificate := .k4 3 [3, 5, 6] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1288
      mask := 11331567406311424
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1544
      mask := 73016356644864
      certificate := .k4 1 [1, 3, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1800
      mask := 9361242003301632
      certificate := .k4 1 [1, 2, 5, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4104
      mask := 1513210061336936460
      certificate := .k4 0 [0, 2, 7, 4, 3] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 265
      mask := 606743552
      certificate := .k4 1 [1, 2, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 521
      mask := 11611943928332288
      certificate := .k4 3 [3, 6, 5] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 777
      mask := 84544526
      certificate := .k4 0 [0, 3, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1033
      mask := 2533275885699084
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1289
      mask := 11331568446498816
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2313
      mask := 5809644498567823360
      certificate := .k4 2 [2, 4, 7, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4361
      mask := 5810792234088398848
      certificate := .k4 2 [2, 5, 6, 7, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7433
      mask := 4794081804510527758
      certificate := .k4 0 [0, 1, 2, 7, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8457
      mask := 13585844848430110
      certificate := .k4 0 [0, 4, 6, 5, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 266
      mask := 639773696
      certificate := .k4 1 [1, 2, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 522
      mask := 11620738947612672
      certificate := .k4 3 [3, 5, 6] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1546
      mask := 74768437111808
      certificate := .k4 1 [1, 2, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2314
      mask := 5809644517619400704
      certificate := .k4 3 [3, 4, 7, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3594
      mask := 10225647926902784
      certificate := .k4 2 [2, 6, 5, 4, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7434
      mask := 4794081817596559642
      certificate := .k4 0 [0, 1, 4, 7, 6, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 11
      mask := 10592512
      certificate := .sharedThree 1 2 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 267
      mask := 640166912
      certificate := .k4 1 [1, 3, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 523
      mask := 11620739484483584
      certificate := .k4 3 [3, 6, 5] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 779
      mask := 100862990
      certificate := .k4 0 [0, 2, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1035
      mask := 2533275914486026
      certificate := .k4 0 [0, 1, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1291
      mask := 11331568480051200
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4107
      mask := 1729382826329571356
      certificate := .k4 0 [0, 2, 3, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4363
      mask := 5814222572928106496
      certificate := .k4 2 [2, 5, 6, 7, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5899
      mask := 12116106420510
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6667
      mask := 9644916051821838
      certificate := .k4 0 [0, 1, 3, 6, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 524
      mask := 11821949592299520
      certificate := .k4 1 [1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 780
      mask := 101254414
      certificate := .k4 0 [0, 1, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1036
      mask := 2533275914487818
      certificate := .k4 0 [0, 3, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1292
      mask := 11333766469910528
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4108
      mask := 1729382830557429788
      certificate := .k4 0 [0, 2, 4, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4364
      mask := 5814226972846325760
      certificate := .k4 3 [3, 5, 6, 7, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7692
      mask := 75213759972618
      certificate := .k4 0 [0, 1, 3, 2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 525
      mask := 11821950632486912
      certificate := .k4 1 [1, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 781
      mask := 101256206
      certificate := .k4 0 [0, 2, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1037
      mask := 2533275936030732
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 14
      mask := 12697856
      certificate := .sharedThree 1 2 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 270
      mask := 1112165376
      certificate := .k4 1 [1, 2, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 526
      mask := 11821950666024960
      certificate := .k4 1 [1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 782
      mask := 101319950
      certificate := .k4 0 [0, 1, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1038
      mask := 2533275952283660
      certificate := .k4 0 [0, 2, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3086
      mask := 3400137774202880
      certificate := .k4 2 [2, 3, 5, 6, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4110
      mask := 1729382843258306588
      certificate := .k4 0 [0, 2, 3, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7438
      mask := 4796333903797518614
      certificate := .k4 0 [0, 1, 2, 7, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 271
      mask := 1145719808
      certificate := .k4 1 [1, 2, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 527
      mask := 11821950666039296
      certificate := .k4 1 [1, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1039
      mask := 2533275952742412
      certificate := .k4 0 [0, 3, 2, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2319
      mask := 5811896283073347584
      certificate := .k4 3 [3, 6, 7, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7439
      mask := 4796333921027522842
      certificate := .k4 0 [0, 1, 3, 7, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets01 : Array (List HardEntry) := #[
  [
    { origin := 8
      code := 8697799730289388830
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 2 0 1 5 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 776
      code := 8266581603606816030
      certificate := .residual 3916658220028291
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1032
      code := 5420594277881441310
      certificate := .residual 768639863790514
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1288
      code := 3140075081450941470
      certificate := .residual 4346719763574279
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5384
      code := 3285891231469789470
      certificate := .residual 4349139977733378
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5640
      code := 3146988536760295710
      certificate := .residual 263033069355504
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 9
      code := 8410694158827859230
      certificate := .residual 3918988239981702
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 777
      code := 3726884181624710430
      certificate := .residual 157979233573620
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1033
      code := 5419406806330076190
      certificate := .residual 1203547363024721
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1289
      code := 2851844722479098910
      certificate := .residual 3323068763737746
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5385
      code := 4154163606970425630
      certificate := .residual 1022613787071408
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5641
      code := 7654234419566403870
      certificate := .residual 3300225149774344
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 10
      code := 8697795349422746910
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 1 2 5 6 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 778
      code := 3150432618907526430
      certificate := .residual 157994266016497
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1034
      code := 3713174884401638430
      certificate := .residual 1343842705006036
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1290
      code := 5130667230218972190
      certificate := .residual 3746380685381268
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5386
      code := 8374880746683490590
      certificate := .residual 3363977526215938
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5642
      code := 7650869913985409310
      certificate := .residual 3300225149774345
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 11
      code := 8689069625664810270
      certificate := .hubPentagon 0 [0, 1, 2, 4, 3, 5, 6, 7] 0 1 2 6 4 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 779
      code := 8693867215323751710
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 6 5 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1035
      code := 5446490936687815710
      certificate := .residual 236284790560113
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1291
      code := 5130666135002311710
      certificate := .residual 3746380685381265
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5387
      code := 3289485261948576030
      certificate := .residual 1022609995944880
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5643
      code := 8659741810657255710
      certificate := .residual 3362744870465794
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 12
      code := 6168184248254803230
      certificate := .residual 4403991276775443
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 780
      code := 7654313722328474910
      certificate := .residual 1167913026665954
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1036
      code := 5455147529172249630
      certificate := .residual 1703548918296290
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1292
      code := 2858189038789094430
      certificate := .residual 3253799472467604
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5388
      code := 3857276638301118750
      certificate := .residual 209140128487920
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5644
      code := 4149307752152490270
      certificate := .residual 3035688894908098
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 13
      code := 8688509961394924830
      certificate := .residual 708974291475411
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 781
      code := 4154171992331347230
      certificate := .residual 2471328076515536
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1037
      code := 8189464194495114270
      certificate := .residual 3299984631541254
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1293
      code := 2857907568107351070
      certificate := .residual 3253799472467601
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5389
      code := 3865933230785552670
      certificate := .residual 4346975314200073
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5645
      code := 3862203275907621150
      certificate := .residual 1734838808404581
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 14
      code := 6454721393713163550
      certificate := .residual 4278891759698982
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 782
      code := 6463102686283326750
      certificate := .residual 1243631141429042
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1038
      code := 8192693988426869790
      certificate := .residual 1831459452811859
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1294
      code := 5132297947931765790
      certificate := .residual 1766497048060753
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5390
      code := 3289481274575151390
      certificate := .residual 4346975314200072
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5646
      code := 4147064748431827230
      certificate := .residual 2920841436030789
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 15
      code := 6175167135772519710
      certificate := .residual 4403991276775444
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 783
      code := 8262233563400398110
      certificate := .residual 3254039990700688
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1039
      code := 6451358515895823390
      certificate := .residual 4410442049490187
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1295
      code := 3714161027419499550
      certificate := .residual 1734880180889185
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5391
      code := 3280824408286552350
      certificate := .residual 209138249382384
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5647
      code := 3285751319697219870
      certificate := .residual 3668700697602754
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
