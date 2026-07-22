/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 24–31 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets03 : Array (List PatternEntry) := #[
  [
    { origin := 24
      mask := 1157645568
      certificate := .sharedThree 1 3 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 280
      mask := 2257224704
      certificate := .k4 1 [1, 2, 3] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1560
      mask := 79165414075392
      certificate := .k4 1 [1, 2, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4376
      mask := 6960542095928983552
      certificate := .k4 3 [3, 6, 7, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5144
      mask := 5629778711809310
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10008
      mask := 4945040515000239382
      certificate := .k4 0 [0, 1, 2, 7, 6, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 537
      mask := 13511228386181120
      certificate := .k4 2 [2, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1049
      mask := 2814750946247680
      certificate := .k4 1 [1, 6, 3, 2] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1305
      mask := 11340364036202496
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1561
      mask := 79165448152064
      certificate := .k4 1 [1, 2, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2329
      mask := 6091118499518218240
      certificate := .k4 2 [2, 7, 6, 3] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3097
      mask := 3659174819414282
      certificate := .k4 0 [0, 1, 3, 2, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3865
      mask := 13599060463330304
      certificate := .k4 1 [1, 2, 4, 6, 5] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7449
      mask := 4936508141643844622
      certificate := .k4 0 [0, 2, 3, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 26
      mask := 1364262912
      certificate := .sharedThree 2 3 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 282
      mask := 12886147094
      certificate := .k4 0 [0, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 538
      mask := 13511247437758464
      certificate := .k4 3 [3, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2330
      mask := 6091119100602351616
      certificate := .k4 3 [3, 6, 7, 4] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3610
      mask := 10768616884610310
      certificate := .k4 0 [0, 1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4122
      mask := 1734168193745813528
      certificate := .k4 0 [0, 3, 7, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4890
      mask := 152456591843594
      certificate := .k4 0 [0, 1, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5146
      mask := 5629778711940126
      certificate := .k4 0 [0, 4, 6, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5914
      mask := 12283607589150
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6682
      mask := 9644928886916374
      certificate := .k4 0 [0, 1, 4, 6, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10522
      mask := 2605543504651354142
      certificate := .k4 0 [0, 3, 4, 6, 5, 7, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 27
      mask := 1627414784
      certificate := .sharedThree 1 3 0 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 283
      mask := 13203669018
      certificate := .k4 0 [0, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1307
      mask := 11342562562408448
      certificate := .k4 2 [2, 5, 3, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2075
      mask := 720575942644237326
      certificate := .k4 0 [0, 3, 7, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3867
      mask := 13599078478784512
      certificate := .k4 1 [1, 3, 4, 6, 5] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6427
      mask := 1970643004834066
      certificate := .k4 0 [0, 1, 6, 2, 3, 4] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6939
      mask := 11330468417053710
      certificate := .k4 0 [0, 2, 3, 1, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7707
      mask := 79204303660306
      certificate := .k4 0 [0, 1, 4, 2, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 28
      mask := 1633746944
      certificate := .sharedThree 2 3 0 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 540
      mask := 13603157866184704
      certificate := .k4 2 [2, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 796
      mask := 21760639004
      certificate := .k4 0 [0, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5148
      mask := 5629778812600350
      certificate := .k4 0 [0, 4, 6, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6172
      mask := 83563492630790
      certificate := .k4 0 [0, 1, 2, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7452
      mask := 4938196992561057038
      certificate := .k4 0 [0, 1, 2, 7, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 29
      mask := 1650589696
      certificate := .sharedThree 2 3 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 285
      mask := 21827158044
      certificate := .k4 0 [0, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 541
      mask := 13607557784403968
      certificate := .k4 3 [3, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 797
      mask := 21761622044
      certificate := .k4 0 [0, 3, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1309
      mask := 11342563099279360
      certificate := .k4 2 [2, 5, 6, 3] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2589
      mask := 10995754017038
      certificate := .k4 0 [0, 1, 2, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6429
      mask := 1970651539718430
      certificate := .k4 0 [0, 1, 3, 6, 4] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 30
      mask := 1677747200
      certificate := .sharedThree 1 3 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 542
      mask := 13811382168322048
      certificate := .k4 4 [4, 5, 6] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 798
      mask := 21810970652
      certificate := .k4 0 [0, 2, 4, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1310
      mask := 11347271115341824
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3102
      mask := 3659175792100366
      certificate := .k4 0 [0, 3, 6, 2, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4382
      mask := 6963854063864643584
      certificate := .k4 2 [2, 6, 7, 5, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4638
      mask := 79205404533010
      certificate := .k4 0 [0, 1, 4, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4894
      mask := 153932192194826
      certificate := .k4 0 [0, 1, 3, 5, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6174
      mask := 83564009971982
      certificate := .k4 0 [0, 1, 2, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 287
      mask := 25771048982
      certificate := .k4 0 [0, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 543
      mask := 13864158726455296
      certificate := .k4 4 [4, 6, 5] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 799
      mask := 21811953692
      certificate := .k4 0 [0, 4, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2335
      mask := 6999582281887145984
      certificate := .k4 1 [1, 5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4895
      mask := 153933803291914
      certificate := .k4 0 [0, 1, 3, 2, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6175
      mask := 83564010038538
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7455
      mask := 4940449091881600278
      certificate := .k4 0 [0, 1, 2, 7, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets03 : Array (List HardEntry) := #[
  [
    { origin := 24
      code := 7184589160277617950
      certificate := .residual 226406619532019
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 792
      code := 5420528452980860190
      certificate := .residual 711896337513425
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1048
      code := 8189394926319528990
      certificate := .residual 3331710506259856
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1304
      code := 2853403831846333470
      certificate := .residual 2923477778371361
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5400
      code := 4148893111707951390
      certificate := .residual 349875201253872
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5656
      code := 3290606744473493790
      certificate := .residual 1023692327717808
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 25
      code := 7180660618116476190
      certificate := .residual 3793888694448390
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 793
      code := 8693719202631148830
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 6, 7] 0 1 2 4 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1049
      code := 7175177204398648350
      certificate := .residual 1877999719610674
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1305
      code := 2851721579055836190
      certificate := .residual 2927897312299797
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5401
      code := 5995936581807694110
      certificate := .residual 342176711443952
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5657
      code := 3869310384852230430
      certificate := .residual 1015995746266032
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 26
      code := 6031663275072564510
      certificate := .residual 779463114410963
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 794
      code := 7688081784408925470
      certificate := .residual 4348042613567745
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1050
      code := 3713035248555617310
      certificate := .residual 1343842705006033
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1306
      code := 4153888184988625950
      certificate := .residual 3546491193113128
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5402
      code := 5564712493871980830
      certificate := .residual 3794715475545346
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5658
      code := 3284062743641514270
      certificate := .residual 1871244612204578
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 27
      code := 6022943160021822750
      certificate := .residual 3723640476413990
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 795
      code := 5455140781798483230
      certificate := .residual 595511780550626
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1051
      code := 6454735958723619870
      certificate := .residual 3917740551801216
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1307
      code := 3721549217830824990
      certificate := .residual 4347907321983242
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5403
      code := 3862203671239123230
      certificate := .residual 4231802802030274
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5659
      code := 5419393472641163550
      certificate := .residual 2425263122528290
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 28
      code := 6019002510582754590
      certificate := .residual 3918988239981696
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 796
      code := 5454296369753253150
      certificate := .residual 4349155010119813
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1052
      code := 5419400209260702750
      certificate := .residual 3489764676551445
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5404
      code := 4147065143763329310
      certificate := .residual 3527997568727746
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5660
      code := 7650865515905736990
      certificate := .residual 1094060979620784
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 29
      code := 7171934894358539550
      certificate := .residual 3911289779080208
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 797
      code := 3147054906303079710
      certificate := .residual 112070295373681
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1053
      code := 5418839458330536990
      certificate := .residual 3487524849550113
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5405
      code := 3285751715028721950
      certificate := .residual 4038065412876101
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5661
      code := 5993610964398301470
      certificate := .residual 1871109262014498
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 30
      code := 5442550541537783070
      certificate := .residual 4411689737676937
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 798
      code := 6029358286390191390
      certificate := .residual 604170434734050
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1054
      code := 3713030747899653150
      certificate := .residual 1171932374908513
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5406
      code := 3858839165658128670
      certificate := .residual 2315224306631269
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5662
      code := 8229569156284473630
      certificate := .residual 1086364398169008
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 31
      code := 5155446065292913950
      certificate := .residual 4411689737676936
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 799
      code := 8262299143542170910
      certificate := .residual 4347907321983233
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1055
      code := 5131169850288860190
      certificate := .residual 186890244864626
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5407
      code := 3284630213168390430
      certificate := .residual 3035658830072514
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5663
      code := 3858262609255522590
      certificate := .residual 2425398472718370
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
