/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 248–255 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets31 : Array (List PatternEntry) := #[
  [
    { origin := 248
      mask := 51052558
      certificate := .k4 0 [0, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 760
      mask := 7034975561185230848
      certificate := .k4 5 [5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4088
      mask := 1441171276841418772
      certificate := .k4 0 [0, 2, 7, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4344
      mask := 5803170454122266648
      certificate := .k4 0 [0, 3, 4, 7, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 249
      mask := 83889422
      certificate := .k4 0 [0, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 761
      mask := 7035045929929408512
      certificate := .k4 5 [5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1529
      mask := 27488347553820
      certificate := .k4 0 [0, 2, 3, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1785
      mask := 6755688579596314
      certificate := .k4 0 [0, 4, 6, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2041
      mask := 41658588620571648
      certificate := .k4 1 [1, 2, 4, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2297
      mask := 5372795191126130688
      certificate := .k4 3 [3, 7, 6, 4] 1 3 4 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 250
      mask := 100666638
      certificate := .k4 0 [0, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 762
      mask := 7061716783484428288
      certificate := .k4 1 [1, 5, 7] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1018
      mask := 1761417629950976
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1274
      mask := 10770815910028288
      certificate := .k4 1 [1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1786
      mask := 6755692924895260
      certificate := .k4 0 [0, 3, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2042
      mask := 41658850617655316
      certificate := .k4 0 [0, 2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2554
      mask := 9896211456262
      certificate := .k4 0 [0, 1, 2, 3, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2810
      mask := 26535130040602
      certificate := .k4 0 [0, 1, 3, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3578
      mask := 10221481002951680
      certificate := .k4 1 [1, 2, 6, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4090
      mask := 1441178460777086976
      certificate := .k4 2 [2, 4, 7, 5, 3] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5114
      mask := 5066875998912798
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5626
      mask := 14074028014839058
      certificate := .k4 0 [0, 1, 4, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5882
      mask := 11008556016670
      certificate := .k4 0 [0, 3, 4, 5, 1, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7418
      mask := 2882446700193590286
      certificate := .k4 0 [0, 2, 3, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8442
      mask := 13583645906316318
      certificate := .k4 0 [0, 3, 4, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10746
      mask := 5809716641126755358
      certificate := .k4 0 [0, 2, 4, 7, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 251
      mask := 101384206
      certificate := .k4 0 [0, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 763
      mask := 7071214364925157376
      certificate := .k4 1 [1, 6, 7] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1019
      mask := 1761417634014208
      certificate := .k4 1 [1, 5, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1531
      mask := 27488663699484
      certificate := .k4 0 [0, 2, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2043
      mask := 41658867796475924
      certificate := .k4 0 [0, 2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5115
      mask := 5066875999895838
      certificate := .k4 0 [0, 1, 6, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6907
      mask := 10696050746731786
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 252
      mask := 117441806
      certificate := .k4 0 [0, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 508
      mask := 10696049117258752
      certificate := .k4 1 [1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 764
      mask := 7205834170598162432
      certificate := .k4 2 [2, 5, 7] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1020
      mask := 1761417634128896
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1276
      mask := 11269995292026880
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1788
      mask := 6755718392709146
      certificate := .k4 0 [0, 3, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2044
      mask := 41659125491367956
      certificate := .k4 0 [0, 2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2300
      mask := 5512968896103105536
      certificate := .k4 1 [1, 6, 7, 3] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6652
      mask := 6768896143654912
      certificate := .k4 2 [2, 5, 3, 6, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8188
      mask := 9658299117551902
      certificate := .k4 0 [0, 1, 2, 6, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8700
      mask := 3458980572154717458
      certificate := .k4 0 [0, 1, 4, 2, 7, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 253
      mask := 117443598
      certificate := .k4 0 [0, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 509
      mask := 10696049121321984
      certificate := .k4 1 [1, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2045
      mask := 41659142670188564
      certificate := .k4 0 [0, 2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6653
      mask := 6768913122721792
      certificate := .k4 2 [2, 5, 3, 6, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8445
      mask := 13583658708905230
      certificate := .k4 0 [0, 1, 5, 6, 4, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 254
      mask := 117637134
      certificate := .k4 0 [0, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 510
      mask := 10696049121436672
      certificate := .k4 1 [1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 766
      mask := 7494068948539801600
      certificate := .k4 3 [3, 5, 7] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1022
      mask := 1763616653206528
      certificate := .k4 1 [1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1534
      mask := 27629524625690
      certificate := .k4 0 [0, 1, 4, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2046
      mask := 42784754017239064
      certificate := .k4 0 [0, 3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4094
      mask := 1445937797188878356
      certificate := .k4 0 [0, 2, 7, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 11006
      mask := 6955968109859048718
      certificate := .k4 0 [0, 1, 3, 6, 7, 5, 4, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 255
      mask := 118095886
      certificate := .k4 0 [0, 3, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 511
      mask := 10696049121452032
      certificate := .k4 1 [1, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 767
      mask := 7505248782771027968
      certificate := .k4 3 [3, 6, 7] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1023
      mask := 1763616657269760
      certificate := .k4 1 [1, 6, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1279
      mask := 11269995828895744
      certificate := .k4 1 [1, 5, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1535
      mask := 27629527302172
      certificate := .k4 0 [0, 2, 4, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1791
      mask := 6755731294388252
      certificate := .k4 0 [0, 4, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2047
      mask := 42784788108541976
      certificate := .k4 0 [0, 3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets31 : Array (List HardEntry) := #[
  [
    { origin := 760
      code := 4149444092129076510
      certificate := .residual 1253507433520946
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1016
      code := 6459803068812979230
      certificate := .residual 809648111079360
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1272
      code := 6166509996778613790
      certificate := .residual 3916658220028288
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5368
      code := 5599269331305488670
      certificate := .residual 4410712632558850
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5624
      code := 3290611142553166110
      certificate := .residual 3361797830289929
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 761
      code := 7654379448547042590
      certificate := .residual 3746484032924304
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1017
      code := 4158165829014481950
      certificate := .residual 809649993797568
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1273
      code := 6164258179986385950
      certificate := .residual 2317466015335520
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5369
      code := 6453032276488085790
      certificate := .residual 952245289309104
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5625
      code := 7794492519778279710
      certificate := .residual 261950678876656
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 762
      code := 3140515171461653790
      certificate := .residual 711911373568977
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1018
      code := 5420581203999943710
      certificate := .residual 3271614728478994
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1274
      code := 6163132297259412510
      certificate := .residual 3581804281346598
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5370
      code := 8398467607022526750
      certificate := .residual 3918131393955074
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5626
      code := 3294477184635429150
      certificate := .residual 3301172189950210
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 763
      code := 8659233020960728350
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 6, 7] 0 1 2 4 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1019
      code := 3145018745552071710
      certificate := .residual 3764195941392658
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1275
      code := 5420594007302630430
      certificate := .residual 3794715475545351
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5371
      code := 5591718573949313310
      certificate := .residual 952243380900784
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5627
      code := 4149308025956655390
      certificate := .residual 3035328084166343
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 764
      code := 7678023588938016030
      certificate := .residual 4409615268393217
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1020
      code := 8190590077489474590
      certificate := .residual 3300119923025414
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1276
      code := 3714161023375272990
      certificate := .residual 2317466015335521
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5372
      code := 6164801900303212830
      certificate := .residual 4408547969025545
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5628
      code := 3862203549711786270
      certificate := .residual 2745870245105234
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 765
      code := 5446484326750905630
      certificate := .residual 113169553246065
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1021
      code := 8192689607827614750
      certificate := .residual 1338878243561043
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1277
      code := 5420526103869680670
      certificate := .residual 347261441049714
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5373
      code := 5590592947813474590
      certificate := .residual 4408547969025544
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5629
      code := 4147065022235992350
      certificate := .residual 1549726265671250
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 766
      code := 3138398451255502110
      certificate := .residual 596611038423010
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1022
      code := 8189173906731002910
      certificate := .residual 307643554354419
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1278
      code := 3871005833376721950
      certificate := .residual 3362504352289152
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5374
      code := 6173458492787646750
      certificate := .residual 208057789389296
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5630
      code := 3285751593501384990
      certificate := .residual 3302419878086796
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 767
      code := 3138395165605520670
      certificate := .residual 4410727664945285
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1023
      code := 8192832944308055070
      certificate := .residual 3792701135939078
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1279
      code := 3870997020305157150
      certificate := .residual 2317586278089824
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5375
      code := 6164801626499047710
      certificate := .residual 3915966730421768
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5631
      code := 3284630091641053470
      certificate := .residual 2042476604154450
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
