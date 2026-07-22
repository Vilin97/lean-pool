/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 0–7 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets00 : Array (List PatternEntry) := #[
  [
    { origin := 0
      mask := 7196
      certificate := .sharedThree 0 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 768
      mask := 8070539455250825216
      certificate := .k4 4 [4, 5, 7] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1280
      mask := 11272194355625984
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2048
      mask := 42785027821404184
      certificate := .k4 0 [0, 3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4096
      mask := 1447907609914900480
      certificate := .k4 2 [2, 4, 7, 6, 3] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6656
      mask := 6777829138759680
      certificate := .k4 2 [2, 5, 4, 6, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1
      mask := 1703962
      certificate := .sharedThree 0 2 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 257
      mask := 286851100
      certificate := .k4 0 [0, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 513
      mask := 10770815905719296
      certificate := .k4 1 [1, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 769
      mask := 8083962293202714624
      certificate := .k4 4 [4, 6, 7] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1793
      mask := 7036875513593884
      certificate := .k4 0 [0, 2, 3, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2049
      mask := 42785061912707096
      certificate := .k4 0 [0, 3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2305
      mask := 5802326003142492160
      certificate := .k4 2 [2, 6, 7, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2817
      mask := 26547998752796
      certificate := .k4 0 [0, 2, 4, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6657
      mask := 6777846117826560
      certificate := .k4 2 [2, 5, 4, 6, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 514
      mask := 11259000712620032
      certificate := .k4 1 [1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 770
      mask := 50922766
      certificate := .k4 0 [0, 1, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1026
      mask := 1970324837187846
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1282
      mask := 11272194890399744
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1794
      mask := 7036875793500442
      certificate := .k4 0 [0, 1, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2050
      mask := 45108564053910528
      certificate := .k4 1 [1, 2, 5, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4610
      mask := 76965868563468
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8450
      mask := 13583693067657502
      certificate := .k4 0 [0, 1, 2, 5, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8706
      mask := 4792955903720063262
      certificate := .k4 0 [0, 1, 3, 7, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 771
      mask := 50924558
      certificate := .k4 0 [0, 2, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1027
      mask := 1970324837188614
      certificate := .k4 0 [0, 2, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1539
      mask := 27676770369564
      certificate := .k4 0 [0, 2, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1795
      mask := 7036875827642396
      certificate := .k4 0 [0, 2, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2819
      mask := 26560699629596
      certificate := .k4 0 [0, 2, 3, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4355
      mask := 5805140522122608640
      certificate := .k4 2 [2, 3, 4, 7, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6659
      mask := 7036875513660702
      certificate := .k4 0 [0, 1, 3, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 772
      mask := 50988302
      certificate := .k4 0 [0, 1, 3, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1028
      mask := 1970324841235718
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1284
      mask := 11285698464186368
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6148
      mask := 79165430787084
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6660
      mask := 7036875547216924
      certificate := .k4 0 [0, 3, 1, 6, 2] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7428
      mask := 4792955903484264718
      certificate := .k4 0 [0, 1, 3, 7, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8708
      mask := 4792955942089556254
      certificate := .k4 0 [0, 1, 4, 7, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 261
      mask := 337182748
      certificate := .k4 0 [0, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 517
      mask := 11340362928908288
      certificate := .k4 1 [1, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 773
      mask := 50990094
      certificate := .k4 0 [0, 3, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1029
      mask := 1970324841251846
      certificate := .k4 0 [0, 2, 6, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1285
      mask := 11285801543401472
      certificate := .k4 3 [3, 5, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1541
      mask := 72569485535232
      certificate := .k4 1 [1, 3, 5, 2] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1797
      mask := 7037153595424796
      certificate := .k4 0 [0, 2, 4, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4101
      mask := 1513210028855821334
      certificate := .k4 0 [0, 4, 7, 2, 1] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4357
      mask := 5805791526348939264
      certificate := .k4 1 [1, 6, 7, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6149
      mask := 79165464928522
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9221
      mask := 5922249353749534
      certificate := .k4 0 [0, 3, 4, 5, 6, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9989
      mask := 4940472293295006982
      certificate := .k4 0 [0, 1, 2, 7, 6, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 6
      mask := 6381824
      certificate := .sharedThree 1 2 0 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 262
      mask := 353435676
      certificate := .k4 0 [0, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 518
      mask := 11342561958952960
      certificate := .k4 2 [2, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1030
      mask := 1970324841301254
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1286
      mask := 11285835366268928
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1542
      mask := 72997271643136
      certificate := .k4 1 [1, 2, 5, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4102
      mask := 1513210031070773276
      certificate := .k4 0 [0, 4, 7, 2, 3] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4358
      mask := 5806354484898562048
      certificate := .k4 2 [2, 6, 7, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4870
      mask := 150242816163864
      certificate := .k4 0 [0, 3, 4, 5, 2] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6662
      mask := 7037153590856734
      certificate := .k4 0 [0, 2, 4, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7430
      mask := 4792955916319359254
      certificate := .k4 0 [0, 1, 4, 7, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 7
      mask := 6842368
      certificate := .sharedThree 1 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 263
      mask := 353894428
      certificate := .k4 0 [0, 3, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 519
      mask := 11356202768269312
      certificate := .k4 4 [4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 775
      mask := 84085774
      certificate := .k4 0 [0, 2, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1031
      mask := 1970324841316614
      certificate := .k4 0 [0, 1, 6, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1799
      mask := 7037200836395036
      certificate := .k4 0 [0, 2, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4359
      mask := 5807480403589595136
      certificate := .k4 3 [3, 6, 7, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets00 : Array (List HardEntry) := #[
  [
    { origin := 0
      code := 8697799730556775710
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 1 3 5 7 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 768
      code := 6020701831342613790
      certificate := .residual 104390639921009
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1024
      code := 8153717281279011870
      certificate := .residual 1339015425089107
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1280
      code := 3870992639438515230
      certificate := .residual 3018991752198694
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5376
      code := 5590592674009309470
      certificate := .residual 3915966730421769
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5632
      code := 6428199806150304030
      certificate := .residual 1734974158594661
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1
      code := 8697795349690133790
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 2 0 1 5 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 769
      code := 3717101826386453790
      certificate := .residual 605269692606434
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1025
      code := 8190575647154334750
      certificate := .residual 307506372826355
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1281
      code := 3148396054435752990
      certificate := .residual 3302134262631687
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5377
      code := 7824238863525208350
      certificate := .residual 199278788155888
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5633
      code := 6141095329905434910
      certificate := .residual 3035551636309698
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 2
      code := 8410689778228604190
      certificate := .residual 4411689737676934
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 770
      code := 8256726681708422430
      certificate := .residual 4409479976808705
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1026
      code := 5418893192665328670
      certificate := .residual 3746517855920788
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1282
      code := 3139951933983452190
      certificate := .residual 347141178295410
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5378
      code := 5599249129591660830
      certificate := .residual 208055910283760
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5634
      code := 6425956802429640990
      certificate := .residual 4231650588109506
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 3
      code := 8693859081117707550
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 6 5 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 771
      code := 3717098527901902110
      certificate := .residual 4411689737676933
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1027
      code := 5418892097448668190
      certificate := .residual 3746517855920785
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1283
      code := 5996977923177999390
      certificate := .residual 2317586278089825
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5379
      code := 8398447679112864030
      certificate := .residual 199276909050352
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5635
      code := 5564643373695033630
      certificate := .residual 2920824465876805
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 4
      code := 7397959300637994270
      certificate := .residual 4411689737676931
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 772
      code := 7652624885687543070
      certificate := .residual 4189839890960416
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1028
      code := 3145293499375119390
      certificate := .residual 3253936643007124
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1284
      code := 5158251776292449310
      certificate := .residual 3893577870611859
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5380
      code := 3865946433514103070
      certificate := .residual 1013831082619824
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5636
      code := 5563521871834702110
      certificate := .residual 3528256976411330
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 5
      code := 7684223732869704990
      certificate := .residual 4349139977733382
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 773
      code := 8226825029383906590
      certificate := .residual 4251412542173216
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1029
      code := 3145012028693376030
      certificate := .residual 3253936643007121
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1285
      code := 5452051303426452510
      certificate := .residual 4408292418399751
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5381
      code := 3862342896896958750
      certificate := .residual 4350102050465026
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5637
      code := 3141636414015463710
      certificate := .residual 1441062780320802
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 6
      code := 8693009180154604830
      certificate := .residual 155917796596467
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 774
      code := 7690130066659042590
      certificate := .residual 3916673252471171
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1030
      code := 4158170209613736990
      certificate := .residual 4317250646643984
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1286
      code := 5163820944454609950
      certificate := .residual 3884919216541330
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5382
      code := 7798428910396104990
      certificate := .residual 3364939598947586
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5638
      code := 3285736200573477150
      certificate := .residual 2489030601069602
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 7
      code := 7399917398290279710
      certificate := .residual 4411689737676932
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 775
      code := 3150432644676936990
      certificate := .residual 157994266016500
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1031
      code := 3871062447718886430
      certificate := .hubPentagon 0 [0, 2, 3, 4, 1, 5, 7, 6] 0 1 2 7 4 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1287
      code := 2858261605449231390
      certificate := .residual 3331727417808275
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5383
      code := 4154172000913056030
      certificate := .residual 1013834873746352
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5639
      code := 7653121739334017310
      certificate := .residual 1076505035839408
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
