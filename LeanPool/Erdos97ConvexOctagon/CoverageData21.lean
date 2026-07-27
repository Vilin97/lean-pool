/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 168–175 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets21 : Array (List PatternEntry) := #[
  [
    { origin := 424
      mask := 145138297339904
      certificate := .k4 2 [2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2216
      mask := 3474747736396398592
      certificate := .k4 4 [4, 7, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4520
      mask := 22170623346974
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5032
      mask := 2814751177982238
      certificate := .k4 0 [0, 1, 6, 3, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 169
      mask := 38562071818338304
      certificate := .sharedThree 2 6 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 425
      mask := 145839921037312
      certificate := .k4 2 [2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2217
      mask := 3571849009859395584
      certificate := .k4 4 [4, 6, 7, 5] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3753
      mask := 11613042903115786
      certificate := .k4 0 [0, 3, 6, 5, 1] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4009
      mask := 731914107002871808
      certificate := .k4 1 [1, 7, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4777
      mask := 142936606679306
      certificate := .k4 0 [0, 1, 3, 5, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7081
      mask := 12191831605395738
      certificate := .k4 0 [0, 1, 6, 5, 4] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 170
      mask := 38562660219879424
      certificate := .sharedThree 4 6 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 426
      mask := 147334566683648
      certificate := .k4 1 [1, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 682
      mask := 3602880397681139712
      certificate := .k4 1 [1, 7, 4] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1450
      mask := 12094628113422
      certificate := .k4 0 [0, 2, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2218
      mask := 3576229326745501696
      certificate := .k4 4 [4, 5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4010
      mask := 731914107539742720
      certificate := .k4 1 [1, 7, 3, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4266
      mask := 4794363278362984714
      certificate := .k4 0 [0, 1, 3, 7, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4522
      mask := 22170673676318
      certificate := .k4 0 [0, 2, 3, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7082
      mask := 12384899566756110
      certificate := .k4 0 [0, 1, 2, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 171
      mask := 38712704902365184
      certificate := .sharedThree 5 6 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 427
      mask := 147334568649728
      certificate := .k4 1 [1, 5, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 683
      mask := 3603023334192709632
      certificate := .k4 4 [4, 7, 5] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 939
      mask := 19972403243008
      certificate := .k4 1 [1, 5, 4, 3] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1451
      mask := 12094630600974
      certificate := .k4 0 [0, 1, 2, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2987
      mask := 2814750858234894
      certificate := .k4 0 [0, 2, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4011
      mask := 792633536590021646
      certificate := .k4 0 [0, 3, 7, 1, 2] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5291
      mask := 9663629171376406
      certificate := .k4 0 [0, 1, 4, 6, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7083
      mask := 12384899566822666
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9899
      mask := 2892931643075486734
      certificate := .k4 0 [0, 3, 7, 5, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10667
      mask := 4945023880594990358
      certificate := .k4 0 [0, 1, 4, 2, 7, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 940
      mask := 20903605838098
      certificate := .k4 0 [0, 1, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2988
      mask := 2814750875010318
      certificate := .k4 0 [0, 1, 2, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4524
      mask := 22170925334558
      certificate := .k4 0 [0, 2, 5, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7084
      mask := 12384899634323722
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10924
      mask := 2885263662928446486
      certificate := .k4 0 [0, 2, 4, 5, 7, 3, 6, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 173
      mask := 40813871632547840
      certificate := .sharedThree 2 6 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 429
      mask := 147334568779776
      certificate := .k4 1 [1, 5, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 685
      mask := 3746995044602609664
      certificate := .k4 2 [2, 4, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1197
      mask := 9590361324281856
      certificate := .k4 1 [1, 5, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1709
      mask := 2814750924753934
      certificate := .k4 0 [0, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1965
      mask := 14374327826800896
      certificate := .k4 1 [1, 6, 4, 5] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3245
      mask := 5911253684012054
      certificate := .k4 0 [0, 2, 4, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7085
      mask := 12384900068106510
      certificate := .k4 0 [0, 1, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 174
      mask := 40813874055741440
      certificate := .sharedThree 3 6 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 686
      mask := 3746995577178554368
      certificate := .k4 2 [2, 7, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1198
      mask := 9642716982027264
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1710
      mask := 2814750941529358
      certificate := .k4 0 [0, 1, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2222
      mask := 3603029830901170176
      certificate := .k4 3 [3, 5, 7, 4] 1 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3246
      mask := 5911253684978966
      certificate := .k4 0 [0, 1, 4, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3502
      mask := 10207865956688134
      certificate := .k4 0 [0, 1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4270
      mask := 4796615091011240210
      certificate := .k4 0 [0, 1, 4, 7, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6062
      mask := 23231528447006
      certificate := .k4 0 [0, 3, 4, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8622
      mask := 2450103333113331998
      certificate := .k4 0 [0, 1, 3, 7, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 175
      mask := 40973300809072640
      certificate := .sharedThree 5 6 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 431
      mask := 149536343851008
      certificate := .k4 2 [2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 687
      mask := 3746995594350034944
      certificate := .k4 2 [2, 4, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1711
      mask := 2814750958306318
      certificate := .k4 0 [0, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2735
      mask := 19971883149338
      certificate := .k4 0 [0, 3, 4, 5, 1] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6319
      mask := 158488599896338
      certificate := .k4 0 [0, 1, 4, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7087
      mask := 12384900118962438
      certificate := .k4 0 [0, 1, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets21 : Array (List HardEntry) := #[
  [
    { origin := 680
      code := 8694995735922566430
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 6, 5, 7] 1 0 2 5 6 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1192
      code := 7148788942262922270
      certificate := .residual 1557451065360065
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5544
      code := 4147065159672848670
      certificate := .residual 1743768118813285
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5800
      code := 8658053363130885150
      certificate := .residual 1006185302497203
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 681
      code := 7690126770580972830
      certificate := .residual 3917770616636806
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1193
      code := 3870992639705902110
      certificate := .residual 2124303467080368
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5545
      code := 3285751730938241310
      certificate := .residual 2965307265735362
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5801
      code := 3871005840320947230
      certificate := .residual 4346704731131392
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 682
      code := 8686829787667457310
      certificate := .residual 1200473168846675
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1194
      code := 2853406031337384990
      certificate := .residual 745345242176418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5546
      code := 3858839181567648030
      certificate := .residual 3598364165457602
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5802
      code := 3294545062482600990
      certificate := .residual 2300026473644256
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 683
      code := 8694980342994658590
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 2 1 5 6 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1195
      code := 5163823246521953310
      certificate := .residual 4386519886533905
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5547
      code := 3284630229077909790
      certificate := .residual 3483757257779013
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5803
      code := 2862199524024837150
      certificate := .residual 4058030306505510
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 684
      code := 8686254751860614430
      certificate := .hubPentagon 0 [0, 1, 2, 3, 5, 6, 4, 7] 0 1 2 4 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1196
      code := 3140070683872619550
      certificate := .residual 4408292418399749
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5548
      code := 6428199943587160350
      certificate := .residual 1479374686682706
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5804
      code := 6463102140822512670
      certificate := .residual 4410321790404999
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 685
      code := 5452902448340624670
      certificate := .residual 4395315711156500
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1197
      code := 2851840324900776990
      certificate := .residual 2516829114190386
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5549
      code := 6425956939866497310
      certificate := .residual 3598277794842311
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5805
      code := 3285751563637416990
      certificate := .residual 2300026473644257
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 686
      code := 5447619063275808030
      certificate := .residual 4395315711156499
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1198
      code := 3145366056426040350
      certificate := .residual 316285286000881
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5550
      code := 5564643511131889950
      certificate := .residual 2112843219198546
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5806
      code := 6428199776286336030
      certificate := .residual 329821925048562
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 687
      code := 6453032278568428830
      certificate := .residual 4209620647985318
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1199
      code := 2857909870174694430
      certificate := .residual 3755400116770066
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5551
      code := 6137730961761296670
      certificate := .residual 2745855209049682
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5807
      code := 2862131475133424670
      certificate := .residual 1076536984246195
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
