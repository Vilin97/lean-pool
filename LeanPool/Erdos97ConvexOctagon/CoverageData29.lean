/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 232–239 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets29 : Array (List PatternEntry) := #[
  [
    { origin := 232
      mask := 7205759405470515200
      certificate := .sharedThree 3 7 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 488
      mask := 9570149214610432
      certificate := .k4 1 [1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 744
      mask := 5945315291306131456
      certificate := .k4 4 [4, 7, 6] 1 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1768
      mask := 5629787302395926
      certificate := .k4 0 [0, 4, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4072
      mask := 1310636285718749184
      certificate := .k4 1 [1, 7, 4, 6, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4328
      mask := 5228960684246564888
      certificate := .k4 0 [0, 3, 4, 7, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4584
      mask := 74766881546506
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10984
      mask := 5809716671493514510
      certificate := .k4 0 [0, 1, 2, 5, 6, 7, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 489
      mask := 9570150852356096
      certificate := .k4 1 [1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2025
      mask := 39406498983510028
      certificate := .k4 0 [0, 2, 3, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 234
      mask := 7493989779944531968
      certificate := .sharedThree 1 7 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 746
      mask := 6052838191257354240
      certificate := .k4 2 [2, 4, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1002
      mask := 1407654061735956
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1258
      mask := 10216663188766720
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1514
      mask := 23231478113558
      certificate := .k4 0 [0, 1, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2282
      mask := 5229805070779416576
      certificate := .k4 2 [2, 6, 7, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4330
      mask := 5231010547297681408
      certificate := .k4 3 [3, 5, 7, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 747
      mask := 6052838723833298944
      certificate := .k4 2 [2, 7, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1003
      mask := 1407666946637844
      certificate := .k4 0 [0, 2, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1515
      mask := 23232098861084
      certificate := .k4 0 [0, 3, 4, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1771
      mask := 5629808777691164
      certificate := .k4 0 [0, 2, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4331
      mask := 5233756715295467520
      certificate := .k4 1 [1, 5, 6, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7403
      mask := 2594216321969368078
      certificate := .k4 0 [0, 2, 3, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7915
      mask := 2814776913772830
      certificate := .k4 0 [0, 1, 2, 6, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 236
      mask := 7493990226621104128
      certificate := .sharedThree 4 7 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 748
      mask := 6052838741004779520
      certificate := .k4 2 [2, 4, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1260
      mask := 10216663658528768
      certificate := .k4 2 [2, 5, 3, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1772
      mask := 5629813072592924
      certificate := .k4 0 [0, 4, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2284
      mask := 5233182770796193792
      certificate := .k4 1 [1, 3, 7, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4332
      mask := 5234321864278933504
      certificate := .k4 2 [2, 5, 6, 7, 3] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6124
      mask := 72984386741522
      certificate := .k4 0 [0, 1, 4, 2, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8684
      mask := 3458908004383534110
      certificate := .k4 0 [0, 2, 4, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9964
      mask := 4800916368251912462
      certificate := .k4 0 [0, 1, 2, 7, 6, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 493
      mask := 9660730068434944
      certificate := .k4 4 [4, 5, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 749
      mask := 6052838741012119552
      certificate := .k4 2 [2, 7, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1773
      mask := 5629825956511772
      certificate := .k4 0 [0, 2, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2285
      mask := 5233182770836537344
      certificate := .k4 2 [2, 3, 7, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4333
      mask := 5235507137270016000
      certificate := .k4 1 [1, 5, 6, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8685
      mask := 3458908004466830366
      certificate := .k4 0 [0, 3, 4, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 238
      mask := 8070450532255268864
      certificate := .sharedThree 2 7 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 494
      mask := 9854922719781120
      certificate := .k4 1 [1, 5, 6] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 750
      mask := 6089993437925343232
      certificate := .k4 4 [4, 7, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1262
      mask := 10221352156921856
      certificate := .k4 2 [2, 4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1774
      mask := 5629830251413532
      certificate := .k4 0 [0, 4, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2286
      mask := 5233183217707646976
      certificate := .k4 3 [3, 4, 7, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2542
      mask := 9896158505998
      certificate := .k4 0 [0, 2, 3, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4334
      mask := 5235509336300060672
      certificate := .k4 2 [2, 5, 6, 7, 3] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8686
      mask := 3458908051628171550
      certificate := .k4 0 [0, 1, 2, 5, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9966
      mask := 4800916381337944346
      certificate := .k4 0 [0, 1, 4, 7, 6, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 239
      mask := 8070450534126977024
      certificate := .sharedThree 3 7 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 495
      mask := 9923092440703232
      certificate := .k4 1 [1, 6, 5] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 751
      mask := 6093370295845912576
      certificate := .k4 2 [2, 7, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1007
      mask := 1688850972298240
      certificate := .k4 1 [1, 3, 6, 2] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1519
      mask := 23279007957020
      certificate := .k4 0 [0, 3, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2287
      mask := 5233745720716060672
      certificate := .k4 1 [1, 6, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2543
      mask := 9896160535822
      certificate := .k4 0 [0, 1, 3, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4335
      mask := 5235522977109377024
      certificate := .k4 3 [3, 7, 6, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4847
      mask := 149534145750028
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6127
      mask := 74768420400140
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets29 : Array (List HardEntry) := #[
  [
    { origin := 744
      code := 7689008565333484830
      certificate := .residual 3362519384732035
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1000
      code := 6172702974236912670
      certificate := .residual 739416805833664
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1256
      code := 4158101496566737950
      certificate := .residual 1561370693492400
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5608
      code := 3285751302718152990
      certificate := .residual 2182920559717970
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 745
      code := 5446497559543768350
      certificate := .residual 158131447544564
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1001
      code := 3871065734438415390
      certificate := .residual 739418688551872
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1257
      code := 3140514888198220830
      certificate := .residual 815713717961634
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5609
      code := 3858838753347559710
      certificate := .residual 2605289118851666
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 746
      code := 8263217235462677790
      certificate := .residual 3362504352289155
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1002
      code := 5159386478491560990
      certificate := .residual 174712139397489
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1258
      code := 3148677529412398110
      certificate := .residual 3302014003546498
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5610
      code := 6428199515367072030
      certificate := .residual 4161283991128770
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 747
      code := 6020706229672961310
      certificate := .residual 158116415101684
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1003
      code := 5168043070975994910
      certificate := .residual 1140736403799778
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1259
      code := 4148742861646556190
      certificate := .residual 2747106658840658
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5611
      code := 6141095039122202910
      certificate := .residual 2912165811693381
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 748
      code := 5446497533774357790
      certificate := .residual 158131447544561
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1004
      code := 5445930199528074270
      certificate := .residual 782651904673744
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1260
      code := 3718086147279252510
      certificate := .residual 4240235966133447
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5612
      code := 6425956511646408990
      certificate := .residual 2297906932433509
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 749
      code := 8697231858341602590
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 5 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1005
      code := 5159377661141806110
      certificate := .residual 307643554354420
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1261
      code := 3141634191068851230
      certificate := .residual 917676477322194
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5613
      code := 5564643082911801630
      certificate := .residual 3105903200847554
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 750
      code := 6455283802471752990
      certificate := .residual 2471465258043600
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1006
      code := 5159377652585425950
      certificate := .residual 307643554354417
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1262
      code := 3714160890768092190
      certificate := .residual 2113500852842962
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5614
      code := 6137730533541208350
      certificate := .residual 3528272008854210
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 751
      code := 7680143312584008990
      certificate := .residual 1166830687567330
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1007
      code := 5452051305548835870
      certificate := .residual 2437683589634610
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1263
      code := 3139951938278353950
      certificate := .residual 4350102050465036
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5615
      code := 3862196687628591390
      certificate := .residual 1996449391768610
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
