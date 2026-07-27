/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 48–55 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets06 : Array (List PatternEntry) := #[
  [
    { origin := 48
      mask := 3503292416
      certificate := .sharedThree 2 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 304
      mask := 55918460956
      certificate := .k4 0 [0, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 560
      mask := 15763046177701888
      certificate := .k4 3 [3, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 816
      mask := 43234887962
      certificate := .k4 0 [0, 1, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1072
      mask := 3377700832691200
      certificate := .k4 1 [1, 2, 6, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1584
      mask := 88115556541440
      certificate := .k4 1 [1, 2, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4400
      mask := 7246314615316938752
      certificate := .k4 2 [2, 5, 7, 6, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 49
      mask := 3758153728
      certificate := .sharedThree 1 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 305
      mask := 56170119196
      certificate := .k4 0 [0, 4, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1329
      mask := 12464064959610880
      certificate := .k4 2 [2, 6, 3, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4145
      mask := 2450104432336281862
      certificate := .k4 0 [0, 1, 2, 7, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4657
      mask := 81364951198732
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 50
      mask := 3772776448
      certificate := .sharedThree 2 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 562
      mask := 15842210209595392
      certificate := .k4 4 [4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 818
      mask := 43251665178
      certificate := .k4 0 [0, 1, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3378
      mask := 9646015510701062
      certificate := .k4 0 [0, 2, 1, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4146
      mask := 2450104432336282630
      certificate := .k4 0 [0, 2, 1, 7, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8754
      mask := 5228679470189118750
      certificate := .k4 0 [0, 1, 3, 7, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 51
      mask := 60129542158
      certificate := .sharedThree 0 4 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 563
      mask := 15850561505067008
      certificate := .k4 3 [3, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3379
      mask := 9646015512667142
      certificate := .k4 0 [0, 2, 5, 6, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4147
      mask := 2450108830432928010
      certificate := .k4 0 [0, 1, 3, 7, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5683
      mask := 15842055591980032
      certificate := .k4 1 [1, 2, 4, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 52
      mask := 150326149120
      certificate := .sharedThree 2 4 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 564
      mask := 36591746985149440
      certificate := .k4 1 [1, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 820
      mask := 51624607772
      certificate := .k4 0 [0, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1076
      mask := 3377992119615488
      certificate := .k4 2 [2, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2100
      mask := 1297037272503321622
      certificate := .k4 0 [0, 4, 7, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2612
      mask := 12095234516230
      certificate := .k4 0 [0, 1, 5, 3, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3380
      mask := 9646015512731910
      certificate := .k4 0 [0, 1, 6, 5, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4404
      mask := 7531157673773891584
      certificate := .k4 2 [2, 6, 7, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9780
      mask := 1732197564016512030
      certificate := .k4 0 [0, 4, 7, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10548
      mask := 2889204587480350742
      certificate := .k4 0 [0, 4, 6, 3, 7, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 53
      mask := 150911057920
      certificate := .sharedThree 3 4 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 309
      mask := 155494907904
      certificate := .k4 2 [2, 3, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 821
      mask := 51625066524
      certificate := .k4 0 [0, 3, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1077
      mask := 3377993126248448
      certificate := .k4 2 [2, 4, 6, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1333
      mask := 13531010998231040
      certificate := .k4 1 [1, 5, 4, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2357
      mask := 21526744094
      certificate := .k4 0 [0, 3, 4, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4149
      mask := 2450117639360520466
      certificate := .k4 0 [0, 1, 4, 7, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 54
      mask := 158913799424
      certificate := .sharedThree 1 4 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 822
      mask := 51825410076
      certificate := .k4 0 [0, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1078
      mask := 3377993189163008
      certificate := .k4 2 [2, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1334
      mask := 13533081179783168
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2870
      mask := 844446410359062
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5686
      mask := 16116641725161754
      certificate := .k4 0 [0, 1, 3, 5, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 567
      mask := 36805052228231168
      certificate := .k4 1 [1, 5, 6] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 823
      mask := 51826393116
      certificate := .k4 0 [0, 3, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1079
      mask := 3378009299484672
      certificate := .k4 2 [2, 3, 6, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1591
      mask := 90447716311314
      certificate := .k4 0 [0, 1, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2871
      mask := 844446410359830
      certificate := .k4 0 [0, 4, 2, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5687
      mask := 16116680094654746
      certificate := .k4 0 [0, 1, 4, 5, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7735
      mask := 92531064988938
      certificate := .k4 0 [0, 1, 3, 2, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets06 : Array (List HardEntry) := #[
  [
    { origin := 48
      code := 8410690872108330270
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 7, 6] 0 1 2 5 7 6 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 816
      code := 4147062961727366430
      certificate := .residual 4189975189770273
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1072
      code := 6452484158910458910
      certificate := .residual 3652170878076454
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5424
      code := 3858839028756046110
      certificate := .residual 2112538780167762
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5680
      code := 6019017117765657630
      certificate := .residual 3512535048794918
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 49
      code := 6176905457452657950
      certificate := .hubPentagon 0 [0, 1, 2, 4, 3, 5, 7, 6] 0 1 2 7 4 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 817
      code := 3714723994569565470
      certificate := .residual 4193297348544533
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1073
      code := 6451358276183485470
      certificate := .residual 2316368651169888
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5425
      code := 3284630076266307870
      certificate := .residual 4350117082851468
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5681
      code := 5564709195337098270
      certificate := .residual 3794595216460167
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 50
      code := 6455288723430124830
      certificate := .residual 3911410038171667
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 818
      code := 3714161053206078750
      certificate := .residual 118598088034162
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1074
      code := 5155452660235791390
      certificate := .residual 2624568115565872
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5426
      code := 6428199790775558430
      certificate := .residual 2965185039579842
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5682
      code := 3858839152773227550
      certificate := .residual 2317464136286433
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 51
      code := 6032793555060337950
      certificate := .residual 709111550073811
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 819
      code := 5420526133700486430
      certificate := .residual 611299585722337
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1075
      code := 7180383273861934110
      certificate := .residual 3300931671773572
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5427
      code := 6141095314530689310
      certificate := .residual 2315359605441125
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5683
      code := 5564643482337469470
      certificate := .residual 347259562000626
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 52
      code := 6024064678276312350
      certificate := .residual 3724737840579622
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 820
      code := 6427636857809429790
      certificate := .residual 4189839890960417
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1076
      code := 3145158248256138270
      certificate := .residual 3361557312056833
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5428
      code := 5564643358320288030
      certificate := .residual 3598608540748482
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5684
      code := 3726892852872668190
      certificate := .residual 3361542279613952
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 53
      code := 8256604219807837470
      certificate := .residual 3911410038171668
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 821
      code := 5996980143442126110
      certificate := .residual 4194259424888853
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1077
      code := 5446477755433774110
      certificate := .residual 316422467528948
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5429
      code := 6137730808949694750
      certificate := .residual 4231665620502210
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5685
      code := 3726884031244723230
      certificate := .residual 2317584399040736
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 54
      code := 7685068156178607390
      certificate := .residual 4411569478585475
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 822
      code := 3139951963814257950
      certificate := .residual 620078509885409
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1078
      code := 8190295425286302750
      certificate := .residual 316422467528947
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5430
      code := 5563521856459956510
      certificate := .residual 4038048494102341
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5686
      code := 3726877459944760350
      certificate := .residual 2949722519647014
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 55
      code := 8406750222435298590
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 7, 6] 1 0 2 5 6 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 823
      code := 5996977953008805150
      certificate := .residual 127256749442930
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1079
      code := 6164258437479951390
      certificate := .residual 4409479976808715
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5431
      code := 2852284537808544030
      certificate := .residual 1995216640734242
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5687
      code := 3292511242470220830
      certificate := .residual 3302014003546503
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
