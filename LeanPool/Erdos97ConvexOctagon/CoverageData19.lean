/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 152–159 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets19 : Array (List PatternEntry) := #[
  [
    { origin := 152
      mask := 10414574759051264
      certificate := .sharedThree 3 6 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 664
      mask := 3026418952310923264
      certificate := .k4 1 [1, 7, 3] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 920
      mask := 18842021536018
      certificate := .k4 0 [0, 1, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1176
      mask := 6843534049017856
      certificate := .k4 3 [3, 4, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1688
      mask := 1688849865067534
      certificate := .k4 0 [0, 2, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4248
      mask := 3474677368994398208
      certificate := .k4 3 [3, 4, 6, 7, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 665
      mask := 3026561888822493184
      certificate := .k4 3 [3, 7, 5] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1433
      mask := 7697202159886
      certificate := .k4 0 [0, 1, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5785
      mask := 4724778795968495616
      certificate := .k4 3 [3, 4, 5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 154
      mask := 11540474045147392
      certificate := .sharedThree 1 6 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 922
      mask := 18846319706132
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1178
      mask := 6843807853182976
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2970
      mask := 2533275902102534
      certificate := .k4 0 [0, 2, 1, 3, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 155
      mask := 11540474047823872
      certificate := .sharedThree 2 6 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 411
      mask := 90580860297216
      certificate := .k4 1 [1, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 667
      mask := 3170534138283819008
      certificate := .k4 2 [2, 3, 7] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 923
      mask := 18850613624852
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4251
      mask := 4792392955699284992
      certificate := .k4 1 [1, 2, 6, 3, 7] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6555
      mask := 5077846217223168
      certificate := .k4 1 [1, 5, 6, 3, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8603
      mask := 1297037268292895006
      certificate := .k4 0 [0, 1, 3, 7, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 156
      mask := 11540650138796032
      certificate := .sharedThree 4 6 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 412
      mask := 92651041849344
      certificate := .k4 2 [2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 924
      mask := 18850614607892
      certificate := .k4 0 [0, 4, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1180
      mask := 7036914162991128
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2204
      mask := 3458919167006605312
      certificate := .k4 2 [2, 5, 7, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2972
      mask := 2533275936113926
      certificate := .k4 0 [0, 1, 2, 3, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4252
      mask := 4792392955732708352
      certificate := .k4 1 [1, 3, 6, 2, 7] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4508
      mask := 22131969101086
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5276
      mask := 9654811687403790
      certificate := .k4 0 [0, 1, 3, 6, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6300
      mask := 153932241019142
      certificate := .k4 0 [0, 1, 2, 3, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8604
      mask := 1297037285489475870
      certificate := .k4 0 [0, 1, 2, 7, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 413
      mask := 92771300933632
      certificate := .k4 2 [2, 5, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 669
      mask := 3170534140422914048
      certificate := .k4 2 [2, 3, 7] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 925
      mask := 18864318447640
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1181
      mask := 7036914414649368
      certificate := .k4 0 [0, 4, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1437
      mask := 7855495192854
      certificate := .k4 0 [0, 1, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3997
      mask := 720585838701879562
      certificate := .k4 0 [0, 1, 7, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9885
      mask := 2892085019122682894
      certificate := .k4 0 [0, 2, 3, 7, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 158
      mask := 13792273862033408
      certificate := .sharedThree 2 6 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 414
      mask := 92788478705664
      certificate := .k4 2 [2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 926
      mask := 18868344979480
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1182
      mask := 7037153875853336
      certificate := .k4 0 [0, 3, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1438
      mask := 9896177380608
      certificate := .k4 1 [1, 2, 3, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2462
      mask := 3471155667226
      certificate := .k4 0 [0, 1, 3, 5, 4] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2718
      mask := 19937239311638
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5022
      mask := 1970376667168782
      certificate := .k4 0 [0, 3, 4, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6302
      mask := 153933827907854
      certificate := .k4 0 [0, 1, 2, 3, 5] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 159
      mask := 13792274680905728
      certificate := .sharedThree 3 6 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 415
      mask := 92788479754240
      certificate := .k4 2 [2, 5, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 671
      mask := 3170679275955159040
      certificate := .k4 3 [3, 7, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 927
      mask := 18868596637720
      certificate := .k4 0 [0, 4, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1183
      mask := 7037154932817944
      certificate := .k4 0 [0, 4, 6, 3] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1695
      mask := 1970324887325710
      certificate := .k4 0 [0, 3, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5279
      mask := 9658273347159318
      certificate := .k4 0 [0, 1, 6, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6559
      mask := 5085653597643782
      certificate := .k4 0 [0, 2, 1, 6, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets19 : Array (List HardEntry) := #[
  [
    { origin := 1176
      code := 5456328253332679710
      certificate := .residual 3915711179795969
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5528
      code := 6425956512181182750
      certificate := .residual 1479511857372754
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5784
      code := 3136569989188346910
      certificate := .residual 2468811968597073
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1177
      code := 2862191363117706270
      certificate := .residual 2694936613328176
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5529
      code := 6137730534075982110
      certificate := .residual 3795963163732108
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5785
      code := 5995919938294440990
      certificate := .residual 3772597165951377
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1178
      code := 3145366082195450910
      certificate := .residual 316285286000884
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5530
      code := 5563521581586243870
      certificate := .residual 2182905523662418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5786
      code := 6136095572114334750
      certificate := .residual 2470976698174548
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1179
      code := 8189454161454197790
      certificate := .residual 316285286000883
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5531
      code := 6136041709985521950
      certificate := .residual 1996314092958754
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5787
      code := 3716962188409758750
      certificate := .residual 3121394178987285
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1180
      code := 6172914892527528990
      certificate := .residual 3486425606329120
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5532
      code := 5993615346033680670
      certificate := .residual 1378528052763682
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5788
      code := 3714719184689095710
      certificate := .residual 3115892313298465
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1181
      code := 7185587263740472350
      certificate := .residual 3793512884687233
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5533
      code := 8230695039780184350
      certificate := .residual 1077585484994480
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5789
      code := 8252649692777210910
      certificate := .residual 1976230759296084
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1182
      code := 7176861672606428190
      certificate := .residual 3795692580776325
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5534
      code := 6168183730531918110
      certificate := .residual 935769794582448
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5790
      code := 3713021538970690590
      certificate := .residual 1976230759296081
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1183
      code := 6460844002744888350
      certificate := .residual 752132264057777
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5535
      code := 6453036381428179230
      certificate := .residual 3915951698029064
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5791
      code := 8182278732413199390
      certificate := .residual 3902339872237969
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
