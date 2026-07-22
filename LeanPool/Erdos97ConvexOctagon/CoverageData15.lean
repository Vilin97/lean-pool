/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 120–127 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets15 : Array (List PatternEntry) := #[
  [
    { origin := 120
      mask := 146237277863936
      certificate := .sharedThree 3 5 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 632
      mask := 1513209474805989396
      certificate := .k4 0 [0, 2, 7] 0 2 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1144
      mask := 5629827295477760
      certificate := .k4 2 [2, 4, 3, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1656
      mask := 158484304929792
      certificate := .k4 1 [1, 2, 4, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6008
      mask := 20890808492318
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 121
      mask := 146806277144576
      certificate := .sharedThree 4 5 0 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 633
      mask := 1513210046027137044
      certificate := .k4 0 [0, 4, 7] 0 2 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1145
      mask := 5629827298623488
      certificate := .k4 2 [2, 6, 4, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1401
      mask := 353502494
      certificate := .k4 0 [0, 1, 3, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5753
      mask := 2424488010436453376
      certificate := .k4 1 [1, 2, 5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6009
      mask := 20891593941278
      certificate := .k4 0 [0, 1, 2, 5, 3] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 634
      mask := 1801439853380894744
      certificate := .k4 0 [0, 3, 7] 0 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1146
      mask := 5704420951064576
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3962
      mask := 432351061796364550
      certificate := .k4 0 [0, 1, 7, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4218
      mask := 2896034912622608384
      certificate := .k4 3 [3, 7, 5, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5242
      mask := 9570170690494738
      certificate := .k4 0 [0, 1, 4, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 123
      mask := 150633101983744
      certificate := .sharedThree 2 5 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 379
      mask := 21041044783122
      certificate := .k4 0 [0, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 635
      mask := 1801440439358717976
      certificate := .k4 0 [0, 4, 7] 0 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3195
      mask := 5348316620539142
      certificate := .k4 0 [0, 1, 6, 4, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4219
      mask := 2898225002077749248
      certificate := .k4 3 [3, 4, 7, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 124
      mask := 151221503524864
      certificate := .sharedThree 4 5 0 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 380
      mask := 23089747394580
      certificate := .k4 0 [0, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 636
      mask := 2423430280246198272
      certificate := .k4 5 [5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 892
      mask := 12094678245642
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1148
      mask := 5704695824777216
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1404
      mask := 21476412702
      certificate := .k4 0 [0, 1, 4, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2172
      mask := 2882451098826714112
      certificate := .k4 1 [1, 5, 7, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2428
      mask := 51875808542
      certificate := .k4 0 [0, 1, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 381
      mask := 23248657973268
      certificate := .k4 0 [0, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 637
      mask := 2449958197300208640
      certificate := .k4 1 [1, 2, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 893
      mask := 12094678247434
      certificate := .k4 0 [0, 3, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1405
      mask := 21593456670
      certificate := .k4 0 [0, 3, 4, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 126
      mask := 159429195530240
      certificate := .sharedThree 2 5 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 382
      mask := 27488612778008
      certificate := .k4 0 [0, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1150
      mask := 5717615090597888
      certificate := .k4 2 [2, 4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1406
      mask := 26089685022
      certificate := .k4 0 [0, 2, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4222
      mask := 3458911440357883924
      certificate := .k4 0 [0, 2, 4, 7, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7038
      mask := 11350260412588314
      certificate := .k4 0 [0, 1, 5, 6, 3] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 127
      mask := 159431618723840
      certificate := .sharedThree 3 5 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 383
      mask := 27663884353560
      certificate := .k4 0 [0, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 895
      mask := 12095181563914
      certificate := .k4 0 [0, 3, 5, 1] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1663
      mask := 161091338412306
      certificate := .k4 0 [0, 1, 4, 5] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2175
      mask := 2882466492194488320
      certificate := .k4 2 [2, 5, 7, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3199
      mask := 5629783007364374
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3967
      mask := 433189989170398214
      certificate := .k4 0 [0, 2, 7, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4991
      mask := 167822105813258
      certificate := .k4 0 [0, 1, 3, 5, 4] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5247
      mask := 9570604759933194
      certificate := .k4 0 [0, 1, 3, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets15 : Array (List HardEntry) := #[
  [
    { origin := 1144
      code := 7149908365073280030
      certificate := .residual 1886795562547506
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5496
      code := 8686693566026277150
      certificate := .residual 3917034029789442
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5752
      code := 4149307722823296030
      certificate := .residual 2308925686251745
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1145
      code := 5996973786585984030
      certificate := .residual 1342760365907409
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5497
      code := 6455296733343310110
      certificate := .residual 3915816406444552
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5753
      code := 6137730521191080990
      certificate := .residual 338360298012914
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1146
      code := 4158097218777738270
      certificate := .residual 4348869394664715
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5498
      code := 6168192257098440990
      certificate := .residual 3915816406444553
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5754
      code := 5442556364409922590
      certificate := .residual 3885022564084371
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1147
      code := 3870922648666598430
      certificate := .residual 3608201016170016
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5499
      code := 3860667132533203230
      certificate := .residual 349873322198512
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5755
      code := 5417224003053020190
      certificate := .residual 3763801341077908
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1148
      code := 3148391789498035230
      certificate := .residual 1823073397568305
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5500
      code := 5997058082598478110
      certificate := .residual 342178590499312
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5756
      code := 8686681890678236190
      certificate := .residual 3902339872237972
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1149
      code := 8154776094017940510
      certificate := .residual 1814279334589236
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5501
      code := 4147204235209662750
      certificate := .residual 4348869394664706
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5757
      code := 8657971881140413470
      certificate := .residual 3746484032924307
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1150
      code := 7149910427160898590
      certificate := .residual 2120263579856577
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5502
      code := 4149308146414444830
      certificate := .residual 2042202262924882
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5758
      code := 6164258461135856670
      certificate := .residual 1746834693087456
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1151
      code := 8192759294463667230
      certificate := .residual 1839033866255040
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5503
      code := 4147065142693781790
      certificate := .residual 3919108499073164
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5759
      code := 5587797683297510430
      certificate := .residual 4408292418399744
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
