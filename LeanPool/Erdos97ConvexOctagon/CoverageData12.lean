/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 96–103 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets12 : Array (List PatternEntry) := #[
  [
    { origin := 96
      mask := 859006566400
      certificate := .sharedThree 2 4 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 608
      mask := 45741882738794496
      certificate := .k4 1 [1, 5, 6] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2400
      mask := 43236066590
      certificate := .k4 0 [0, 1, 3, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2912
      mask := 1688862750426390
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6240
      mask := 96930214469898
      certificate := .k4 0 [0, 1, 3, 4, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7776
      mask := 145177153504530
      certificate := .k4 0 [0, 1, 4, 2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9824
      mask := 2463680403052134678
      certificate := .k4 0 [0, 1, 2, 7, 5, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10080
      mask := 7099229921754530830
      certificate := .k4 0 [0, 3, 5, 7, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 97
      mask := 962072731648
      certificate := .sharedThree 1 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 609
      mask := 45810052459716608
      certificate := .k4 1 [1, 6, 5] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 865
      mask := 7696583566342
      certificate := .k4 0 [0, 2, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1377
      mask := 14161993233620992
      certificate := .k4 1 [1, 6, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4193
      mask := 2882449999265333260
      certificate := .k4 0 [0, 2, 3, 7, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4961
      mask := 162872166973464
      certificate := .k4 0 [0, 3, 4, 5, 2] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6241
      mask := 96930254356492
      certificate := .k4 0 [0, 2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10081
      mask := 7099238859027825686
      certificate := .k4 0 [0, 4, 5, 7, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 98
      mask := 962087354368
      certificate := .sharedThree 2 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2914
      mask := 1688862750491670
      certificate := .k4 0 [0, 2, 4, 6, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9314
      mask := 10205688409631774
      certificate := .k4 0 [0, 4, 2, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9826
      mask := 2463680420282138906
      certificate := .k4 0 [0, 1, 3, 7, 5, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 99
      mask := 965830770688
      certificate := .sharedThree 3 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 867
      mask := 7696583631110
      certificate := .k4 0 [0, 1, 5, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1123
      mask := 5139538255044608
      certificate := .k4 1 [1, 5, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2147
      mask := 2594225117981060096
      certificate := .k4 1 [1, 5, 7, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8803
      mask := 6958212336553306394
      certificate := .k4 0 [0, 1, 4, 6, 7, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10083
      mask := 7100071048686642190
      certificate := .k4 0 [0, 3, 6, 7, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 100
      mask := 15393162788878
      certificate := .sharedThree 0 5 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 612
      mask := 46307031730094080
      certificate := .k4 2 [2, 5, 6] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 868
      mask := 9896158308618
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1380
      mask := 14711877901746176
      certificate := .k4 2 [2, 6, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2148
      mask := 2594225118618189824
      certificate := .k4 2 [2, 7, 5, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4708
      mask := 88386132206612
      certificate := .k4 0 [0, 2, 4, 1, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5220
      mask := 7047871413100826
      certificate := .k4 0 [0, 1, 5, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8804
      mask := 6958485835781054742
      certificate := .k4 0 [0, 1, 2, 5, 7, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 101
      mask := 24189255811094
      certificate := .sharedThree 0 5 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 613
      mask := 46373002427760640
      certificate := .k4 2 [2, 6, 5] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 869
      mask := 9896160985100
      certificate := .k4 0 [0, 2, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2405
      mask := 43252780310
      certificate := .k4 0 [0, 1, 2, 3, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3941
      mask := 216172782206746894
      certificate := .k4 0 [0, 1, 3, 7, 2] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4197
      mask := 2882453297348881408
      certificate := .k4 1 [1, 2, 3, 7, 5] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 102
      mask := 28587302322202
      certificate := .sharedThree 0 5 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 614
      mask := 46377400470077440
      certificate := .k4 2 [2, 5, 6] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 870
      mask := 9896175085834
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3942
      mask := 216172784362553614
      certificate := .k4 0 [0, 1, 2, 7, 3] 0 1 3 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 103
      mask := 30786325577756
      certificate := .sharedThree 0 5 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 359
      mask := 603787886592
      certificate := .k4 2 [2, 4, 3] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 615
      mask := 46377400472174592
      certificate := .k4 2 [2, 6, 5] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 871
      mask := 9896191861002
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1127
      mask := 5154931417833472
      certificate := .k4 1 [1, 6, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1383
      mask := 14724951783243776
      certificate := .k4 2 [2, 6, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3943
      mask := 216172803598221590
      certificate := .k4 0 [0, 1, 4, 7, 2] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4967
      mask := 163281783358738
      certificate := .k4 0 [0, 1, 4, 2, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7271
      mask := 14434390528508186
      certificate := .k4 0 [0, 1, 6, 5, 3] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10087
      mask := 7102323126582682646
      certificate := .k4 0 [0, 4, 6, 7, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets12 : Array (List HardEntry) := #[
  [
    { origin := 96
      code := 6028799718126071070
      certificate := .residual 4411689737676930
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1120
      code := 2852278069844536350
      certificate := .residual 4170004660737221
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5472
      code := 6164806280117018910
      certificate := .residual 953327621082032
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5728
      code := 3292495849308349470
      certificate := .residual 3763801341077906
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 97
      code := 7679580362667797790
      certificate := .residual 3919108499073154
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1121
      code := 3713030747648977950
      certificate := .residual 2317405881600101
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5473
      code := 3867059112994464030
      certificate := .residual 1023696118844336
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5729
      code := 3858823622709273630
      certificate := .residual 3608201016170017
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 98
      code := 6463393094542306590
      certificate := .residual 4403871017683988
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1122
      code := 2851717318914370590
      certificate := .residual 2982865092065602
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5474
      code := 5590605597368705310
      certificate := .residual 945631039630256
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5730
      code := 3284614670219535390
      certificate := .residual 3614800334083349
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 99
      code := 6459170970143304990
      certificate := .residual 4403871017683985
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1123
      code := 5995847784353786910
      certificate := .residual 1481298832039378
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5475
      code := 3858832585567822110
      certificate := .residual 1873304089393186
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5731
      code := 2852269131761771550
      certificate := .residual 2469879245950033
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 100
      code := 5159386447612488990
      certificate := .residual 629716203341792
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1124
      code := 6136035516895226910
      certificate := .residual 2748053695466578
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5476
      code := 5560702845549338910
      certificate := .residual 2427322651097122
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5732
      code := 7148705516495692830
      certificate := .residual 4049790669524776
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 101
      code := 8257725703402302750
      certificate := .residual 3911289779080212
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1125
      code := 5131169850038184990
      certificate := .residual 4411539413806348
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5477
      code := 3292858430246150430
      certificate := .residual 1015999537392560
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5733
      code := 7146462512775029790
      certificate := .residual 3792821395080714
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 102
      code := 7176861793085041950
      certificate := .residual 3911289779080209
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1126
      code := 5991922527842626590
      certificate := .residual 4248877701442759
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5478
      code := 6139406481649885470
      certificate := .residual 1873168790583330
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5734
      code := 7148705379593610270
      certificate := .residual 3300240182167050
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 103
      code := 6451356316910234910
      certificate := .residual 620937202108384
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1127
      code := 5130609099108019230
      certificate := .residual 989142335587282
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5479
      code := 3284614683104436510
      certificate := .residual 2427457949906978
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5735
      code := 7146462375872947230
      certificate := .residual 4049788786806568
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
