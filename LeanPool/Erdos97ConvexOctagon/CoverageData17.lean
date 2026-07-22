/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 136–143 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets17 : Array (List PatternEntry) := #[
  [
    { origin := 136
      mask := 215507567378432
      certificate := .sharedThree 3 5 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 648
      mask := 2594236817460953088
      certificate := .k4 4 [4, 5, 7] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 904
      mask := 13349097570304
      certificate := .k4 2 [2, 3, 4, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1160
      mask := 6755443766478848
      certificate := .k4 1 [1, 3, 4, 6] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2440
      mask := 3298621531150
      certificate := .k4 0 [0, 3, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2696
      mask := 18846319781126
      certificate := .k4 0 [0, 1, 2, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3208
      mask := 5629800186250518
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4488
      mask := 19933043895326
      certificate := .k4 0 [0, 4, 5, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5000
      mask := 1688850201592094
      certificate := .k4 0 [0, 1, 6, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6024
      mask := 21062857924870
      certificate := .k4 0 [0, 1, 5, 4, 3, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 137
      mask := 216346092634112
      certificate := .sharedThree 4 5 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 393
      mask := 76965820391424
      certificate := .k4 1 [1, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 649
      mask := 2738188573443531776
      certificate := .k4 1 [1, 2, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 905
      mask := 13349567332352
      certificate := .k4 2 [2, 4, 5, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3465
      mask := 9924191956575494
      certificate := .k4 0 [0, 1, 2, 5, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 394
      mask := 79166481393664
      certificate := .k4 1 [1, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 650
      mask := 2738188573451789312
      certificate := .k4 1 [1, 7, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 906
      mask := 13349632344064
      certificate := .k4 2 [2, 3, 4, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1162
      mask := 6755452394668032
      certificate := .k4 2 [2, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1418
      mask := 55835231518
      certificate := .k4 0 [0, 1, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1674
      mask := 163419220148244
      certificate := .k4 0 [0, 2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3466
      mask := 9924191956706310
      certificate := .k4 0 [0, 2, 1, 5, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5002
      mask := 1688888520753438
      certificate := .k4 0 [0, 1, 4, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6538
      mask := 5066841724046350
      certificate := .k4 0 [0, 3, 2, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 139
      mask := 219902338662400
      certificate := .sharedThree 2 5 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 395
      mask := 79166521737216
      certificate := .k4 2 [2, 3, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 651
      mask := 2738188573451887616
      certificate := .k4 1 [1, 2, 7] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 907
      mask := 13366277439488
      certificate := .k4 2 [2, 3, 5, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1163
      mask := 6755452395192320
      certificate := .k4 2 [2, 4, 3, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2187
      mask := 2898224693913845760
      certificate := .k4 3 [3, 6, 7, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2443
      mask := 3299158270222
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4491
      mask := 19945829772302
      certificate := .k4 0 [0, 2, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4747
      mask := 92638157079826
      certificate := .k4 0 [0, 1, 4, 2, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7307
      mask := 15762784721592594
      certificate := .k4 0 [0, 1, 4, 3, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9867
      mask := 2882447838613152790
      certificate := .k4 0 [0, 2, 4, 3, 7, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 140
      mask := 220761319014400
      certificate := .sharedThree 4 5 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 396
      mask := 79613392846848
      certificate := .k4 3 [3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 652
      mask := 2738188573451919360
      certificate := .k4 1 [1, 7, 2] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1164
      mask := 6755684284647424
      certificate := .k4 1 [1, 3, 6, 4] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2188
      mask := 2898295061584281600
      certificate := .k4 3 [3, 7, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4236
      mask := 3458923445398011904
      certificate := .k4 2 [2, 3, 4, 7, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7308
      mask := 15762793317859348
      certificate := .k4 0 [0, 2, 4, 3, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 397
      mask := 81364967778304
      certificate := .k4 1 [1, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 909
      mask := 13366813786112
      certificate := .k4 2 [2, 5, 3, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1165
      mask := 6755692912836608
      certificate := .k4 2 [2, 3, 6, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1677
      mask := 167300060151808
      certificate := .k4 2 [2, 3, 4, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2189
      mask := 2993135636329791488
      certificate := .k4 3 [3, 6, 7, 5] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4493
      mask := 19963009638686
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8333
      mask := 11331568246268190
      certificate := .k4 0 [0, 1, 2, 5, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 142
      mask := 228698432208896
      certificate := .sharedThree 2 5 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 398
      mask := 81365471094784
      certificate := .k4 1 [1, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 654
      mask := 2738333708976169984
      certificate := .k4 1 [1, 7, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1166
      mask := 6755717570643968
      certificate := .k4 1 [1, 3, 4, 6] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1422
      mask := 6597072399630
      certificate := .k4 0 [0, 1, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1678
      mask := 167682787770392
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2190
      mask := 2999759093838643200
      certificate := .k4 3 [3, 5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2702
      mask := 18854907552022
      certificate := .k4 0 [0, 1, 2, 4, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3982
      mask := 648518348514231310
      certificate := .k4 0 [0, 2, 3, 1, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4494
      mask := 19963343547662
      certificate := .k4 0 [0, 1, 5, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5006
      mask := 1688901405655326
      certificate := .k4 0 [0, 1, 6, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 143
      mask := 228701908238336
      certificate := .sharedThree 3 5 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 911
      mask := 14293737668620
      certificate := .k4 0 [0, 3, 2, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1423
      mask := 6597072464910
      certificate := .k4 0 [0, 2, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1679
      mask := 167716879073304
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5263
      mask := 9649314666138638
      certificate := .k4 0 [0, 3, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6543
      mask := 5066859154590734
      certificate := .k4 0 [0, 2, 3, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets17 : Array (List HardEntry) := #[
  [
    { origin := 1160
      code := 3871005816665041950
      certificate := .residual 4348869394664713
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5512
      code := 4145376318603321630
      certificate := .residual 1994389914580002
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5768
      code := 8659093639675438110
      certificate := .residual 2941065685963558
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1161
      code := 3726892827612441630
      certificate := .residual 4348869394664712
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5513
      code := 5591731479260094750
      certificate := .residual 936852126455728
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5769
      code := 4149307752636933150
      certificate := .residual 269331616547058
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1162
      code := 4158040199043640350
      certificate := .residual 333670249292016
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5514
      code := 4147062943704080670
      certificate := .residual 1380722880142370
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5770
      code := 6137730551004718110
      certificate := .residual 1746834693087457
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1163
      code := 3866783692266040350
      certificate := .residual 3608063844275752
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5515
      code := 6137799802251567390
      certificate := .residual 3793888694448386
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5771
      code := 8686677509794882590
      certificate := .residual 936917930874803
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1164
      code := 3722670703213440030
      certificate := .residual 4348869394664714
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5516
      code := 8401838035908092190
      certificate := .residual 340013860921840
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5772
      code := 7608079273227248670
      certificate := .residual 3911135697111441
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1165
      code := 4153385690690841630
      certificate := .residual 2396829421902163
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5517
      code := 8661430669641703710
      certificate := .residual 332315396802032
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5773
      code := 7676198412520842270
      certificate := .residual 2468811968597076
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1166
      code := 5420582032932695070
      certificate := .residual 2286266264038626
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5518
      code := 8230703861408129310
      certificate := .residual 3792671071103497
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5774
      code := 3717098525771228190
      certificate := .residual 3349285244307858
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1167
      code := 4153242217308318750
      certificate := .residual 2526709300056372
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5519
      code := 8229582359547797790
      certificate := .residual 3792671071103496
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5775
      code := 7581128044744074270
      certificate := .residual 4334447695825298
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
