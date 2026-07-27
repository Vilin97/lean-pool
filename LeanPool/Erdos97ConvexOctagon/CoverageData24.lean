/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 192–199 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets24 : Array (List PatternEntry) := #[
  [
    { origin := 192
      mask := 1008806316530991118
      certificate := .sharedThree 0 7 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 448
      mask := 163294668128256
      certificate := .k4 2 [2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 704
      mask := 4899916394591863808
      certificate := .k4 1 [1, 2, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 960
      mask := 23231479218196
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1984
      mask := 15763016129708056
      certificate := .k4 0 [0, 3, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2240
      mask := 4800837202783429632
      certificate := .k4 1 [1, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10944
      mask := 3468546353679385870
      certificate := .k4 0 [0, 1, 2, 6, 5, 7, 4, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 193
      mask := 1585267068834414614
      certificate := .sharedThree 0 7 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 449
      mask := 163414927212544
      certificate := .k4 2 [2, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 705
      mask := 4899916397880541184
      certificate := .k4 2 [2, 3, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 961
      mask := 23231481249812
      certificate := .k4 0 [0, 4, 5, 2] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1473
      mask := 14315129667612
      certificate := .k4 0 [0, 4, 2, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1729
      mask := 3377701068537884
      certificate := .k4 0 [0, 2, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3265
      mask := 6755692909232156
      certificate := .k4 0 [0, 2, 4, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 194
      mask := 1873497444986126362
      certificate := .sharedThree 0 7 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 450
      mask := 163432104984576
      certificate := .k4 2 [2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 706
      mask := 4899917236406321152
      certificate := .k4 2 [2, 4, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 962
      mask := 23244364120084
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1218
      mask := 9651514679240704
      certificate := .k4 1 [1, 5, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1474
      mask := 14333178282012
      certificate := .k4 0 [0, 4, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1730
      mask := 3377701085249564
      certificate := .k4 0 [0, 3, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1986
      mask := 15835484290836480
      certificate := .k4 1 [1, 5, 6, 4] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 195
      mask := 2017612633061982236
      certificate := .sharedThree 0 7 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 451
      mask := 163432106033152
      certificate := .k4 2 [2, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 707
      mask := 4937634041458377728
      certificate := .k4 1 [1, 6, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 963
      mask := 23244365168660
      certificate := .k4 0 [0, 2, 5, 4] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1731
      mask := 3377701135122460
      certificate := .k4 0 [0, 2, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2243
      mask := 4801963102690271232
      certificate := .k4 1 [1, 7, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5059
      mask := 3096277660270606
      certificate := .k4 0 [0, 2, 4, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5315
      mask := 10205666933812238
      certificate := .k4 0 [0, 2, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6339
      mask := 162869463458070
      certificate := .k4 0 [0, 1, 2, 4, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6595
      mask := 5629813373665310
      certificate := .k4 0 [0, 4, 3, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 196
      mask := 2522015791329771520
      certificate := .sharedThree 2 7 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 452
      mask := 167712835764224
      certificate := .k4 3 [3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 708
      mask := 4939322894606925824
      certificate := .k4 3 [3, 6, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 964
      mask := 26432067610624
      certificate := .k4 1 [1, 3, 4, 5] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1732
      mask := 3377701151834140
      certificate := .k4 0 [0, 3, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2756
      mask := 21045342905606
      certificate := .k4 0 [0, 1, 5, 4, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4804
      mask := 145135629934858
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 197
      mask := 2522015791914680320
      certificate := .sharedThree 3 7 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 453
      mask := 167815914979328
      certificate := .k4 3 [3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 709
      mask := 4941575532945866752
      certificate := .k4 4 [4, 6, 7] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2245
      mask := 4803089004234858496
      certificate := .k4 1 [1, 7, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4549
      mask := 26556353219606
      certificate := .k4 0 [0, 4, 5, 3, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7365
      mask := 1441152434901748766
      certificate := .k4 0 [0, 3, 4, 7, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 198
      mask := 2522015941651333120
      certificate := .sharedThree 4 7 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 454
      mask := 167849737846784
      certificate := .k4 3 [3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 710
      mask := 5044031582659331072
      certificate := .k4 1 [1, 2, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2502
      mask := 6597122729230
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7110
      mask := 12738942809957390
      certificate := .k4 0 [0, 3, 6, 5, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7366
      mask := 1441152434918525982
      certificate := .k4 0 [0, 4, 7, 2, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8646
      mask := 2594222932394901534
      certificate := .k4 0 [0, 3, 4, 5, 7, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 199
      mask := 2531867415512350720
      certificate := .sharedThree 6 7 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 455
      mask := 167850006282240
      certificate := .k4 3 [3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 711
      mask := 5044031582667588608
      certificate := .k4 1 [1, 7, 2] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 967
      mask := 26440694235136
      certificate := .k4 2 [2, 4, 3, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1223
      mask := 9658531045203968
      certificate := .k4 1 [1, 6, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1479
      mask := 18846319846656
      certificate := .k4 1 [1, 2, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2247
      mask := 4805341223311171584
      certificate := .k4 1 [1, 7, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2503
      mask := 6597122731022
      certificate := .k4 0 [0, 3, 1, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5575
      mask := 13586944357311766
      certificate := .k4 0 [0, 1, 4, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8135
      mask := 9644954657243422
      certificate := .k4 0 [0, 1, 4, 6, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10439
      mask := 1441159062240111630
      certificate := .k4 0 [0, 3, 4, 7, 2, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets24 : Array (List HardEntry) := #[
  [
    { origin := 704
      code := 3149311144688313630
      certificate := .residual 4326046471266579
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1216
      code := 8192763675079633950
      certificate := .residual 1346452657004224
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5568
      code := 6137730551055048990
      certificate := .residual 1743497469813349
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5824
      code := 6428199806099973150
      certificate := .residual 1738296320123105
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 705
      code := 4154163609050768670
      certificate := .residual 4200961986576550
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1217
      code := 2860442772611558430
      certificate := .residual 3300931671773570
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5569
      code := 5563521598565310750
      certificate := .residual 3105888168454850
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5825
      code := 2862122824499389470
      certificate := .residual 1077636227667891
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 706
      code := 3145366216958895390
      certificate := .residual 1171934254014048
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1218
      code := 3139947540449356830
      certificate := .residual 1423471131106978
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5570
      code := 4149305562253943070
      certificate := .residual 1442295531355170
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5826
      code := 8661912649817318430
      certificate := .residual 1738296320123104
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 707
      code := 3721818044823594270
      certificate := .residual 1171932374908512
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1219
      code := 3860508104845716510
      certificate := .residual 2748068731522130
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5571
      code := 4145367103248195870
      certificate := .residual 2486971123880994
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5827
      code := 8659660824468710430
      certificate := .residual 3792565844454912
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 708
      code := 6028587786195068190
      certificate := .residual 1231998015078208
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1220
      code := 3716955866723281950
      certificate := .residual 4248894620216519
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5572
      code := 5590597052753568030
      certificate := .residual 953325712673712
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5828
      code := 8657972000378250270
      certificate := .residual 3495219553702694
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 709
      code := 3726950546396570910
      certificate := .residual 1231999897796416
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1221
      code := 2852277932407680030
      certificate := .residual 918775720543186
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5573
      code := 6164814548788896030
      certificate := .residual 945629131221936
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5829
      code := 3862203275857290270
      certificate := .residual 1738176031678689
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 710
      code := 5454378726616884510
      certificate := .residual 1223339360894784
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1222
      code := 3713030610212121630
      certificate := .residual 1551650411027922
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5574
      code := 5563515412202184990
      certificate := .residual 1872341987358754
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5830
      code := 6425956528575144990
      certificate := .residual 260552692383986
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 711
      code := 3150498346195641630
      certificate := .residual 1223341243612992
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1223
      code := 2851717181477514270
      certificate := .residual 4349966758980876
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5575
      code := 3138258826163708190
      certificate := .residual 2426225198872610
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5831
      code := 8658044164888519710
      certificate := .residual 1007284545918899
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
