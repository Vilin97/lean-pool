/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 88–95 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets11 : Array (List PatternEntry) := #[
  [
    { origin := 88
      mask := 828928737536
      certificate := .sharedThree 1 4 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 600
      mask := 42784784065232896
      certificate := .k4 3 [3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1368
      mask := 13607729046224896
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1880
      mask := 11331566840736768
      certificate := .k4 1 [1, 2, 5, 6] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2136
      mask := 2450173701575073792
      certificate := .k4 1 [1, 7, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4952
      mask := 161115782783242
      certificate := .k4 0 [0, 1, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 89
      mask := 828941336576
      certificate := .sharedThree 2 4 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 601
      mask := 42785024583401472
      certificate := .k4 3 [3, 6, 4] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1369
      mask := 13607729314660352
      certificate := .k4 3 [3, 5, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1625
      mask := 147334566748422
      certificate := .k4 0 [0, 1, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2137
      mask := 2450178101259329536
      certificate := .k4 1 [1, 7, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2393
      mask := 38991430942
      certificate := .k4 0 [0, 1, 4, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2905
      mask := 1688849915461902
      certificate := .k4 0 [0, 1, 3, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4441
      mask := 10995990274334
      certificate := .k4 0 [0, 1, 5, 3, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 90
      mask := 832166690816
      certificate := .sharedThree 3 4 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 602
      mask := 42785057869398016
      certificate := .k4 3 [3, 4, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2138
      mask := 2450187316614979584
      certificate := .k4 1 [1, 7, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3930
      mask := 14724956074082324
      certificate := .k4 0 [0, 2, 4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5210
      mask := 6769973942812700
      certificate := .k4 0 [0, 4, 6, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7002
      mask := 11334866461467662
      certificate := .k4 0 [0, 2, 3, 1, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9818
      mask := 2461428303765143822
      certificate := .k4 0 [0, 1, 2, 7, 5, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 91
      mask := 833236369408
      certificate := .sharedThree 2 4 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 603
      mask := 42785058674704384
      certificate := .k4 3 [3, 6, 4] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1115
      mask := 5066850233762816
      certificate := .k4 1 [1, 6, 4, 2] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1371
      mask := 13607866753613824
      certificate := .k4 3 [3, 5, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2907
      mask := 1688849948429326
      certificate := .k4 0 [0, 2, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6491
      mask := 3377726871371806
      certificate := .k4 0 [0, 2, 4, 6, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7003
      mask := 11334866463499278
      certificate := .k4 0 [0, 3, 6, 5, 2, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10075
      mask := 5810282889614484502
      certificate := .k4 0 [0, 4, 7, 6, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10587
      mask := 3468546323312626718
      certificate := .k4 0 [0, 2, 4, 7, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 92
      mask := 836478435328
      certificate := .sharedThree 3 4 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 348
      mask := 575535219712
      certificate := .k4 1 [1, 2, 4] 1 2 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 604
      mask := 45249301529550848
      certificate := .k4 1 [1, 5, 6] 1 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7260
      mask := 14149894310749206
      certificate := .k4 0 [0, 4, 6, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8796
      mask := 6955955860610753806
      certificate := .k4 0 [0, 1, 3, 6, 7, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9820
      mask := 2461428316851175706
      certificate := .k4 0 [0, 1, 4, 7, 5, 6, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 93
      mask := 841813640192
      certificate := .sharedThree 1 4 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 605
      mask := 45251500567429120
      certificate := .k4 2 [2, 5, 6] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1629
      mask := 147337318638592
      certificate := .k4 1 [1, 2, 5, 3] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 94
      mask := 845101924352
      certificate := .sharedThree 3 4 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 606
      mask := 45255902357356544
      certificate := .k4 3 [3, 5, 6] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 862
      mask := 7696581599494
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2398
      mask := 43236001054
      certificate := .k4 0 [0, 1, 2, 3, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2654
      mask := 14294207046670
      certificate := .k4 0 [0, 3, 5, 2, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8798
      mask := 6956234035966845198
      certificate := .k4 0 [0, 1, 2, 5, 7, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 607
      mask := 45265656764956672
      certificate := .k4 4 [4, 5, 6] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 863
      mask := 7696581600262
      certificate := .k4 0 [0, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1119
      mask := 5066868750567424
      certificate := .k4 1 [1, 6, 4, 3] 1 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1375
      mask := 14161855794667520
      certificate := .k4 1 [1, 6, 5, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1631
      mask := 148038942336000
      certificate := .k4 1 [1, 2, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6239
      mask := 96912807100428
      certificate := .k4 0 [0, 2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets11 : Array (List HardEntry) := #[
  [
    { origin := 88
      code := 6028848096049900830
      certificate := .residual 3918988239981697
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1112
      code := 3858394538300697630
      certificate := .residual 831277788613556
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5464
      code := 3284630093245374750
      certificate := .residual 1752291532792421
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5720
      code := 6137154788874839070
      certificate := .residual 3045388487022113
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 89
      code := 7676196318743112990
      certificate := .residual 129318065997680
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1113
      code := 3857273036440366110
      certificate := .residual 1012192553183169
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5465
      code := 6428199807754625310
      certificate := .residual 2183179864891986
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5721
      code := 5560702832664437790
      certificate := .residual 3051987804935445
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 90
      code := 6027669437570100510
      certificate := .residual 4411569478585474
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1114
      code := 5131229055910702110
      certificate := .residual 3916898738204933
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5466
      code := 6141095331509756190
      certificate := .residual 4410727664945292
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5722
      code := 5128357294206673950
      certificate := .residual 2468796906851409
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 91
      code := 7391345605866958110
      certificate := .residual 3918988239981698
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1115
      code := 5131161152477752350
      certificate := .residual 1785208665339682
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5467
      code := 5564643375299354910
      certificate := .residual 2605136886566482
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5723
      code := 6139406481599554590
      certificate := .residual 3122356281021717
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 92
      code := 6026825012690300190
      certificate := .residual 4411689737676935
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1116
      code := 5131238848687795230
      certificate := .residual 3793512884687234
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5468
      code := 6137730825928761630
      certificate := .residual 1549756363472466
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5724
      code := 5562954525389153310
      certificate := .residual 3115756963108385
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 93
      code := 7175172823803505950
      certificate := .residual 3919108499073159
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1117
      code := 5419400209010027550
      certificate := .residual 1422509054762658
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5469
      code := 5563521873439023390
      certificate := .residual 4161193796421319
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5725
      code := 5166346941884851230
      certificate := .residual 1976215697550420
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 94
      code := 6024064411992403230
      certificate := .residual 1505314909371952
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1118
      code := 3716956004160138270
      certificate := .residual 4249375660746946
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5470
      code := 6141093141076435230
      certificate := .residual 1441333429320738
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5726
      code := 5130600165303444510
      certificate := .residual 1976215697550417
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 95
      code := 6454720852555541790
      certificate := .residual 1505316817780272
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1119
      code := 3857143736701578270
      certificate := .residual 3475218863138626
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5471
      code := 5132289015213646110
      certificate := .residual 2486835773690914
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5727
      code := 5598408814949360670
      certificate := .residual 4394921110841745
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
