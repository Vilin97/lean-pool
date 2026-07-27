/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 56–63 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets07 : Array (List PatternEntry) := #[
  [
    { origin := 56
      mask := 176093669632
      certificate := .sharedThree 1 4 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 312
      mask := 163212043264
      certificate := .k4 1 [1, 2, 4] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 568
      mask := 37154696938570752
      certificate := .k4 1 [1, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 824
      mask := 51875741724
      certificate := .k4 0 [0, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1336
      mask := 13533218616639488
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 57
      mask := 176096346112
      certificate := .sharedThree 2 4 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 569
      mask := 37154700227248128
      certificate := .k4 2 [2, 3, 6] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 825
      mask := 51876266012
      certificate := .k4 0 [0, 2, 4, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1337
      mask := 13533218617688064
      certificate := .k4 2 [2, 5, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1849
      mask := 10214463028866048
      certificate := .k4 1 [1, 5, 6, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2105
      mask := 1369094840779997206
      certificate := .k4 0 [0, 2, 4, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2361
      mask := 21559905310
      certificate := .k4 0 [0, 3, 4, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4409
      mask := 6597358657822
      certificate := .k4 0 [0, 1, 3, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8761
      mask := 5233258635471103246
      certificate := .k4 0 [0, 1, 3, 7, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 58
      mask := 287767199744
      certificate := .sharedThree 2 4 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 570
      mask := 37155538753028096
      certificate := .k4 2 [2, 4, 6] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 826
      mask := 3298537055494
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1082
      mask := 3452467122012160
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1338
      mask := 13537498277871616
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3130
      mask := 4785366667183366
      certificate := .k4 0 [0, 1, 2, 4, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5178
      mask := 5657434005766172
      certificate := .k4 0 [0, 2, 6, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 59
      mask := 288886882304
      certificate := .sharedThree 3 4 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 315
      mask := 172674777088
      certificate := .k4 2 [2, 3, 4] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 571
      mask := 37370201219530752
      certificate := .k4 2 [2, 5, 6] 2 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 827
      mask := 3298537121030
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2107
      mask := 1369094862247362582
      certificate := .k4 0 [0, 2, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4923
      mask := 159021175801106
      certificate := .k4 0 [0, 1, 4, 2, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 60
      mask := 296352761088
      certificate := .sharedThree 1 4 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 572
      mask := 37717646887797760
      certificate := .k4 1 [1, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 828
      mask := 3298537185542
      certificate := .k4 0 [0, 1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1084
      mask := 3452468191559680
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1340
      mask := 13537635179954176
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1596
      mask := 92513600955392
      certificate := .k4 1 [1, 2, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2108
      mask := 1369094879711330330
      certificate := .k4 0 [0, 3, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8764
      mask := 5234308669077873930
      certificate := .k4 0 [0, 1, 3, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 61
      mask := 297510371328
      certificate := .sharedThree 3 4 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 573
      mask := 37717646891860992
      certificate := .k4 1 [1, 6, 2] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 829
      mask := 3298537186310
      certificate := .k4 0 [0, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1341
      mask := 13537635448389632
      certificate := .k4 3 [3, 5, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1597
      mask := 92515279044608
      certificate := .k4 2 [2, 3, 4, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2109
      mask := 1441152439113941014
      certificate := .k4 0 [0, 2, 7, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2365
      mask := 21577075742
      certificate := .k4 0 [0, 4, 2, 3, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2877
      mask := 844743042941210
      certificate := .k4 0 [0, 1, 3, 6, 4] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7997
      mask := 5066867509641502
      certificate := .k4 0 [0, 1, 2, 6, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8765
      mask := 5801199824058010654
      certificate := .k4 0 [0, 2, 4, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10045
      mask := 5233821585424540686
      certificate := .k4 0 [0, 3, 7, 6, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 318
      mask := 181227497472
      certificate := .k4 1 [1, 3, 4] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 830
      mask := 3299088541962
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1086
      mask := 3456865168523264
      certificate := .k4 2 [2, 3, 6, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1598
      mask := 92638157013012
      certificate := .k4 0 [0, 2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2110
      mask := 1441152443408842774
      certificate := .k4 0 [0, 4, 7, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4414
      mask := 6597408989470
      certificate := .k4 0 [0, 1, 5, 2, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8766
      mask := 5801199824141306910
      certificate := .k4 0 [0, 3, 4, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 63
      mask := 313537396736
      certificate := .sharedThree 2 4 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 575
      mask := 37717646891991040
      certificate := .k4 1 [1, 6, 2] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 831
      mask := 3299105319178
      certificate := .k4 0 [0, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2111
      mask := 1441152456292761622
      certificate := .k4 0 [0, 2, 7, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2879
      mask := 1407374938229774
      certificate := .k4 0 [0, 3, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6719
      mask := 9649327769141530
      certificate := .k4 0 [0, 1, 4, 6, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8767
      mask := 5801199871302648094
      certificate := .k4 0 [0, 1, 2, 6, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets07 : Array (List HardEntry) := #[
  [
    { origin := 56
      code := 6020124028603280670
      certificate := .residual 3919108499073152
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1080
      code := 6425463230137789470
      certificate := .residual 2983815835859488
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5432
      code := 4157540745662357790
      certificate := .residual 1007216833091504
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5688
      code := 3284630063381406750
      certificate := .residual 347139299246322
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 57
      code := 6027726611954085150
      certificate := .residual 3919108499073153
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1081
      code := 8185652733411486750
      certificate := .residual 1243633049837364
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5433
      code := 3284067126346440990
      certificate := .residual 1378663402953762
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5689
      code := 6141095301645788190
      certificate := .residual 2317584399040737
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 58
      code := 8401969528966360350
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 6, 7] 0 1 2 4 6 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1082
      code := 7176861810043284510
      certificate := .residual 1487082567597761
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5434
      code := 6455288481650499870
      certificate := .residual 935767886174128
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5690
      code := 5155451889234600990
      certificate := .residual 4377603802688147
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 59
      code := 6455284342312807710
      certificate := .residual 4403871017683987
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1083
      code := 5132363918658923550
      certificate := .residual 1261221073035057
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5435
      code := 6453036656301891870
      certificate := .residual 4408532936632841
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5691
      code := 3281954555917624350
      certificate := .residual 4325651870951828
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 60
      code := 7173065174095637790
      certificate := .residual 3911410038171664
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1084
      code := 3862340685314288670
      certificate := .residual 2923477778371360
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5436
      code := 5591723227567284510
      certificate := .residual 4408532936632840
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5692
      code := 5600379139785876510
      certificate := .residual 4394921110841748
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 61
      code := 7175740309239901470
      certificate := .residual 3911410038171665
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1085
      code := 7148858078349388830
      certificate := .residual 3300931671773569
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5437
      code := 6461693248786325790
      certificate := .residual 278426265174512
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5693
      code := 2862190729553372190
      certificate := .residual 4308334562798227
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 62
      code := 8404783183248764190
      certificate := .residual 226269360933619
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1086
      code := 7148789079699778590
      certificate := .residual 3303111367862661
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5438
      code := 4155298310807281950
      certificate := .residual 1006134501218224
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5694
      code := 5446497545397396510
      certificate := .residual 1755613694320864
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 63
      code := 7395988974230580510
      certificate := .residual 4348042613567750
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1087
      code := 6460844003279662110
      certificate := .residual 752132264057780
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5439
      code := 4146632896694903070
      certificate := .residual 279508604273136
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5695
      code := 5444245720048788510
      certificate := .residual 3915711179795968
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
