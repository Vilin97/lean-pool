/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 112–119 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets14 : Array (List PatternEntry) := #[
  [
    { origin := 112
      mask := 80577881440256
      certificate := .sharedThree 4 5 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 880
      mask := 10995219180544
      certificate := .k4 1 [1, 2, 3, 5] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1392
      mask := 216173344754532626
      certificate := .k4 0 [0, 1, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1648
      mask := 153933869809676
      certificate := .k4 0 [0, 2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3184
      mask := 5348303734703382
      certificate := .k4 0 [0, 1, 4, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4720
      mask := 90301693781012
      certificate := .k4 0 [0, 2, 4, 5, 1] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5744
      mask := 1729382813142810654
      certificate := .k4 0 [0, 2, 4, 7, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9072
      mask := 1700996335034634
      certificate := .k4 0 [0, 1, 5, 6, 2, 4, 3] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10096
      mask := 7244822852912883974
      certificate := .k4 0 [0, 1, 2, 7, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 369
      mask := 9896228093952
      certificate := .k4 2 [2, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 625
      mask := 504403158274080774
      certificate := .k4 0 [0, 2, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 881
      mask := 10995219573760
      certificate := .k4 1 [1, 3, 5, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1137
      mask := 5629552421765120
      certificate := .k4 2 [2, 4, 6, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1393
      mask := 360287972429463564
      certificate := .k4 0 [0, 2, 3, 7] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2673
      mask := 18833433830678
      certificate := .k4 0 [0, 1, 4, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3185
      mask := 5348303734719510
      certificate := .k4 0 [0, 4, 6, 1, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4209
      mask := 2885331819224393728
      certificate := .k4 1 [1, 5, 6, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5745
      mask := 1729382813175647518
      certificate := .k4 0 [0, 1, 4, 7, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8561
      mask := 432345603193340190
      certificate := .k4 0 [0, 1, 4, 7, 3, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 114
      mask := 89060447158272
      certificate := .sharedThree 2 5 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 882
      mask := 10995722497024
      certificate := .k4 1 [1, 2, 5, 3] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1138
      mask := 5629783007446016
      certificate := .k4 1 [1, 2, 6, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1394
      mask := 360288541428744212
      certificate := .k4 0 [0, 2, 4, 7] 0 2 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1906
      mask := 11821949609074954
      certificate := .k4 0 [0, 1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2674
      mask := 18833433895958
      certificate := .k4 0 [0, 2, 4, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5746
      mask := 1729382817421525022
      certificate := .k4 0 [0, 2, 3, 7, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6514
      mask := 3399854544519168
      certificate := .k4 2 [2, 5, 6, 4, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7282
      mask := 14636990850097414
      certificate := .k4 0 [0, 1, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7794
      mask := 149555621569560
      certificate := .k4 0 [0, 3, 4, 5, 2, 1] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 115
      mask := 89061800804352
      certificate := .sharedThree 3 5 0 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 371
      mask := 12094627916042
      certificate := .k4 0 [0, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 627
      mask := 792633536615022602
      certificate := .k4 0 [0, 3, 7] 0 1 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1139
      mask := 5629800183120896
      certificate := .k4 1 [1, 2, 4, 6] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1395
      mask := 648518936916131864
      certificate := .k4 0 [0, 3, 4, 7] 0 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2675
      mask := 18833434871062
      certificate := .k4 0 [0, 1, 4, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4211
      mask := 2892093816272087040
      certificate := .k4 1 [1, 6, 5, 7, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6515
      mask := 3399871523586048
      certificate := .k4 2 [2, 5, 6, 4, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7283
      mask := 14636992477855756
      certificate := .k4 0 [0, 2, 3, 4, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8563
      mask := 432345607472054558
      certificate := .k4 0 [0, 1, 3, 7, 4, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 116
      mask := 144036031823872
      certificate := .sharedThree 2 5 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 372
      mask := 12095215108106
      certificate := .k4 0 [0, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 628
      mask := 936748722502041612
      certificate := .k4 0 [0, 2, 7] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1908
      mask := 11821950135577600
      certificate := .k4 1 [1, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2420
      mask := 51825476894
      certificate := .k4 0 [0, 1, 3, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4212
      mask := 2892656766232297472
      certificate := .k4 2 [2, 6, 5, 7, 3] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5236
      mask := 9570149264878604
      certificate := .k4 0 [0, 2, 3, 1, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6516
      mask := 3404253125804032
      certificate := .k4 2 [2, 6, 3, 5, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7284
      mask := 14637009925111820
      certificate := .k4 0 [0, 2, 3, 4, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 117
      mask := 144038221053952
      certificate := .sharedThree 3 5 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 373
      mask := 14293653848076
      certificate := .k4 0 [0, 2, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 629
      mask := 936748724724432908
      certificate := .k4 0 [0, 3, 7] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 885
      mask := 10995756442624
      certificate := .k4 1 [1, 5, 3, 2] 1 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1653
      mask := 154655668043776
      certificate := .k4 2 [2, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1909
      mask := 11821950649248010
      certificate := .k4 0 [0, 1, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2165
      mask := 2703779357062594560
      certificate := .k4 2 [2, 6, 7, 5] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3445
      mask := 9659222534938898
      certificate := .k4 0 [0, 1, 4, 6, 5] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4213
      mask := 2893714496444981248
      certificate := .k4 1 [1, 5, 7, 3, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4469
      mask := 13220466262046
      certificate := .k4 0 [0, 3, 5, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5237
      mask := 9570149299020042
      certificate := .k4 0 [0, 1, 3, 6, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6517
      mask := 3404270104870912
      certificate := .k4 2 [2, 6, 3, 5, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 118
      mask := 144598663954432
      certificate := .sharedThree 4 5 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 374
      mask := 14294271918092
      certificate := .k4 0 [0, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1142
      mask := 5629809918476288
      certificate := .k4 2 [2, 3, 6, 4] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3190
      mask := 5348304837691418
      certificate := .k4 0 [0, 4, 6, 1, 3] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5238
      mask := 9570150835776524
      certificate := .k4 0 [0, 2, 3, 1, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 631
      mask := 1369094849361346578
      certificate := .k4 0 [0, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1143
      mask := 5629827094151168
      certificate := .k4 2 [2, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4215
      mask := 2893730302159486976
      certificate := .k4 3 [3, 6, 7, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7799
      mask := 149573052113940
      certificate := .k4 0 [0, 2, 4, 1, 3, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets14 : Array (List HardEntry) := #[
  [
    { origin := 1136
      code := 3140087176546053150
      certificate := .residual 1704648176168674
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5488
      code := 5128989379177079070
      certificate := .residual 201441638627824
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5744
      code := 4147200936674780190
      certificate := .residual 4348749135579527
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1137
      code := 3148743769030487070
      certificate := .residual 235185532687729
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5489
      code := 2860997195188527390
      certificate := .residual 192662714464752
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5745
      code := 4147065129808880670
      certificate := .residual 338600849211634
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1138
      code := 8192828562639252510
      certificate := .residual 3792565844454918
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5490
      code := 5131232109093576990
      certificate := .residual 201443517733360
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5746
      code := 5563521979407590430
      certificate := .residual 2308685135053025
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1139
      code := 8154843163203824670
      certificate := .residual 1831596634339923
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5491
      code := 7364878298609475870
      certificate := .residual 3792821395080713
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5747
      code := 5131245298419164190
      certificate := .residual 1076521948190643
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1140
      code := 4149440763195386910
      certificate := .residual 2924577021592352
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5492
      code := 7362635294888812830
      certificate := .residual 3792821395080712
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5748
      code := 8661360575725102110
      certificate := .residual 3299969599098368
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1141
      code := 7149979562712591390
      certificate := .residual 3302014003546497
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5493
      code := 2858753780761616670
      certificate := .residual 192664593570288
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5749
      code := 8661351754097157150
      certificate := .residual 2308925686251744
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1142
      code := 7149910564062981150
      certificate := .residual 3303126400255365
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5494
      code := 7364878161707393310
      certificate := .residual 3300240182167048
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5750
      code := 8661345182797194270
      certificate := .residual 2941063806858022
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1143
      code := 8184102838881315870
      certificate := .residual 3893560959063440
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5495
      code := 7362635157986730270
      certificate := .residual 3300240182167049
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5751
      code := 8155343033993978910
      certificate := .residual 3363586684062087
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
