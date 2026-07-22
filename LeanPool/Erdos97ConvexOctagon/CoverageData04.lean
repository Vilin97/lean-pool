/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 32–39 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets04 : Array (List PatternEntry) := #[
  [
    { origin := 32
      mask := 1886388224
      certificate := .sharedThree 2 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 288
      mask := 30064772374
      certificate := .k4 0 [0, 1, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 544
      mask := 13881476034592768
      certificate := .k4 4 [4, 5, 6] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1056
      mask := 2887318104991744
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1312
      mask := 11347407480553472
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1568
      mask := 81364984553738
      certificate := .k4 0 [0, 1, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2080
      mask := 792633536590053390
      certificate := .k4 0 [0, 2, 3, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3360
      mask := 9644916003266822
      certificate := .k4 0 [0, 1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6176
      mask := 83564077539594
      certificate := .k4 0 [0, 1, 3, 2, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 33
      mask := 2206400512
      certificate := .sharedThree 2 3 0 1 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 545
      mask := 13881613473546240
      certificate := .k4 4 [4, 6, 5] 0 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1057
      mask := 2887319145179136
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4385
      mask := 6964984363154931712
      certificate := .k4 3 [3, 6, 7, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 290
      mask := 30064967702
      certificate := .k4 0 [0, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 802
      mask := 25770919190
      certificate := .k4 0 [0, 1, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1058
      mask := 2887319178717184
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1826
      mask := 9662671393678336
      certificate := .k4 1 [1, 6, 5, 4] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4130
      mask := 1801440407222485020
      certificate := .k4 0 [0, 4, 7, 3, 2] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4386
      mask := 6967229435707678720
      certificate := .k4 1 [1, 5, 7, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5410
      mask := 11259000696040460
      certificate := .k4 0 [0, 2, 3, 1, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10786
      mask := 6958204639972502558
      certificate := .k4 0 [0, 2, 4, 6, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 291
      mask := 30065950742
      certificate := .k4 0 [0, 4, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2083
      mask := 792633575521386522
      certificate := .k4 0 [0, 4, 3, 7] 0 1 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2339
      mask := 7026533510907191296
      certificate := .k4 1 [1, 5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7459
      mask := 4946078290770354438
      certificate := .k4 0 [0, 1, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10787
      mask := 6958204640055798814
      certificate := .k4 0 [0, 3, 4, 6, 7, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 36
      mask := 2442199040
      certificate := .sharedThree 2 3 0 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 804
      mask := 25770984726
      certificate := .k4 0 [0, 1, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1060
      mask := 2893915174758400
      certificate := .k4 1 [1, 3, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1316
      mask := 11356169213837312
      certificate := .k4 3 [3, 5, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1828
      mask := 9667086620059648
      certificate := .k4 1 [1, 6, 5, 4] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2084
      mask := 792634099222183962
      certificate := .k4 0 [0, 3, 4, 7] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4132
      mask := 1801440420124688396
      certificate := .k4 0 [0, 3, 7, 4, 2] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5668
      mask := 14990741534220566
      certificate := .k4 0 [0, 1, 2, 5, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7460
      mask := 5224738519868066830
      certificate := .k4 0 [0, 2, 3, 7, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8228
      mask := 10205705589498142
      certificate := .k4 0 [0, 1, 4, 5, 6, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 37
      mask := 2701172992
      certificate := .sharedThree 1 3 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 293
      mask := 38656344092
      certificate := .k4 0 [0, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 549
      mask := 14074169742352384
      certificate := .k4 1 [1, 6, 4] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1317
      mask := 11356169750708224
      certificate := .k4 3 [3, 6, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2085
      mask := 864691130645282830
      certificate := .k4 0 [0, 2, 7, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5669
      mask := 14990763007942934
      certificate := .k4 0 [0, 1, 4, 5, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8741
      mask := 4945032655210096910
      certificate := .k4 0 [0, 1, 2, 7, 6, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 38
      mask := 2711683072
      certificate := .sharedThree 2 3 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1574
      mask := 83563492566016
      certificate := .k4 1 [1, 2, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2086
      mask := 864691130661994510
      certificate := .k4 0 [0, 3, 7, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5926
      mask := 13220466132254
      certificate := .k4 0 [0, 1, 3, 5, 2, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7462
      mask := 5225301469825600782
      certificate := .k4 0 [0, 1, 3, 7, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 39
      mask := 2728525824
      certificate := .sharedThree 2 3 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 295
      mask := 43268440090
      certificate := .k4 0 [0, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1063
      mask := 2893916248498176
      certificate := .k4 1 [1, 6, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1319
      mask := 11894518399903744
      certificate := .k4 1 [1, 5, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2087
      mask := 864691130711867406
      certificate := .k4 0 [0, 2, 7, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4135
      mask := 2450101136024808448
      certificate := .k4 1 [1, 2, 5, 3, 7] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6439
      mask := 2814751177590046
      certificate := .k4 0 [0, 1, 2, 6, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets04 : Array (List HardEntry) := #[
  [
    { origin := 32
      code := 5442549446321122590
      certificate := .residual 3124966165754280
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 800
      code := 6028513861510391070
      certificate := .residual 4350117082851461
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1056
      code := 5157704203357547550
      certificate := .residual 712285307943888
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5408
      code := 6141095451432771870
      certificate := .residual 2042187201179218
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5664
      code := 6164798601768330270
      certificate := .residual 2923892976750376
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 33
      code := 5155444970076253470
      certificate := .residual 4411689737676938
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 801
      code := 7680136727664026910
      certificate := .residual 4189975189770272
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1057
      code := 6163132537773911070
      certificate := .residual 1203904415154000
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5409
      code := 6425956923956977950
      certificate := .residual 2745992379589202
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5665
      code := 5590589649278592030
      certificate := .residual 4408547969025546
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 34
      code := 7180591349940890910
      certificate := .residual 1988155130967488
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 802
      code := 8254336871360390430
      certificate := .residual 4251547840983072
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1058
      code := 6166509980601707550
      certificate := .residual 4410442049490185
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5410
      code := 5564643495222370590
      certificate := .residual 4411689737676940
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5666
      code := 6164798327964165150
      certificate := .residual 3915966730421770
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 35
      code := 5451206997120134430
      certificate := .residual 138098946286448
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 803
      code := 3725758281434031390
      certificate := .residual 103291382048625
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1059
      code := 6022957742479272990
      certificate := .residual 4410442049490184
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5411
      code := 6137730945851777310
      certificate := .residual 4231425101817543
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5667
      code := 5590589375474426910
      certificate := .residual 2923891068342056
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 36
      code := 6022942894774037790
      certificate := .residual 2059468769785392
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 804
      code := 6455296725831148830
      certificate := .residual 4409479976808704
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1060
      code := 3862349361617464350
      certificate := .residual 350147663258736
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5412
      code := 5563521993362039070
      certificate := .residual 1549893534162514
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5668
      code := 3865088805855421470
      certificate := .residual 3486842687426344
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 37
      code := 5446490925729066270
      certificate := .residual 629718082397152
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 805
      code := 6425393974011782430
      certificate := .residual 4251412542173217
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1061
      code := 6427714773259545630
      certificate := .residual 342449173455088
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5413
      code := 5132297956764606750
      certificate := .residual 1994254564389922
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5669
      code := 3288636849645020190
      certificate := .residual 4346975314200074
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 38
      code := 8410695253242359070
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 7, 6] 0 1 3 5 6 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 806
      code := 5420528307154740510
      certificate := .residual 4255832076101653
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1062
      code := 6166493488178949150
      certificate := .residual 3045114133599784
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5414
      code := 6453044909064249630
      certificate := .residual 936850218047408
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5670
      code := 3865088395149173790
      certificate := .residual 3361812862682634
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 39
      code := 8410690872375717150
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 7, 6] 2 0 1 5 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 807
      code := 3714161027670631710
      certificate := .residual 621177753307105
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1063
      code := 6022941250056514590
      certificate := .residual 4410442049490186
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5415
      code := 5564641296232669470
      certificate := .residual 1379760778107938
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5671
      code := 3288636438938772510
      certificate := .residual 3486838896299816
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
