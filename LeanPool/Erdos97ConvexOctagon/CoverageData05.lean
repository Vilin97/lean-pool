/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 40–47 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets05 : Array (List PatternEntry) := #[
  [
    { origin := 40
      mask := 2751505408
      certificate := .sharedThree 1 3 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 296
      mask := 47244642586
      certificate := .k4 0 [0, 1, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 552
      mask := 14636853415116800
      certificate := .k4 2 [2, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 808
      mask := 38739705884
      certificate := .k4 0 [0, 2, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1064
      mask := 3096224794165514
      certificate := .k4 0 [0, 1, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4136
      mask := 2450101136058231808
      certificate := .k4 1 [1, 3, 5, 2, 7] 1 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7720
      mask := 88102720924696
      certificate := .k4 0 [0, 3, 4, 1, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10024
      mask := 5228679453010429214
      certificate := .k4 0 [0, 1, 3, 2, 7, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 553
      mask := 14637111113154560
      certificate := .k4 2 [2, 6, 4] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 809
      mask := 38740164636
      certificate := .k4 0 [0, 3, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1065
      mask := 3096224794167306
      certificate := .k4 0 [0, 3, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1321
      mask := 11901114429497344
      certificate := .k4 1 [1, 6, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2089
      mask := 864691130881081372
      certificate := .k4 0 [0, 2, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2345
      mask := 12936350750
      certificate := .k4 0 [0, 2, 3, 4, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6697
      mask := 9646015560838158
      certificate := .k4 0 [0, 3, 1, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8745
      mask := 5224738520187355422
      certificate := .k4 0 [0, 1, 2, 6, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 42
      mask := 2964324352
      certificate := .sharedThree 2 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 298
      mask := 47294971930
      certificate := .k4 0 [0, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 554
      mask := 14637128288829440
      certificate := .k4 2 [2, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1066
      mask := 3096225834338570
      certificate := .k4 0 [0, 1, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1322
      mask := 11901114966353920
      certificate := .k4 1 [1, 3, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2090
      mask := 864691130897793052
      certificate := .k4 0 [0, 3, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2346
      mask := 12936416286
      certificate := .k4 0 [0, 3, 4, 1, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2858
      mask := 27659925520412
      certificate := .k4 0 [0, 2, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 43
      mask := 3238052096
      certificate := .sharedThree 1 3 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 299
      mask := 47546630170
      certificate := .k4 0 [0, 4, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1067
      mask := 3096225834354698
      certificate := .k4 0 [0, 3, 6, 1] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1323
      mask := 11901114966368256
      certificate := .k4 1 [1, 6, 3, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1835
      mask := 10204567423886592
      certificate := .k4 1 [1, 2, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3115
      mask := 4785353781298454
      certificate := .k4 0 [0, 1, 4, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6955
      mask := 11331567976917262
      certificate := .k4 0 [0, 1, 2, 5, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 44
      mask := 3250651136
      certificate := .sharedThree 2 3 0 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 300
      mask := 51541245980
      certificate := .k4 0 [0, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 556
      mask := 14711895076372480
      certificate := .k4 4 [4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 812
      mask := 38991364124
      certificate := .k4 0 [0, 2, 4, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1068
      mask := 3096225851115786
      certificate := .k4 0 [0, 1, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1324
      mask := 12459666374656000
      certificate := .k4 2 [2, 3, 6, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1580
      mask := 83992990187520
      certificate := .k4 2 [2, 3, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2092
      mask := 864691130964377628
      certificate := .k4 0 [0, 3, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2860
      mask := 844424984742926
      certificate := .k4 0 [0, 2, 3, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5932
      mask := 13220751409182
      certificate := .k4 0 [0, 2, 4, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 45
      mask := 3267493888
      certificate := .sharedThree 2 3 1 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 301
      mask := 51891929116
      certificate := .k4 0 [0, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 557
      mask := 14724659726516224
      certificate := .k4 2 [2, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 813
      mask := 38991822876
      certificate := .k4 0 [0, 4, 3, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1069
      mask := 3096225851130122
      certificate := .k4 0 [0, 1, 6, 3] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3629
      mask := 11330468951632138
      certificate := .k4 0 [0, 1, 3, 6, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3885
      mask := 13603437037027348
      certificate := .k4 0 [0, 2, 4, 6, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4397
      mask := 7211547920209805312
      certificate := .k4 2 [2, 6, 7, 5, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 46
      mask := 3288384512
      certificate := .sharedThree 1 3 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 302
      mask := 55835164700
      certificate := .k4 0 [0, 2, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 558
      mask := 15762772373536768
      certificate := .k4 3 [3, 4, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1326
      mask := 12459667381288960
      certificate := .k4 2 [2, 6, 3, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2862
      mask := 844425018884366
      certificate := .k4 0 [0, 1, 3, 6, 2] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7726
      mask := 88133020574986
      certificate := .k4 0 [0, 1, 3, 2, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10030
      mask := 5233255336936811534
      certificate := .k4 0 [0, 2, 3, 7, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 303
      mask := 55836147740
      certificate := .k4 0 [0, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 559
      mask := 15763012891705344
      certificate := .k4 3 [3, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2095
      mask := 936748743977861148
      certificate := .k4 0 [0, 4, 2, 7] 0 2 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2863
      mask := 844425018885134
      certificate := .k4 0 [0, 3, 2, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4399
      mask := 7244053197997211648
      certificate := .k4 2 [2, 5, 7, 6, 3] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5679
      mask := 15762892398945280
      certificate := .k4 1 [1, 2, 4, 6, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7727
      mask := 88133020640268
      certificate := .k4 0 [0, 2, 3, 1, 4, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8751
      mask := 5225301482995253278
      certificate := .k4 0 [0, 2, 4, 6, 7, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets05 : Array (List HardEntry) := #[
  [
    { origin := 40
      code := 8697794253403925790
      certificate := .residual 3919108499073158
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 808
      code := 5420526108165039390
      certificate := .residual 128355992864626
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1064
      code := 6452484415601863710
      certificate := .residual 1766852221134672
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5416
      code := 6463953189995208990
      certificate := .residual 348792862155248
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5672
      code := 6176849385392563230
      certificate := .residual 4403716935715220
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 41
      code := 7401888936946248990
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 7, 6] 1 0 2 7 5 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 809
      code := 4157549558708593950
      certificate := .residual 4347907321983232
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1065
      code := 6461191191255936030
      certificate := .residual 2396827539183955
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5417
      code := 4157549567290302750
      certificate := .residual 4346824990222857
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5673
      code := 5157704223821521950
      certificate := .residual 4377740973378195
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 42
      code := 7685063775813315870
      certificate := .residual 3919108499073155
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 810
      code := 4149305811566880030
      certificate := .residual 4251547840983073
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1066
      code := 7171799521858513950
      certificate := .residual 2509119394140465
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5418
      code := 3869323589185102110
      certificate := .residual 4346824990222856
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5674
      code := 3860667531440808990
      certificate := .residual 4334447695825300
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 43
      code := 7181790898371636510
      certificate := .residual 3794986058614022
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 811
      code := 3140514888198677790
      certificate := .residual 4254869999757333
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1067
      code := 6424318531947555870
      certificate := .residual 2526707417338164
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5419
      code := 3726822759056728350
      certificate := .residual 333397787280880
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5675
      code := 2862200060419630110
      certificate := .residual 4308471733488275
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 44
      code := 7185710678799494430
      certificate := .residual 156055055194867
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 812
      code := 3139951938278810910
      certificate := .residual 119697331455858
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1068
      code := 5991979564789754910
      certificate := .residual 2771134040222913
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5420
      code := 3293355667400352030
      certificate := .residual 3302134262631682
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5676
      code := 6176836187159454750
      certificate := .residual 935803625707443
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 45
      code := 8189454433089957150
      certificate := .residual 3919108499073156
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 813
      code := 5996977927473358110
      certificate := .residual 612398829144033
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1069
      code := 3145300087386762270
      certificate := .residual 2286249345264866
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5421
      code := 4149308010581909790
      certificate := .residual 2746007415644754
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5677
      code := 3857289827626705950
      certificate := .residual 1006155204695987
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 46
      code := 8410695252974972190
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 7, 6] 2 0 1 5 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 814
      code := 6453036656276563230
      certificate := .residual 4409615268393216
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1070
      code := 3136574496252718110
      certificate := .residual 3606055243924117
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5422
      code := 3862203534337040670
      certificate := .residual 4231442020591303
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5678
      code := 6022957767204725790
      certificate := .residual 3915696147353088
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 47
      code := 8697798634003180830
      certificate := .residual 4411569478585478
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 815
      code := 4155289489154008350
      certificate := .residual 4348042613567744
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1071
      code := 2849470020007848990
      certificate := .residual 3602702921417377
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5423
      code := 3285751578126639390
      certificate := .residual 1479526919118418
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5679
      code := 6020705941856117790
      certificate := .residual 2317464136286432
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
