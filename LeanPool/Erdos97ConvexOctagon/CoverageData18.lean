/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 144–151 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets18 : Array (List PatternEntry) := #[
  [
    { origin := 144
      mask := 3940649673949198
      certificate := .sharedThree 0 6 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 400
      mask := 81365504647168
      certificate := .k4 1 [1, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 656
      mask := 2882303764279590912
      certificate := .k4 2 [2, 3, 7] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4496
      mask := 19980188459294
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7056
      mask := 11821950135512326
      certificate := .k4 0 [0, 1, 2, 3, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7312
      mask := 15762891381735436
      certificate := .k4 0 [0, 2, 3, 4, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 145
      mask := 6192449487634454
      certificate := .sharedThree 0 6 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 401
      mask := 83564031377408
      certificate := .k4 2 [2, 3, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 657
      mask := 2882304486024413184
      certificate := .k4 3 [3, 4, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 913
      mask := 14294207430668
      certificate := .k4 0 [0, 3, 5, 2] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1169
      mask := 6755726198833152
      certificate := .k4 2 [2, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1681
      mask := 167727879684096
      certificate := .k4 2 [2, 4, 3, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2193
      mask := 3026577977501548544
      certificate := .k4 3 [3, 7, 5, 4] 1 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4497
      mask := 19980189442334
      certificate := .k4 0 [0, 1, 5, 4, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7313
      mask := 15762908789104906
      certificate := .k4 0 [0, 1, 3, 4, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 146
      mask := 7318349394477082
      certificate := .sharedThree 0 6 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 914
      mask := 14294255730700
      certificate := .k4 0 [0, 2, 3, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1170
      mask := 6755726199357440
      certificate := .k4 2 [2, 4, 3, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1682
      mask := 167819689852952
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3474
      mask := 10204567423821062
      certificate := .k4 0 [0, 1, 2, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4242
      mask := 3470253037820313600
      certificate := .k4 3 [3, 6, 5, 7, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5522
      mask := 12384900068041994
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6546
      mask := 5066875998979358
      certificate := .k4 0 [0, 1, 2, 6, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7314
      mask := 15762908828991500
      certificate := .k4 0 [0, 2, 3, 4, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 147
      mask := 7881299347898396
      certificate := .sharedThree 0 6 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 403
      mask := 83564566151168
      certificate := .k4 2 [2, 3, 5] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 659
      mask := 2882457693156016128
      certificate := .k4 2 [2, 5, 7] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1171
      mask := 6755727004663808
      certificate := .k4 2 [2, 4, 6, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1683
      mask := 167853781155864
      certificate := .k4 0 [0, 3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2451
      mask := 3320013005078
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4243
      mask := 3472436674623987712
      certificate := .k4 1 [1, 5, 7, 4, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4499
      mask := 19980523413790
      certificate := .k4 0 [0, 1, 5, 4, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5523
      mask := 12384900068107276
      certificate := .k4 0 [0, 2, 3, 1, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 148
      mask := 9851624187166720
      certificate := .sharedThree 2 6 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 660
      mask := 2882471608839045120
      certificate := .k4 4 [4, 5, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1172
      mask := 6834737955995648
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2452
      mask := 3320013005846
      certificate := .k4 0 [0, 4, 2, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2964
      mask := 2533275881131022
      certificate := .k4 0 [0, 2, 3, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 149
      mask := 9851624772075520
      certificate := .sharedThree 3 6 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 917
      mask := 18833434804244
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1173
      mask := 6834978474164224
      certificate := .k4 3 [3, 5, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9877
      mask := 2882462239385847070
      certificate := .k4 0 [0, 1, 3, 2, 7, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 150
      mask := 9851774508728320
      certificate := .sharedThree 4 6 0 1 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 406
      mask := 88390434291712
      certificate := .k4 2 [2, 4, 5] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 918
      mask := 18834253676568
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1174
      mask := 6835011760160768
      certificate := .k4 3 [3, 4, 5, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1430
      mask := 7696631737358
      certificate := .k4 0 [0, 3, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2454
      mask := 3338028458266
      certificate := .k4 0 [0, 1, 4, 5, 3] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2966
      mask := 2533275885323278
      certificate := .k4 0 [0, 2, 3, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 151
      mask := 10414574138303744
      certificate := .sharedThree 1 6 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 407
      mask := 88409485869056
      certificate := .k4 3 [3, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 663
      mask := 3026418952310892544
      certificate := .k4 1 [1, 3, 7] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2455
      mask := 3338028460058
      certificate := .k4 0 [0, 4, 3, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3735
      mask := 11348099792371736
      certificate := .k4 0 [0, 3, 4, 6, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6551
      mask := 5073464481836032
      certificate := .k4 1 [1, 5, 6, 2, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets18 : Array (List HardEntry) := #[
  [
    { origin := 1168
      code := 3722585502941015070
      certificate := .residual 2771150958996673
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5520
      code := 8371515816107761950
      certificate := .residual 3363706943147266
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5776
      code := 6137724364641592350
      certificate := .residual 4241517474354721
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1169
      code := 7149895188114140190
      certificate := .residual 2517915237077297
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5521
      code := 4149307735708197150
      certificate := .residual 2306700892652133
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5777
      code := 5563515412151854110
      certificate := .residual 4247019340043541
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1170
      code := 5420513034283084830
      certificate := .residual 3043242714776213
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5522
      code := 3862203259463328030
      certificate := .residual 2965322298178242
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5778
      code := 5559643761362396190
      certificate := .residual 1978395488873556
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1171
      code := 5132287056177884190
      certificate := .residual 3039890392269473
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5523
      code := 4147064731987534110
      certificate := .residual 4161421172656834
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5779
      code := 5559574762712785950
      certificate := .residual 1978395488873553
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1172
      code := 4158101616623447070
      certificate := .residual 1765752963262288
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5524
      code := 3858838753882333470
      certificate := .residual 3475098603595589
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5780
      code := 3138394620144706590
      certificate := .residual 3340489419434386
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1173
      code := 4158101496834124830
      certificate := .residual 3089358348928550
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5525
      code := 3284629801392595230
      certificate := .residual 3668715729995458
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5781
      code := 5417216306472084510
      certificate := .residual 3763801341077905
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1174
      code := 4158097115967482910
      certificate := .residual 2316488913924192
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5526
      code := 6428199515901845790
      certificate := .residual 3668509100238535
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5782
      code := 3140501816999470110
      certificate := .residual 3045523837212193
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 1175
      code := 7185710407163735070
      certificate := .residual 3793512884687236
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5527
      code := 6141095039656976670
      certificate := .residual 2675655733895762
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5783
      code := 3138258813278807070
      certificate := .residual 3051025702901013
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
