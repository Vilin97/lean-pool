/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 200–207 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets25 : Array (List PatternEntry) := #[
  [
    { origin := 200
      mask := 2666130979403343104
      certificate := .sharedThree 1 7 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 456
      mask := 844424934540544
      certificate := .k4 1 [1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 712
      mask := 5044031582667686912
      certificate := .k4 1 [1, 2, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 968
      mask := 26535146825728
      certificate := .k4 1 [1, 3, 5, 4] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1736
      mask := 3659175787775246
      certificate := .k4 0 [0, 1, 3, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1992
      mask := 36592588799755264
      certificate := .k4 1 [1, 2, 6, 4] 2 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4296
      mask := 4938478466485452812
      certificate := .k4 0 [0, 3, 2, 7, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9416
      mask := 11331619718242590
      certificate := .k4 0 [0, 1, 2, 5, 6, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 201
      mask := 2666130980024090624
      certificate := .sharedThree 3 7 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 713
      mask := 5044031582667718656
      certificate := .k4 1 [1, 7, 2] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4041
      mask := 936748724665877518
      certificate := .k4 0 [0, 3, 7, 2, 1] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6345
      mask := 162882349408518
      certificate := .k4 0 [0, 1, 2, 4, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 202
      mask := 2666131138317123584
      certificate := .sharedThree 4 7 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 714
      mask := 5080623329640054784
      certificate := .k4 2 [2, 7, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 970
      mask := 26568969693184
      certificate := .k4 1 [1, 3, 4, 5] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2762
      mask := 22136264656150
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4554
      mask := 27642410641678
      certificate := .k4 0 [0, 1, 2, 4, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 203
      mask := 2676545553541627904
      certificate := .sharedThree 6 7 0 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 459
      mask := 918092209217792
      certificate := .k4 1 [1, 5, 6] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 715
      mask := 5081186279580812288
      certificate := .k4 1 [1, 7, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1739
      mask := 3659196177842204
      certificate := .k4 0 [0, 4, 2, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2507
      mask := 6597155826702
      certificate := .k4 0 [0, 2, 3, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4299
      mask := 4940730287689629716
      certificate := .k4 0 [0, 2, 4, 7, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4555
      mask := 72567824149516
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 204
      mask := 2954361355555055872
      certificate := .sharedThree 1 7 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 460
      mask := 1407374887961856
      certificate := .k4 1 [1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1228
      mask := 10139696235701248
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1740
      mask := 3659214761230364
      certificate := .k4 0 [0, 4, 3, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4556
      mask := 72567858160906
      certificate := .k4 0 [0, 1, 3, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4812
      mask := 145157021409554
      certificate := .k4 0 [0, 1, 4, 2, 5] 1 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8652
      mask := 2594231895487217694
      certificate := .k4 0 [0, 2, 3, 7, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9932
      mask := 3469392947265430550
      certificate := .k4 0 [0, 4, 7, 5, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10444
      mask := 1442841315032714254
      certificate := .k4 0 [0, 3, 4, 7, 2, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 205
      mask := 2954361355557732352
      certificate := .sharedThree 2 7 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 717
      mask := 5188146774032252928
      certificate := .k4 2 [2, 3, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 973
      mask := 26577595793408
      certificate := .k4 2 [2, 3, 4, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1229
      mask := 10139696237667328
      certificate := .k4 1 [1, 5, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1485
      mask := 19954418066710
      certificate := .k4 0 [0, 1, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2253
      mask := 4938759941378296832
      certificate := .k4 1 [1, 6, 7, 2] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4557
      mask := 72567858290954
      certificate := .k4 0 [0, 1, 3, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6605
      mask := 5642995167264768
      certificate := .k4 2 [2, 5, 6, 3, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7373
      mask := 1729382813176302622
      certificate := .k4 0 [0, 4, 7, 3, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 206
      mask := 2954361531648704512
      certificate := .sharedThree 4 7 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 718
      mask := 5188147633213931520
      certificate := .k4 3 [3, 4, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 974
      mask := 26577596317696
      certificate := .k4 2 [2, 4, 3, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1486
      mask := 19958713033750
      certificate := .k4 0 [0, 4, 5, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2510
      mask := 6597156285454
      certificate := .k4 0 [0, 3, 2, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4302
      mask := 4945521937888601088
      certificate := .k4 1 [1, 5, 6, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4558
      mask := 72569395047436
      certificate := .k4 0 [0, 2, 3, 1, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6606
      mask := 5643012146331648
      certificate := .k4 2 [2, 5, 6, 3, 4] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8654
      mask := 2603854640815098894
      certificate := .k4 0 [0, 2, 7, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10702
      mask := 5228698273575021824
      certificate := .k4 1 [1, 2, 3, 7, 6, 4, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 207
      mask := 2965901829600182272
      certificate := .sharedThree 6 7 0 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 463
      mask := 1483241192226816
      certificate := .k4 2 [2, 5, 6] 0 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1231
      mask := 10139696237797376
      certificate := .k4 1 [1, 5, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4303
      mask := 4946150858537591808
      certificate := .k4 1 [1, 5, 6, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6863
      mask := 10215562540491022
      certificate := .k4 0 [0, 1, 5, 6, 2] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10959
      mask := 5224741857310893078
      certificate := .k4 0 [0, 2, 4, 3, 7, 6, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets25 : Array (List HardEntry) := #[
  [
    { origin := 712
      code := 6022942919503668510
      certificate := .residual 2400121526892880
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1224
      code := 6139399885039365150
      certificate := .residual 2912406333990722
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5576
      code := 7653108657063256350
      certificate := .residual 1094062862338992
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5832
      code := 6028513859379717150
      certificate := .residual 3911135697111442
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 713
      code := 5446490950458696990
      certificate := .residual 4410727664945291
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1225
      code := 5995847646916930590
      certificate := .residual 2317541180409957
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5577
      code := 3716962188460089630
      certificate := .residual 1872071338358818
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5833
      code := 7607518384860226590
      certificate := .residual 4403716935715218
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 714
      code := 3140087327753790750
      certificate := .residual 2968558023252640
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1226
      code := 5131169712601328670
      certificate := .residual 3545814802741570
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5578
      code := 8227326153098584350
      certificate := .residual 1086366280887216
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5834
      code := 7580567156377052190
      certificate := .residual 3349285244307857
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 715
      code := 6030757277541623070
      certificate := .residual 1382169606544948
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1227
      code := 5991922390405770270
      certificate := .residual 4249238479218882
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5579
      code := 6137715140914110750
      certificate := .residual 2426495847872546
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5835
      code := 7653172303111971870
      certificate := .residual 2469909343751252
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 716
      code := 6028514273820960030
      certificate := .residual 1504382905597377
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1228
      code := 5130608961671162910
      certificate := .residual 4169987741963461
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5580
      code := 8661985203826909470
      certificate := .residual 3362880162050306
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5836
      code := 3860514699801584670
      certificate := .residual 4241652773164577
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 717
      code := 3714855935957034270
      certificate := .residual 1390963566763569
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1229
      code := 2860161297651624990
      certificate := .residual 3301172189950215
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5581
      code := 6176848712146018590
      certificate := .residual 348790983099888
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5837
      code := 3284062743591183390
      certificate := .residual 4246057263699221
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 718
      code := 6020691094155060510
      certificate := .residual 4411689737676939
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1230
      code := 2851717177199324190
      certificate := .residual 346043814129778
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5582
      code := 4157549565685981470
      certificate := .residual 3361662538705416
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5838
      code := 3292772941797319710
      certificate := .residual 1978410524929108
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 719
      code := 6029347686639494430
      certificate := .residual 3532605094632096
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1231
      code := 5995847642638740510
      certificate := .residual 2316488913924193
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5583
      code := 3869323587580780830
      certificate := .residual 3361662538705417
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5839
      code := 3284047350663275550
      certificate := .residual 1978410524929105
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
