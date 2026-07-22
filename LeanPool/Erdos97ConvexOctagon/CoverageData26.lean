/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 208–215 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets26 : Array (List PatternEntry) := #[
  [
    { origin := 464
      mask := 1970324836992262
      certificate := .k4 0 [0, 1, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 720
      mask := 5227553267483410432
      certificate := .k4 2 [2, 6, 7] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 976
      mask := 27526999048216
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1232
      mask := 10146294448783360
      certificate := .k4 2 [2, 3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2000
      mask := 37155559480754176
      certificate := .k4 2 [2, 3, 6, 4] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2512
      mask := 6609957823766
      certificate := .k4 0 [0, 1, 4, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5072
      mask := 3377713701322782
      certificate := .k4 0 [0, 3, 4, 6, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7376
      mask := 2450103332877533454
      certificate := .k4 0 [0, 1, 3, 7, 5, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 209
      mask := 3530822107861680128
      certificate := .sharedThree 2 7 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 465
      mask := 1970324841365510
      certificate := .k4 0 [0, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 721
      mask := 5230931826184290304
      certificate := .k4 4 [4, 6, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 977
      mask := 27527250706456
      certificate := .k4 0 [0, 4, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1489
      mask := 19971597936922
      certificate := .k4 0 [0, 1, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1745
      mask := 4785366667314432
      certificate := .k4 1 [1, 2, 4, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2001
      mask := 37155576594038784
      certificate := .k4 2 [2, 4, 6, 3] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2257
      mask := 4941012041839280128
      certificate := .k4 2 [2, 7, 6, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 210
      mask := 3530822108680552448
      certificate := .sharedThree 3 7 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 978
      mask := 27629809827864
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2514
      mask := 6609957889046
      certificate := .k4 0 [0, 2, 4, 5, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2770
      mask := 22153443476758
      certificate := .k4 0 [0, 1, 2, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3794
      mask := 13583392424748032
      certificate := .k4 1 [1, 2, 5, 4, 6] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7378
      mask := 2450103345712627990
      certificate := .k4 0 [0, 1, 4, 7, 5, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 211
      mask := 3544614381717291008
      certificate := .sharedThree 6 7 0 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 979
      mask := 27630329921560
      certificate := .k4 0 [0, 4, 5, 3] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1747
      mask := 4876746386071808
      certificate := .k4 1 [1, 5, 4, 6] 0 1 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2003
      mask := 37717646887862534
      certificate := .k4 0 [0, 1, 2, 6] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6611
      mask := 5656326743654400
      certificate := .k4 2 [2, 6, 4, 5, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 212
      mask := 4827858800545562624
      certificate := .sharedThree 2 7 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 724
      mask := 5332261962061465600
      certificate := .k4 1 [1, 3, 7] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 980
      mask := 27659874598936
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1236
      mask := 10155381459255296
      certificate := .k4 2 [2, 4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1492
      mask := 20890724147478
      certificate := .k4 0 [0, 1, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2260
      mask := 4944952390867641344
      certificate := .k4 1 [1, 2, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3284
      mask := 6768886518120448
      certificate := .k4 2 [2, 4, 5, 6, 3] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4308
      mask := 5225019995917912330
      certificate := .k4 0 [0, 1, 3, 7, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5588
      mask := 13590282134093850
      certificate := .k4 0 [0, 3, 5, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6612
      mask := 5656343722721280
      certificate := .k4 2 [2, 6, 4, 5, 3] 1 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 213
      mask := 4827858801665245184
      certificate := .sharedThree 3 7 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 469
      mask := 2613540766613504
      certificate := .k4 3 [3, 5, 6] 0 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 725
      mask := 5332261962061496320
      certificate := .k4 1 [1, 7, 3] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 981
      mask := 27660143034392
      certificate := .k4 0 [0, 3, 5, 4] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3285
      mask := 6768903697989632
      certificate := .k4 2 [2, 5, 3, 4, 6] 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4309
      mask := 5225019995934689546
      certificate := .k4 0 [0, 1, 3, 7, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 214
      mask := 4827859088303980544
      certificate := .sharedThree 4 7 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 726
      mask := 5368853709033832448
      certificate := .k4 3 [3, 7, 6] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 982
      mask := 844424934409478
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1494
      mask := 20891543019802
      certificate := .k4 0 [0, 1, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2262
      mask := 4944952820365262848
      certificate := .k4 2 [2, 4, 7, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2774
      mask := 22162118803484
      certificate := .k4 0 [0, 3, 2, 5, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4566
      mask := 72589249765650
      certificate := .k4 0 [0, 1, 4, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8662
      mask := 2882446700512878878
      certificate := .k4 0 [0, 1, 2, 5, 7, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 215
      mask := 4827932467820232704
      certificate := .sharedThree 5 7 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 471
      mask := 3096225867890698
      certificate := .k4 0 [0, 3, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 983
      mask := 844424934475014
      certificate := .k4 0 [0, 1, 2, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1751
      mask := 5066850228520214
      certificate := .k4 0 [0, 1, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2007
      mask := 37717650176623616
      certificate := .k4 1 [1, 2, 6, 3] 2 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2263
      mask := 4945515340820931584
      certificate := .k4 1 [1, 6, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5079
      mask := 3377744050192414
      certificate := .k4 0 [0, 2, 6, 3, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5847
      mask := 7736108523806
      certificate := .k4 0 [0, 1, 4, 5, 3] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6615
      mask := 5910975890917662
      certificate := .k4 0 [0, 1, 2, 3, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets26 : Array (List HardEntry) := #[
  [
    { origin := 720
      code := 5452053504538993950
      certificate := .residual 1452521171082801
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 976
      code := 6461210423826017310
      certificate := .hubPentagon 0 [0, 2, 3, 4, 1, 5, 6, 7] 0 1 2 4 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1232
      code := 5456273428076129310
      certificate := .residual 4408532936632834
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5584
      code := 3725701255592075550
      certificate := .residual 333399666336240
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5840
      code := 5454295824292439070
      certificate := .residual 3902339872237970
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 721
      code := 3140638170395731230
      certificate := .residual 1461315131301428
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 977
      code := 6171577092312099870
      certificate := .residual 4395315711156496
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1233
      code := 3140091574124375070
      certificate := .residual 4346960281807362
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5585
      code := 6463946565752643870
      certificate := .residual 4410442049490178
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5841
      code := 3148382858651427870
      certificate := .residual 3271220128164241
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 722
      code := 3138395166675068190
      certificate := .residual 1583528430353857
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 978
      code := 5450932123503651870
      certificate := .residual 4395315711156497
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1234
      code := 6454735974900526110
      certificate := .residual 4409479976808713
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5586
      code := 4149308008977588510
      certificate := .residual 2912182781847365
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5842
      code := 5419393459756262430
      certificate := .residual 3612876155704597
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 723
      code := 5444239125110088990
      certificate := .residual 1837173720611152
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 979
      code := 5447603640283130910
      certificate := .residual 3902373695234451
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1235
      code := 6024079260533222430
      certificate := .residual 4409479976808712
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5587
      code := 3862203532732719390
      certificate := .residual 3598334100622018
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5843
      code := 5417150456035599390
      certificate := .residual 3608471665169953
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 724
      code := 3722952748660450590
      certificate := .residual 2399022269020496
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 980
      code := 5442552740523371550
      certificate := .residual 2632264696967472
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1236
      code := 4149453854055951390
      certificate := .residual 350012371774576
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5588
      code := 4147065005256925470
      certificate := .residual 3106040459445954
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5844
      code := 5419386888456299550
      certificate := .residual 2469909343751249
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 725
      code := 5455147406041048350
      certificate := .residual 3531505851210400
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 981
      code := 6031599607043681310
      certificate := .residual 1835341575158228
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1237
      code := 6139488811347962910
      certificate := .residual 342312002915568
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5589
      code := 3285751576522318110
      certificate := .residual 2297771582243429
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5845
      code := 3722600483032458270
      certificate := .residual 3280015953037713
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 726
      code := 6030757140639540510
      certificate := .residual 1382169606544945
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 982
      code := 7184588890747530270
      certificate := .residual 3794595216460164
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1238
      code := 6452484158108298270
      certificate := .residual 1491004078448304
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5590
      code := 3284630074661986590
      certificate := .residual 4091084640762562
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5846
      code := 3866981748828595230
      certificate := .residual 2470991734230100
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 727
      code := 3717098802775614750
      certificate := .residual 1574734484585921
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 983
      code := 5166976377944632350
      certificate := .residual 3915846471280129
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1239
      code := 5420528307154283550
      certificate := .residual 816811093115810
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5591
      code := 6428199789171237150
      certificate := .residual 3364954631334028
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5847
      code := 5995853968068633630
      certificate := .residual 3678840141256225
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
