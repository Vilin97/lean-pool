/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 240–247 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets30 : Array (List PatternEntry) := #[
  [
    { origin := 240
      mask := 593166
      certificate := .k4 0 [0, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 752
      mask := 6341068588064964608
      certificate := .k4 3 [3, 4, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1776
      mask := 5910974516299030
      certificate := .k4 0 [0, 1, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2544
      mask := 9896160601102
      certificate := .k4 0 [0, 2, 3, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4080
      mask := 1441152447988432924
      certificate := .k4 0 [0, 2, 3, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5104
      mask := 5066828754275358
      certificate := .k4 0 [0, 2, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 241
      mask := 658702
      certificate := .k4 0 [0, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 753
      mask := 6341069103461040128
      certificate := .k4 3 [3, 7, 4] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1009
      mask := 1688851001789440
      certificate := .k4 1 [1, 2, 6, 3] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1521
      mask := 26539441782810
      certificate := .k4 0 [0, 4, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1777
      mask := 5910974600577052
      certificate := .k4 0 [0, 3, 2, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2801
      mask := 23244364186902
      certificate := .k4 0 [0, 1, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5105
      mask := 5066828754340894
      certificate := .k4 0 [0, 4, 6, 1, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9969
      mask := 4800925326916157718
      certificate := .k4 0 [0, 1, 2, 7, 6, 5, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 498
      mask := 10133099168031744
      certificate := .k4 1 [1, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 754
      mask := 6341069135673294848
      certificate := .k4 3 [3, 4, 7] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2546
      mask := 9896175283214
      certificate := .k4 0 [0, 2, 1, 3, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4082
      mask := 1441152464967958556
      certificate := .k4 0 [0, 3, 2, 7, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8178
      mask := 9658251872914462
      certificate := .k4 0 [0, 2, 4, 5, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 243
      mask := 723982
      certificate := .k4 0 [0, 2, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 755
      mask := 6341069137552343040
      certificate := .k4 3 [3, 7, 4] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1779
      mask := 5911253683815702
      certificate := .k4 0 [0, 1, 4, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2291
      mask := 5237686817066582016
      certificate := .k4 3 [3, 7, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2547
      mask := 9896177249542
      certificate := .k4 0 [0, 1, 2, 3, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3315
      mask := 9361242003170566
      certificate := .k4 0 [0, 1, 2, 5, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5107
      mask := 5066828837571614
      certificate := .k4 0 [0, 3, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9971
      mask := 4800925344146161946
      certificate := .k4 0 [0, 1, 3, 7, 6, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 756
      mask := 6379349731163766784
      certificate := .k4 4 [4, 7, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1268
      mask := 10225870458322944
      certificate := .k4 2 [2, 5, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1524
      mask := 26569254895642
      certificate := .k4 0 [0, 3, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2292
      mask := 5237783127144792064
      certificate := .k4 3 [3, 7, 6, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4084
      mask := 1441152482348105756
      certificate := .k4 0 [0, 3, 4, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5108
      mask := 5066828854348830
      certificate := .k4 0 [0, 4, 6, 1, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8692
      mask := 3458913532291064846
      certificate := .k4 0 [0, 3, 4, 7, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 501
      mask := 10210064975553536
      certificate := .k4 1 [1, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 757
      mask := 6381600675473653760
      certificate := .k4 3 [3, 7, 6] 3 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1525
      mask := 26573533085722
      certificate := .k4 0 [0, 4, 5, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2293
      mask := 5271957047779262464
      certificate := .k4 3 [3, 6, 7, 5] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7157
      mask := 13584745336284182
      certificate := .k4 0 [0, 4, 6, 5, 1, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 502
      mask := 10216663723016192
      certificate := .k4 3 [3, 5, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 758
      mask := 6999087501654622208
      certificate := .k4 5 [5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2038
      mask := 41095909240520978
      certificate := .k4 0 [0, 1, 4, 6] 1 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2294
      mask := 5305672471796514816
      certificate := .k4 3 [3, 5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4342
      mask := 5802985736688893952
      certificate := .k4 3 [3, 4, 5, 7, 6] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 503
      mask := 10225887635046400
      certificate := .k4 4 [4, 5, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 759
      mask := 7026109099418845184
      certificate := .k4 5 [5, 7, 6] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1527
      mask := 26582156574748
      certificate := .k4 0 [0, 4, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1783
      mask := 5911301213650972
      certificate := .k4 0 [0, 3, 4, 6] 0 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5111
      mask := 5066841640225806
      certificate := .k4 0 [0, 2, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8439
      mask := 13583645823020062
      certificate := .k4 0 [0, 2, 4, 6, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets30 : Array (List HardEntry) := #[
  [
    { origin := 752
      code := 4147201482135594270
      certificate := .residual 1252425101647666
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1008
      code := 5163820946576993310
      certificate := .residual 4346855055058437
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1264
      code := 6427634641840204830
      certificate := .residual 2903612388423490
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5616
      code := 3718088070886252830
      certificate := .residual 1379490129108002
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 753
      code := 8230831648747971870
      certificate := .residual 3746621203614352
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1009
      code := 2851861217024240670
      certificate := .residual 1141835661672162
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1265
      code := 5996977927472901150
      certificate := .residual 2316458848637029
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5617
      code := 8227330533664416030
      certificate := .residual 1077587367712688
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 754
      code := 8661485077465294110
      certificate := .hubPentagon 0 [0, 1, 3, 4, 2, 5, 6, 7] 0 1 2 3 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1010
      code := 2860517809508674590
      certificate := .residual 173612881525105
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1266
      code := 5420525971262499870
      certificate := .residual 3607387453904194
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5618
      code := 6461703848537022750
      certificate := .residual 4411539413806338
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 755
      code := 3714723978626622750
      certificate := .residual 712048544259025
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1011
      code := 3149304534265850910
      certificate := .residual 782514723145680
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1267
      code := 5993052670961740830
      certificate := .residual 4240459566044354
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5619
      code := 7825380016833880350
      certificate := .residual 3918958175202562
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 756
      code := 8694980340888986910
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 5 6 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1012
      code := 2858265988438256670
      certificate := .residual 307506372826356
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1268
      code := 5418843718472002590
      certificate := .residual 4108415090800837
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5364
      code := 6168179608612757790
      certificate := .residual 943464467575728
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5620
      code := 5600379407741149470
      certificate := .residual 278422507013616
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 757
      code := 6453032276462757150
      certificate := .residual 1978884048742608
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1013
      code := 3140075083573324830
      certificate := .residual 2446477549853234
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1269
      code := 2851721579306511390
      certificate := .residual 1986420816143010
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5365
      code := 6455283811053461790
      certificate := .residual 943466375984048
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5621
      code := 8686682433507221790
      certificate := .residual 269643505780208
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 758
      code := 6020706229438997790
      certificate := .residual 158116415101681
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1014
      code := 2851844724601482270
      certificate := .residual 4408427709883909
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1270
      code := 6032720999124986910
      certificate := .residual 1489957486108339
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5366
      code := 6173477856109912350
      certificate := .residual 4411674705290498
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5622
      code := 3867071920391512350
      certificate := .residual 1006138292344752
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 759
      code := 8254352418954896670
      certificate := .residual 1158036741799394
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1015
      code := 2858265979881876510
      certificate := .residual 307506372826353
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1271
      code := 3713174639592238110
      certificate := .residual 1560309065096883
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5367
      code := 7824258500651639070
      certificate := .residual 3919093466686722
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5623
      code := 4155289076868768030
      certificate := .residual 3361797830289928
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
