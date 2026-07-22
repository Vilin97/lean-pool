/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 176–183 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets22 : Array (List PatternEntry) := #[
  [
    { origin := 176
      mask := 45317471250456832
      certificate := .sharedThree 1 6 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 432
      mask := 150258088673280
      certificate := .k4 3 [3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 688
      mask := 3746995594357374976
      certificate := .k4 2 [2, 7, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1200
      mask := 9642718619772928
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2992
      mask := 2814750908566542
      certificate := .k4 0 [0, 2, 3, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3248
      mask := 5911253688140822
      certificate := .k4 0 [0, 4, 6, 2, 1] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5040
      mask := 2814802716016926
      certificate := .k4 0 [0, 1, 6, 3, 4] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8624
      mask := 2450103371482824990
      certificate := .k4 0 [0, 1, 4, 7, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 177
      mask := 45317471260966912
      certificate := .sharedThree 2 6 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 689
      mask := 3747140729881755648
      certificate := .k4 4 [4, 7, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 945
      mask := 21036749824274
      certificate := .k4 0 [0, 1, 5, 4] 0 1 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1969
      mask := 14636889651806208
      certificate := .k4 2 [2, 4, 6, 3] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2225
      mask := 3747144426516381696
      certificate := .k4 2 [2, 7, 5, 3] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 178
      mask := 45317473951547392
      certificate := .sharedThree 3 6 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 690
      mask := 3747153219658186752
      certificate := .k4 2 [2, 7, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 946
      mask := 22016005645312
      certificate := .k4 1 [1, 2, 4, 5] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1458
      mask := 12270721573146
      certificate := .k4 0 [0, 1, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1970
      mask := 14636990850032640
      certificate := .k4 1 [1, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2994
      mask := 2814750941724942
      certificate := .k4 0 [0, 1, 2, 6, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6578
      mask := 5629778812470558
      certificate := .k4 0 [0, 1, 4, 6, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8626
      mask := 2450107731744489758
      certificate := .k4 0 [0, 1, 2, 7, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10674
      mask := 4945031569138122782
      certificate := .k4 0 [0, 3, 4, 5, 6, 7, 2] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 179
      mask := 45318162740150272
      certificate := .sharedThree 4 6 0 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 691
      mask := 4035225440875446272
      certificate := .k4 3 [3, 4, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10931
      mask := 2892085062324536598
      certificate := .k4 0 [0, 1, 2, 6, 5, 7, 3, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 180
      mask := 45598946237743104
      certificate := .sharedThree 2 6 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 436
      mask := 151735322583040
      certificate := .k4 1 [1, 5, 3] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 692
      mask := 4035225956271521792
      certificate := .k4 3 [3, 7, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 948
      mask := 22042379812864
      certificate := .k4 2 [2, 3, 4, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1204
      mask := 9644916003202048
      certificate := .k4 1 [1, 2, 6, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1716
      mask := 3096224744033294
      certificate := .k4 0 [0, 2, 1, 6] 0 1 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1972
      mask := 14637115403993108
      certificate := .k4 0 [0, 2, 4, 6] 2 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4532
      mask := 26530616970526
      certificate := .k4 0 [0, 1, 4, 5, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9908
      mask := 3458909134246716430
      certificate := .k4 0 [0, 2, 3, 4, 7, 5, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10932
      mask := 2892647981982485526
      certificate := .k4 0 [0, 2, 4, 6, 5, 7, 3, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 181
      mask := 45598948945035264
      certificate := .sharedThree 3 6 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 437
      mask := 153933853491200
      certificate := .k4 2 [2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 693
      mask := 4035225988483776512
      certificate := .k4 3 [3, 4, 7] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 949
      mask := 22042581139456
      certificate := .k4 2 [2, 4, 5, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1205
      mask := 9644916005168128
      certificate := .k4 1 [1, 6, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1717
      mask := 3096224748617998
      certificate := .k4 0 [0, 1, 2, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5301
      mask := 10133099218299916
      certificate := .k4 0 [0, 2, 3, 6, 1] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 182
      mask := 45599642011828224
      certificate := .sharedThree 4 6 1 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 438
      mask := 153934323253248
      certificate := .k4 2 [2, 5, 3] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 694
      mask := 4035225990362824704
      certificate := .k4 3 [3, 7, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 950
      mask := 22136264729600
      certificate := .k4 1 [1, 2, 5, 4] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1974
      mask := 14709567204123648
      certificate := .k4 1 [1, 5, 6, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5302
      mask := 10133099252441354
      certificate := .k4 0 [0, 1, 3, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5558
      mask := 13583667297264918
      certificate := .k4 0 [0, 1, 5, 6, 4] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 183
      mask := 46161896180589568
      certificate := .sharedThree 1 6 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 439
      mask := 153934388264960
      certificate := .k4 2 [2, 3, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 695
      mask := 4035375521259847680
      certificate := .k4 4 [4, 7, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 951
      mask := 22153442501632
      certificate := .k4 1 [1, 2, 4, 5] 1 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1207
      mask := 9644916005298176
      certificate := .k4 1 [1, 6, 5, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1463
      mask := 13194948575260
      certificate := .k4 0 [0, 2, 5, 3] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2231
      mask := 4793032869243053056
      certificate := .k4 1 [1, 5, 7, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4279
      mask := 4936789616540845318
      certificate := .k4 0 [0, 1, 2, 7, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5559
      mask := 13583671592231958
      certificate := .k4 0 [0, 4, 6, 5, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10679
      mask := 4945040532180109598
      certificate := .k4 0 [0, 1, 2, 7, 6, 5, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10935
      mask := 3463977023622956046
      certificate := .k4 0 [0, 2, 3, 5, 7, 4, 6, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets22 : Array (List HardEntry) := #[
  [
    { origin := 688
      code := 5446478027099301150
      certificate := .residual 1180592915422816
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1200
      code := 8190520808261053470
      certificate := .residual 3340489419434384
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5552
      code := 5563522009271558430
      certificate := .residual 3795001091000460
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5808
      code := 8661921326120494110
      certificate := .residual 3792550812012032
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 689
      code := 6020686714341254430
      certificate := .residual 1180591036317280
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1201
      code := 7175172822746557470
      certificate := .residual 1385418510359858
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5553
      code := 5419406829785637150
      certificate := .residual 1440100703976482
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5809
      code := 8659669500771886110
      certificate := .residual 2300146762088672
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 690
      code := 8695556580571833630
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 6 5 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1202
      code := 3714156749630499870
      certificate := .residual 1836423914256849
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5554
      code := 5559581359832490270
      certificate := .residual 2488895302259746
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5810
      code := 8657980676681425950
      certificate := .residual 3495217674597158
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 691
      code := 8262373201368802590
      certificate := .residual 3364699080770950
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1203
      code := 6171834931792604190
      certificate := .residual 2466096771748179
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5555
      code := 7654243378631205150
      certificate := .residual 1076503153121200
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5811
      code := 8185658630621291550
      certificate := .residual 3917740551801223
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 692
      code := 8693867756481373470
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 2 1 6 5 7 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1204
      code := 7172921005954329630
      certificate := .residual 2439850161576241
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5556
      code := 5420588367487361310
      certificate := .residual 271811993518576
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5812
      code := 3862203246043653150
      certificate := .residual 329701636604146
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 693
      code := 8694645099340719390
      certificate := .residual 1201420201910099
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1205
      code := 6137214037938170910
      certificate := .residual 2457438184773940
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5557
      code := 7654234557003260190
      certificate := .residual 3792806362688009
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5813
      code := 6425956498761507870
      certificate := .residual 2300146762088673
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 694
      code := 4154172533488968990
      certificate := .residual 4270231219241126
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1206
      code := 5993101048885570590
      certificate := .residual 2762475386139841
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5558
      code := 7650870051422265630
      certificate := .residual 3792806362688008
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5814
      code := 3150416706054251550
      certificate := .residual 3323172111280787
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 695
      code := 8693798488305788190
      certificate := .hubPentagon 0 [0, 1, 2, 4, 5, 6, 3, 7] 0 1 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1207
      code := 2858191212510735390
      certificate := .residual 2277590691181794
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5559
      code := 8688935906493784350
      certificate := .residual 3916898738204930
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5815
      code := 3150353183487943710
      certificate := .residual 3271220128164244
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
