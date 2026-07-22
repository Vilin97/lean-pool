/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 104–111 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets13 : Array (List PatternEntry) := #[
  [
    { origin := 104
      mask := 73667283451904
      certificate := .sharedThree 2 5 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 360
      mask := 3298537186560
      certificate := .k4 1 [1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 616
      mask := 47437333426864128
      certificate := .k4 3 [3, 5, 6] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 872
      mask := 9896191862794
      certificate := .k4 0 [0, 3, 1, 5] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1128
      mask := 5348037442421010
      certificate := .k4 0 [0, 1, 4, 6] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1640
      mask := 151734802489610
      certificate := .k4 0 [0, 1, 3, 5] 1 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3944
      mask := 216172823217996058
      certificate := .k4 0 [0, 1, 4, 7, 3] 0 1 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4200
      mask := 2882453452204015616
      certificate := .k4 2 [2, 3, 4, 7, 5] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4712
      mask := 88399018025222
      certificate := .k4 0 [0, 1, 2, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6248
      mask := 97079951122706
      certificate := .k4 0 [0, 1, 4, 3, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6760
      mask := 9663749430469654
      certificate := .k4 0 [0, 4, 5, 6, 1] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7784
      mask := 145857402964230
      certificate := .k4 0 [0, 1, 2, 3, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 105
      mask := 73668403134464
      certificate := .sharedThree 3 5 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 617
      mask := 47498906078019584
      certificate := .k4 3 [3, 6, 5] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1385
      mask := 15842176655163392
      certificate := .k4 3 [3, 5, 6, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2153
      mask := 2594284491612775424
      certificate := .k4 1 [1, 2, 7, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3945
      mask := 216173357640548630
      certificate := .k4 0 [0, 1, 2, 7, 4] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5481
      mask := 11355910711700480
      certificate := .k4 1 [1, 2, 4, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7273
      mask := 14636849117094166
      certificate := .k4 0 [0, 1, 2, 4, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8041
      mask := 5643012094820378
      certificate := .k4 0 [0, 3, 5, 2, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 106
      mask := 73955041869824
      certificate := .sharedThree 4 5 0 1 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 618
      mask := 47507701097299968
      certificate := .k4 3 [3, 5, 6] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1386
      mask := 15842177192034304
      certificate := .k4 3 [3, 6, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3946
      mask := 216173375104516378
      certificate := .k4 0 [0, 1, 3, 7, 4] 0 1 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5482
      mask := 11613041817362702
      certificate := .k4 0 [0, 1, 2, 5, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6250
      mask := 142939223893258
      certificate := .k4 0 [0, 1, 3, 2, 5] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7274
      mask := 14636849117160722
      certificate := .k4 0 [0, 1, 4, 2, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 107
      mask := 75866302334208
      certificate := .sharedThree 1 5 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 363
      mask := 5497560442112
      certificate := .k4 1 [1, 2, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 619
      mask := 47507701634170880
      certificate := .k4 3 [3, 6, 5] 3 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 875
      mask := 9896228028428
      certificate := .k4 0 [0, 3, 2, 5] 0 2 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1387
      mask := 15850733035323392
      certificate := .k4 3 [3, 6, 5, 4] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2411
      mask := 47547747350
      certificate := .k4 0 [0, 2, 4, 3, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5739
      mask := 1441152434818256158
      certificate := .k4 0 [0, 1, 4, 7, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5995
      mask := 19945913592846
      certificate := .k4 0 [0, 3, 2, 4, 5, 1] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7275
      mask := 14636866297946386
      certificate := .k4 0 [0, 1, 4, 2, 6] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 620
      mask := 49698887648149504
      certificate := .k4 4 [4, 5, 6] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 876
      mask := 10038160654360
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2156
      mask := 2594286690635899904
      certificate := .k4 1 [1, 5, 7, 2] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4716
      mask := 88416481992970
      certificate := .k4 0 [0, 1, 3, 4, 5] 1 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6252
      mask := 143628013020434
      certificate := .k4 0 [0, 1, 4, 2, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 109
      mask := 76162655059968
      certificate := .sharedThree 4 5 0 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 621
      mask := 49751664206282752
      certificate := .k4 4 [4, 6, 5] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 877
      mask := 10068225425432
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1133
      mask := 5348308025360658
      certificate := .k4 0 [0, 1, 6, 4] 0 1 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1389
      mask := 15850870474276864
      certificate := .k4 3 [3, 6, 4, 5] 3 4 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1645
      mask := 152456608622592
      certificate := .k4 1 [1, 3, 5, 4] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3437
      mask := 9658291332343808
      certificate := .k4 1 [1, 6, 5, 4, 3] 1 3 4 5
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 366
      mask := 7696581403910
      certificate := .k4 0 [0, 1, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 622
      mask := 49768981514420224
      certificate := .k4 4 [4, 5, 6] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 878
      mask := 10072251957272
      certificate := .k4 0 [0, 3, 4, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1134
      mask := 5629525309408256
      certificate := .k4 1 [1, 2, 4, 6] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1390
      mask := 216172782122402054
      certificate := .k4 0 [0, 1, 2, 7] 0 1 2 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 111
      mask := 80264353611776
      certificate := .sharedThree 2 5 0 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 623
      mask := 49769118953373696
      certificate := .k4 4 [4, 6, 5] 4 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 879
      mask := 10072503615512
      certificate := .k4 0 [0, 4, 3, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1391
      mask := 216172784311632138
      certificate := .k4 0 [0, 1, 3, 7] 0 1 3 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4207
      mask := 2882463232058982424
      certificate := .k4 0 [0, 3, 4, 7, 5] 0 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7279
      mask := 14636977964146966
      certificate := .k4 0 [0, 1, 2, 4, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 7535
      mask := 11017229836574
      certificate := .k4 0 [0, 1, 4, 5, 2, 3] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 9327
      mask := 10212277459422230
      certificate := .k4 0 [0, 2, 4, 6, 5, 3, 1] 0 1 2 4
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets13 : Array (List HardEntry) := #[
  [
    { origin := 104
      code := 6170944581331856670
      certificate := .residual 3911289779080210
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1128
      code := 5131237749192944670
      certificate := .residual 3793753402863879
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5480
      code := 6428269058399658270
      certificate := .residual 3795948131345666
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5736
      code := 8688943183795184670
      certificate := .residual 3911135697111444
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 105
      code := 7175740154322627870
      certificate := .residual 4403871017683986
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1129
      code := 3713030743370787870
      certificate := .residual 2316368651169889
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5481
      code := 4155790866969780510
      certificate := .residual 3303366918432002
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5737
      code := 6019017377682416670
      certificate := .residual 3885159734774419
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 106
      code := 6026829393289555230
      certificate := .residual 4411569478585479
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1130
      code := 5131169845759994910
      certificate := .residual 346164076884082
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5482
      code := 7364891501338026270
      certificate := .residual 1084199734522800
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5738
      code := 5995936430967874590
      certificate := .residual 3772597165951380
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 107
      code := 7175177204402760990
      certificate := .residual 3918988239981703
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1131
      code := 6460928950737792030
      certificate := .residual 4386519886533904
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5483
      code := 7366012866296275230
      certificate := .residual 1084201617241008
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5739
      code := 8657980938202506270
      certificate := .residual 3746621203614355
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 108
      code := 6461140884022897950
      certificate := .residual 1514146473778739
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1132
      code := 6171858560587361310
      certificate := .hubPentagon 0 [0, 2, 3, 4, 1, 6, 7, 5] 0 1 2 7 4 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5484
      code := 6426025797853896990
      certificate := .residual 3794986058614018
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5740
      code := 8688929985562076190
      certificate := .residual 935818687453107
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 109
      code := 6171789023190723870
      certificate := .residual 1765384611160916
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1133
      code := 3148396187577707550
      certificate := .residual 768641746508722
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5485
      code := 7366004198549479710
      certificate := .residual 1092980530566064
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5741
      code := 6166510004257612830
      certificate := .residual 4408277385956864
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 110
      code := 7681264814197320990
      certificate := .residual 1514161535524403
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1134
      code := 3141636390559902750
      certificate := .residual 1202449987870545
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5486
      code := 4158033476963262750
      certificate := .residual 3302404845700354
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5742
      code := 5590049226419266590
      certificate := .residual 2308685135053024
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 111
      code := 7391912953365146910
      certificate := .residual 1765399672906580
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1135
      code := 6032721106497530910
      certificate := .residual 1342760365907412
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5487
      code := 7362639556066402590
      certificate := .residual 1092978647847856
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5743
      code := 5157703687961502750
      certificate := .residual 4066688967914278
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
