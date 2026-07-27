/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes

/-! # Coverage certificate data, buckets 184–191 -/

namespace Erdos97Octagon.RawIncidence

/-- Generated monotone-obstruction entries for this hash-bucket group. -/
def patternBuckets23 : Array (List PatternEntry) := #[
  [
    { origin := 184
      mask := 46161898932011008
      certificate := .sharedThree 3 6 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 440
      mask := 153934389837824
      certificate := .k4 2 [2, 5, 3] 2 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 696
      mask := 4035383598751154176
      certificate := .k4 3 [3, 7, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1208
      mask := 9647115026441216
      certificate := .k4 1 [1, 2, 5, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1464
      mask := 13194965286940
      certificate := .k4 0 [0, 3, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2744
      mask := 21032457085974
      certificate := .k4 0 [0, 4, 5, 1, 2] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3000
      mask := 2814764027756826
      certificate := .k4 0 [0, 1, 4, 6, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4024
      mask := 864691169602306076
      certificate := .k4 0 [0, 4, 3, 7, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4280
      mask := 4936789616540910854
      certificate := .k4 0 [0, 1, 2, 7, 6] 0 1 2 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4536
      mask := 26530651176990
      certificate := .k4 0 [0, 4, 5, 3, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 185
      mask := 46162600555184128
      certificate := .sharedThree 4 6 2 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 697
      mask := 4729273289459892224
      certificate := .k4 5 [5, 6, 7] 0 5 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4281
      mask := 4937071092621265920
      certificate := .k4 1 [1, 2, 3, 7, 6] 1 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5561
      mask := 13583684477135130
      certificate := .k4 0 [0, 1, 5, 6, 4] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 442
      mask := 159034060570624
      certificate := .k4 2 [2, 4, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 698
      mask := 4755801206516007936
      certificate := .k4 1 [1, 2, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1466
      mask := 13195031871516
      certificate := .k4 0 [0, 3, 5, 2] 0 2 3 4
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4794
      mask := 143640897855750
      certificate := .k4 0 [0, 1, 2, 5, 4] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5306
      mask := 10133120643916050
      certificate := .k4 0 [0, 1, 4, 2, 6] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 187
      mask := 47287796098400256
      certificate := .sharedThree 2 6 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 443
      mask := 159054181695488
      certificate := .k4 3 [3, 4, 5] 3 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2747
      mask := 21033008506906
      certificate := .k4 0 [0, 3, 4, 5, 1] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8891
      mask := 83602348138774
      certificate := .k4 0 [0, 1, 2, 4, 3, 5] 1 2 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 188
      mask := 47288517641895936
      certificate := .sharedThree 4 6 3 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1212
      mask := 9649315152685056
      certificate := .k4 1 [1, 3, 6, 5] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1724
      mask := 3096538276446490
      certificate := .k4 0 [0, 1, 4, 6] 0 3 4 6
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 701
      mask := 4793518853395185664
      certificate := .k4 2 [2, 6, 7] 1 2 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 957
      mask := 22180019044352
      certificate := .k4 2 [2, 5, 4, 3] 2 3 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1213
      mask := 9649315656001536
      certificate := .k4 1 [1, 6, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2237
      mask := 4797459803704181760
      certificate := .k4 1 [1, 7, 6, 4] 1 2 4 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 2749
      mask := 21033025284122
      certificate := .k4 0 [0, 4, 5, 1, 3] 0 1 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 3517
      mask := 10208965468235014
      certificate := .k4 0 [0, 1, 2, 6, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 6333
      mask := 161099938997268
      certificate := .k4 0 [0, 2, 4, 1, 5] 2 4 5 7
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 190
      mask := 49539595912609792
      certificate := .sharedThree 2 6 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 702
      mask := 4794644756544094208
      certificate := .k4 3 [3, 6, 7] 1 3 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 958
      mask := 23111221182484
      certificate := .k4 0 [0, 2, 4, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1214
      mask := 9649315689539584
      certificate := .k4 1 [1, 3, 5, 6] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1470
      mask := 14294204818702
      certificate := .k4 0 [0, 1, 3, 5] 0 1 2 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1726
      mask := 3377700849451022
      certificate := .k4 0 [0, 3, 6, 2] 0 1 2 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 4030
      mask := 864718221990166528
      certificate := .k4 2 [2, 3, 7, 5, 4] 2 3 4 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 8638
      mask := 2461709777572036878
      certificate := .k4 0 [0, 1, 2, 7, 5, 6] 0 2 3 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 10430
      mask := 1297059413163016474
      certificate := .k4 0 [0, 1, 7, 4, 5, 2, 3] 0 1 3 4
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 191
      mask := 49539598853865472
      certificate := .sharedThree 3 6 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 447
      mask := 161224482398208
      certificate := .k4 1 [1, 5, 4] 1 4 5 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 703
      mask := 4796897386326654976
      certificate := .k4 4 [4, 6, 7] 1 4 6 7
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 959
      mask := 23111222165524
      certificate := .k4 0 [0, 4, 2, 5] 0 2 4 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1215
      mask := 9649315689553920
      certificate := .k4 1 [1, 6, 5, 3] 1 3 5 6
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1983
      mask := 15762908812673024
      certificate := .k4 2 [2, 3, 4, 6] 2 3 5 6
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

/-- Generated exact-table entries for this hash-bucket group. -/
def hardBuckets23 : Array (List HardEntry) := #[
  [
    { origin := 696
      code := 3723520191431927070
      certificate := .residual 4334705125450003
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1208
      code := 3136570097621560350
      certificate := .residual 3532334445632161
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5560
      code := 4149307752687264030
      certificate := .residual 3918146426341516
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5816
      code := 8659170047632204830
      certificate := .residual 3340489419434388
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 697
      code := 3718236806367110430
      certificate := .residual 4334705125450004
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1209
      code := 2849465621376691230
      certificate := .residual 3535686768138901
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5561
      code := 3862203276442394910
      certificate := .residual 2112813121397330
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5817
      code := 8659093382465971230
      certificate := .residual 3253902820010643
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 698
      code := 8697799490038621470
      certificate := .hubPentagon 0 [0, 1, 2, 3, 4, 5, 6, 7] 1 0 2 6 5 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1210
      code := 6172613626560015390
      certificate := .residual 941840974194625
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5562
      code := 4147064748966600990
      certificate := .residual 2605151948312146
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5818
      code := 6460859423606891550
      certificate := .residual 4411419154721159
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 699
      code := 7688164141790618910
      certificate := .residual 3363616748897670
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1211
      code := 6171492124699683870
      certificate := .residual 822483828394932
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5563
      code := 3858838770861400350
      certificate := .residual 3598243905914567
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5819
      code := 7609207234720097310
      certificate := .residual 3918837916117383
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 700
      code := 8696888256942531870
      certificate := .residual 1200337870036819
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1212
      code := 3858394537765923870
      certificate := .residual 831277788613553
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5564
      code := 3284629818371662110
      certificate := .residual 1620108045221458
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5820
      code := 3870997164017771550
      certificate := .residual 1738176031678688
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 701
      code := 8693858840599553310
      certificate := .cycleStrip 0 [0, 1, 2, 3, 4, 5, 6, 7] 0 2 1 6 5 7 3
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1213
      code := 2857909737550801950
      certificate := .residual 3362744870465797
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5565
      code := 6428199532880912670
      certificate := .residual 3483791146706757
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5821
      code := 3294536386179425310
      certificate := .residual 4346719763574272
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 702
      code := 8693789841949943070
      certificate := .hubPentagon 0 [0, 1, 2, 3, 5, 6, 4, 7] 0 1 2 4 3 5
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1214
      code := 2849465617098501150
      certificate := .residual 1785343964149538
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5566
      code := 6141095056636043550
      certificate := .residual 4090932426791618
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5822
      code := 2862190847721661470
      certificate := .residual 4058032185611046
      valid := Certificate.valid_of_validB (by decide) }
  ],
  [
    { origin := 703
      code := 3141767489127671070
      certificate := .residual 4326046471266580
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 1215
      code := 2860161430275517470
      certificate := .residual 837910979072946
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5567
      code := 6425956529160249630
      certificate := .residual 3598638605584066
      valid := Certificate.valid_of_validB (by decide) },
    { origin := 5823
      code := 3285751593451054110
      certificate := .residual 260432403939570
      valid := Certificate.valid_of_validB (by decide) }
  ]
]

end Erdos97Octagon.RawIncidence
