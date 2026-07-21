/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.ModularPrefix

/-!
# Kernel-checked bounded C3 certificate

The Boolean certificates cover `27 ≤ m ≤ 6560` in 64-value chunks. Their
soundness is transported through proved modular exponentiation and ternary
prefix lemmas, yielding the headline carry theorem at the end of this file.
-/

namespace GKPCarry

private def finiteCheckAt (m : ℕ) : Bool :=
  decide
    (2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2)

private def finiteCheck (lower count : ℕ) : Bool :=
  (List.range' lower count).all finiteCheckAt

private lemma finiteCheckAt_eq_true_iff (m : ℕ) :
    finiteCheckAt m = true ↔
      2 ≤ (Nat.digits 3
        (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  simp [finiteCheckAt]

private lemma finiteCheck_sound
    {lower count m : ℕ} (hcheck : finiteCheck lower count = true)
    (hmember : m ∈ List.range' lower count) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  have hall : ∀ value ∈ List.range' lower count, finiteCheckAt value = true := by
    simpa [finiteCheck] using hcheck
  exact (finiteCheckAt_eq_true_iff m).mp (hall m hmember)

private theorem finiteCheck_27_90 : finiteCheck 27 64 = true := by decide
private theorem finiteCheck_91_154 : finiteCheck 91 64 = true := by decide
private theorem finiteCheck_155_218 : finiteCheck 155 64 = true := by decide
private theorem finiteCheck_219_282 : finiteCheck 219 64 = true := by decide
private theorem finiteCheck_283_346 : finiteCheck 283 64 = true := by decide
private theorem finiteCheck_347_410 : finiteCheck 347 64 = true := by decide
private theorem finiteCheck_411_474 : finiteCheck 411 64 = true := by decide
private theorem finiteCheck_475_538 : finiteCheck 475 64 = true := by decide
private theorem finiteCheck_539_602 : finiteCheck 539 64 = true := by decide
private theorem finiteCheck_603_666 : finiteCheck 603 64 = true := by decide
private theorem finiteCheck_667_730 : finiteCheck 667 64 = true := by decide
private theorem finiteCheck_731_794 : finiteCheck 731 64 = true := by decide
private theorem finiteCheck_795_858 : finiteCheck 795 64 = true := by decide
private theorem finiteCheck_859_922 : finiteCheck 859 64 = true := by decide
private theorem finiteCheck_923_986 : finiteCheck 923 64 = true := by decide
private theorem finiteCheck_987_1050 : finiteCheck 987 64 = true := by decide
private theorem finiteCheck_1051_1114 : finiteCheck 1051 64 = true := by decide
private theorem finiteCheck_1115_1178 : finiteCheck 1115 64 = true := by decide
private theorem finiteCheck_1179_1242 : finiteCheck 1179 64 = true := by decide
private theorem finiteCheck_1243_1306 : finiteCheck 1243 64 = true := by decide
private theorem finiteCheck_1307_1370 : finiteCheck 1307 64 = true := by decide
private theorem finiteCheck_1371_1434 : finiteCheck 1371 64 = true := by decide
private theorem finiteCheck_1435_1498 : finiteCheck 1435 64 = true := by decide
private theorem finiteCheck_1499_1562 : finiteCheck 1499 64 = true := by decide
private theorem finiteCheck_1563_1626 : finiteCheck 1563 64 = true := by decide
private theorem finiteCheck_1627_1690 : finiteCheck 1627 64 = true := by decide
private theorem finiteCheck_1691_1754 : finiteCheck 1691 64 = true := by decide
private theorem finiteCheck_1755_1818 : finiteCheck 1755 64 = true := by decide
private theorem finiteCheck_1819_1882 : finiteCheck 1819 64 = true := by decide
private theorem finiteCheck_1883_1946 : finiteCheck 1883 64 = true := by decide
private theorem finiteCheck_1947_2010 : finiteCheck 1947 64 = true := by decide
private theorem finiteCheck_2011_2074 : finiteCheck 2011 64 = true := by decide
private theorem finiteCheck_2075_2138 : finiteCheck 2075 64 = true := by decide
private theorem finiteCheck_2139_2202 : finiteCheck 2139 64 = true := by decide
private theorem finiteCheck_2203_2266 : finiteCheck 2203 64 = true := by decide
private theorem finiteCheck_2267_2330 : finiteCheck 2267 64 = true := by decide
private theorem finiteCheck_2331_2394 : finiteCheck 2331 64 = true := by decide
private theorem finiteCheck_2395_2458 : finiteCheck 2395 64 = true := by decide
private theorem finiteCheck_2459_2522 : finiteCheck 2459 64 = true := by decide
private theorem finiteCheck_2523_2586 : finiteCheck 2523 64 = true := by decide
private theorem finiteCheck_2587_2650 : finiteCheck 2587 64 = true := by decide
private theorem finiteCheck_2651_2714 : finiteCheck 2651 64 = true := by decide
private theorem finiteCheck_2715_2778 : finiteCheck 2715 64 = true := by decide
private theorem finiteCheck_2779_2842 : finiteCheck 2779 64 = true := by decide
private theorem finiteCheck_2843_2906 : finiteCheck 2843 64 = true := by decide
private theorem finiteCheck_2907_2970 : finiteCheck 2907 64 = true := by decide
private theorem finiteCheck_2971_3034 : finiteCheck 2971 64 = true := by decide
private theorem finiteCheck_3035_3098 : finiteCheck 3035 64 = true := by decide
private theorem finiteCheck_3099_3162 : finiteCheck 3099 64 = true := by decide
private theorem finiteCheck_3163_3226 : finiteCheck 3163 64 = true := by decide
private theorem finiteCheck_3227_3290 : finiteCheck 3227 64 = true := by decide
private theorem finiteCheck_3291_3354 : finiteCheck 3291 64 = true := by decide
private theorem finiteCheck_3355_3418 : finiteCheck 3355 64 = true := by decide
private theorem finiteCheck_3419_3482 : finiteCheck 3419 64 = true := by decide
private theorem finiteCheck_3483_3546 : finiteCheck 3483 64 = true := by decide
private theorem finiteCheck_3547_3610 : finiteCheck 3547 64 = true := by decide
private theorem finiteCheck_3611_3674 : finiteCheck 3611 64 = true := by decide
private theorem finiteCheck_3675_3738 : finiteCheck 3675 64 = true := by decide
private theorem finiteCheck_3739_3802 : finiteCheck 3739 64 = true := by decide
private theorem finiteCheck_3803_3866 : finiteCheck 3803 64 = true := by decide
private theorem finiteCheck_3867_3930 : finiteCheck 3867 64 = true := by decide
private theorem finiteCheck_3931_3994 : finiteCheck 3931 64 = true := by decide
private theorem finiteCheck_3995_4058 : finiteCheck 3995 64 = true := by decide
private theorem finiteCheck_4059_4122 : finiteCheck 4059 64 = true := by decide
private theorem finiteCheck_4123_4186 : finiteCheck 4123 64 = true := by decide
private theorem finiteCheck_4187_4250 : finiteCheck 4187 64 = true := by decide
private theorem finiteCheck_4251_4314 : finiteCheck 4251 64 = true := by decide
private theorem finiteCheck_4315_4378 : finiteCheck 4315 64 = true := by decide
private theorem finiteCheck_4379_4442 : finiteCheck 4379 64 = true := by decide
private theorem finiteCheck_4443_4506 : finiteCheck 4443 64 = true := by decide
private theorem finiteCheck_4507_4570 : finiteCheck 4507 64 = true := by decide
private theorem finiteCheck_4571_4634 : finiteCheck 4571 64 = true := by decide
private theorem finiteCheck_4635_4698 : finiteCheck 4635 64 = true := by decide
private theorem finiteCheck_4699_4762 : finiteCheck 4699 64 = true := by decide
private theorem finiteCheck_4763_4826 : finiteCheck 4763 64 = true := by decide
private theorem finiteCheck_4827_4890 : finiteCheck 4827 64 = true := by decide
private theorem finiteCheck_4891_4954 : finiteCheck 4891 64 = true := by decide
private theorem finiteCheck_4955_5018 : finiteCheck 4955 64 = true := by decide
private theorem finiteCheck_5019_5082 : finiteCheck 5019 64 = true := by decide
private theorem finiteCheck_5083_5146 : finiteCheck 5083 64 = true := by decide
private theorem finiteCheck_5147_5210 : finiteCheck 5147 64 = true := by decide
private theorem finiteCheck_5211_5274 : finiteCheck 5211 64 = true := by decide
private theorem finiteCheck_5275_5338 : finiteCheck 5275 64 = true := by decide
private theorem finiteCheck_5339_5402 : finiteCheck 5339 64 = true := by decide
private theorem finiteCheck_5403_5466 : finiteCheck 5403 64 = true := by decide
private theorem finiteCheck_5467_5530 : finiteCheck 5467 64 = true := by decide
private theorem finiteCheck_5531_5594 : finiteCheck 5531 64 = true := by decide
private theorem finiteCheck_5595_5658 : finiteCheck 5595 64 = true := by decide
private theorem finiteCheck_5659_5722 : finiteCheck 5659 64 = true := by decide
private theorem finiteCheck_5723_5786 : finiteCheck 5723 64 = true := by decide
private theorem finiteCheck_5787_5850 : finiteCheck 5787 64 = true := by decide
private theorem finiteCheck_5851_5914 : finiteCheck 5851 64 = true := by decide
private theorem finiteCheck_5915_5978 : finiteCheck 5915 64 = true := by decide
private theorem finiteCheck_5979_6042 : finiteCheck 5979 64 = true := by decide
private theorem finiteCheck_6043_6106 : finiteCheck 6043 64 = true := by decide
private theorem finiteCheck_6107_6170 : finiteCheck 6107 64 = true := by decide
private theorem finiteCheck_6171_6234 : finiteCheck 6171 64 = true := by decide
private theorem finiteCheck_6235_6298 : finiteCheck 6235 64 = true := by decide
private theorem finiteCheck_6299_6362 : finiteCheck 6299 64 = true := by decide
private theorem finiteCheck_6363_6426 : finiteCheck 6363 64 = true := by decide
private theorem finiteCheck_6427_6490 : finiteCheck 6427 64 = true := by decide
private theorem finiteCheck_6491_6554 : finiteCheck 6491 64 = true := by decide
private theorem finiteCheck_6555_6560 : finiteCheck 6555 6 = true := by decide

private theorem finiteModularCertificate_27_1050
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 1050) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h90 : m ≤ 90
  · exact finiteCheck_sound finiteCheck_27_90 (by simp; omega)
  by_cases h154 : m ≤ 154
  · exact finiteCheck_sound finiteCheck_91_154 (by simp; omega)
  by_cases h218 : m ≤ 218
  · exact finiteCheck_sound finiteCheck_155_218 (by simp; omega)
  by_cases h282 : m ≤ 282
  · exact finiteCheck_sound finiteCheck_219_282 (by simp; omega)
  by_cases h346 : m ≤ 346
  · exact finiteCheck_sound finiteCheck_283_346 (by simp; omega)
  by_cases h410 : m ≤ 410
  · exact finiteCheck_sound finiteCheck_347_410 (by simp; omega)
  by_cases h474 : m ≤ 474
  · exact finiteCheck_sound finiteCheck_411_474 (by simp; omega)
  by_cases h538 : m ≤ 538
  · exact finiteCheck_sound finiteCheck_475_538 (by simp; omega)
  by_cases h602 : m ≤ 602
  · exact finiteCheck_sound finiteCheck_539_602 (by simp; omega)
  by_cases h666 : m ≤ 666
  · exact finiteCheck_sound finiteCheck_603_666 (by simp; omega)
  by_cases h730 : m ≤ 730
  · exact finiteCheck_sound finiteCheck_667_730 (by simp; omega)
  by_cases h794 : m ≤ 794
  · exact finiteCheck_sound finiteCheck_731_794 (by simp; omega)
  by_cases h858 : m ≤ 858
  · exact finiteCheck_sound finiteCheck_795_858 (by simp; omega)
  by_cases h922 : m ≤ 922
  · exact finiteCheck_sound finiteCheck_859_922 (by simp; omega)
  by_cases h986 : m ≤ 986
  · exact finiteCheck_sound finiteCheck_923_986 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_987_1050 (by simp; omega)

private theorem finiteModularCertificate_1051_2074
    {m : ℕ} (hlower : 1051 ≤ m) (hupper : m ≤ 2074) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h1114 : m ≤ 1114
  · exact finiteCheck_sound finiteCheck_1051_1114 (by simp; omega)
  by_cases h1178 : m ≤ 1178
  · exact finiteCheck_sound finiteCheck_1115_1178 (by simp; omega)
  by_cases h1242 : m ≤ 1242
  · exact finiteCheck_sound finiteCheck_1179_1242 (by simp; omega)
  by_cases h1306 : m ≤ 1306
  · exact finiteCheck_sound finiteCheck_1243_1306 (by simp; omega)
  by_cases h1370 : m ≤ 1370
  · exact finiteCheck_sound finiteCheck_1307_1370 (by simp; omega)
  by_cases h1434 : m ≤ 1434
  · exact finiteCheck_sound finiteCheck_1371_1434 (by simp; omega)
  by_cases h1498 : m ≤ 1498
  · exact finiteCheck_sound finiteCheck_1435_1498 (by simp; omega)
  by_cases h1562 : m ≤ 1562
  · exact finiteCheck_sound finiteCheck_1499_1562 (by simp; omega)
  by_cases h1626 : m ≤ 1626
  · exact finiteCheck_sound finiteCheck_1563_1626 (by simp; omega)
  by_cases h1690 : m ≤ 1690
  · exact finiteCheck_sound finiteCheck_1627_1690 (by simp; omega)
  by_cases h1754 : m ≤ 1754
  · exact finiteCheck_sound finiteCheck_1691_1754 (by simp; omega)
  by_cases h1818 : m ≤ 1818
  · exact finiteCheck_sound finiteCheck_1755_1818 (by simp; omega)
  by_cases h1882 : m ≤ 1882
  · exact finiteCheck_sound finiteCheck_1819_1882 (by simp; omega)
  by_cases h1946 : m ≤ 1946
  · exact finiteCheck_sound finiteCheck_1883_1946 (by simp; omega)
  by_cases h2010 : m ≤ 2010
  · exact finiteCheck_sound finiteCheck_1947_2010 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_2011_2074 (by simp; omega)

private theorem finiteModularCertificate_2075_3098
    {m : ℕ} (hlower : 2075 ≤ m) (hupper : m ≤ 3098) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h2138 : m ≤ 2138
  · exact finiteCheck_sound finiteCheck_2075_2138 (by simp; omega)
  by_cases h2202 : m ≤ 2202
  · exact finiteCheck_sound finiteCheck_2139_2202 (by simp; omega)
  by_cases h2266 : m ≤ 2266
  · exact finiteCheck_sound finiteCheck_2203_2266 (by simp; omega)
  by_cases h2330 : m ≤ 2330
  · exact finiteCheck_sound finiteCheck_2267_2330 (by simp; omega)
  by_cases h2394 : m ≤ 2394
  · exact finiteCheck_sound finiteCheck_2331_2394 (by simp; omega)
  by_cases h2458 : m ≤ 2458
  · exact finiteCheck_sound finiteCheck_2395_2458 (by simp; omega)
  by_cases h2522 : m ≤ 2522
  · exact finiteCheck_sound finiteCheck_2459_2522 (by simp; omega)
  by_cases h2586 : m ≤ 2586
  · exact finiteCheck_sound finiteCheck_2523_2586 (by simp; omega)
  by_cases h2650 : m ≤ 2650
  · exact finiteCheck_sound finiteCheck_2587_2650 (by simp; omega)
  by_cases h2714 : m ≤ 2714
  · exact finiteCheck_sound finiteCheck_2651_2714 (by simp; omega)
  by_cases h2778 : m ≤ 2778
  · exact finiteCheck_sound finiteCheck_2715_2778 (by simp; omega)
  by_cases h2842 : m ≤ 2842
  · exact finiteCheck_sound finiteCheck_2779_2842 (by simp; omega)
  by_cases h2906 : m ≤ 2906
  · exact finiteCheck_sound finiteCheck_2843_2906 (by simp; omega)
  by_cases h2970 : m ≤ 2970
  · exact finiteCheck_sound finiteCheck_2907_2970 (by simp; omega)
  by_cases h3034 : m ≤ 3034
  · exact finiteCheck_sound finiteCheck_2971_3034 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_3035_3098 (by simp; omega)

private theorem finiteModularCertificate_3099_4122
    {m : ℕ} (hlower : 3099 ≤ m) (hupper : m ≤ 4122) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h3162 : m ≤ 3162
  · exact finiteCheck_sound finiteCheck_3099_3162 (by simp; omega)
  by_cases h3226 : m ≤ 3226
  · exact finiteCheck_sound finiteCheck_3163_3226 (by simp; omega)
  by_cases h3290 : m ≤ 3290
  · exact finiteCheck_sound finiteCheck_3227_3290 (by simp; omega)
  by_cases h3354 : m ≤ 3354
  · exact finiteCheck_sound finiteCheck_3291_3354 (by simp; omega)
  by_cases h3418 : m ≤ 3418
  · exact finiteCheck_sound finiteCheck_3355_3418 (by simp; omega)
  by_cases h3482 : m ≤ 3482
  · exact finiteCheck_sound finiteCheck_3419_3482 (by simp; omega)
  by_cases h3546 : m ≤ 3546
  · exact finiteCheck_sound finiteCheck_3483_3546 (by simp; omega)
  by_cases h3610 : m ≤ 3610
  · exact finiteCheck_sound finiteCheck_3547_3610 (by simp; omega)
  by_cases h3674 : m ≤ 3674
  · exact finiteCheck_sound finiteCheck_3611_3674 (by simp; omega)
  by_cases h3738 : m ≤ 3738
  · exact finiteCheck_sound finiteCheck_3675_3738 (by simp; omega)
  by_cases h3802 : m ≤ 3802
  · exact finiteCheck_sound finiteCheck_3739_3802 (by simp; omega)
  by_cases h3866 : m ≤ 3866
  · exact finiteCheck_sound finiteCheck_3803_3866 (by simp; omega)
  by_cases h3930 : m ≤ 3930
  · exact finiteCheck_sound finiteCheck_3867_3930 (by simp; omega)
  by_cases h3994 : m ≤ 3994
  · exact finiteCheck_sound finiteCheck_3931_3994 (by simp; omega)
  by_cases h4058 : m ≤ 4058
  · exact finiteCheck_sound finiteCheck_3995_4058 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_4059_4122 (by simp; omega)

private theorem finiteModularCertificate_4123_5146
    {m : ℕ} (hlower : 4123 ≤ m) (hupper : m ≤ 5146) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h4186 : m ≤ 4186
  · exact finiteCheck_sound finiteCheck_4123_4186 (by simp; omega)
  by_cases h4250 : m ≤ 4250
  · exact finiteCheck_sound finiteCheck_4187_4250 (by simp; omega)
  by_cases h4314 : m ≤ 4314
  · exact finiteCheck_sound finiteCheck_4251_4314 (by simp; omega)
  by_cases h4378 : m ≤ 4378
  · exact finiteCheck_sound finiteCheck_4315_4378 (by simp; omega)
  by_cases h4442 : m ≤ 4442
  · exact finiteCheck_sound finiteCheck_4379_4442 (by simp; omega)
  by_cases h4506 : m ≤ 4506
  · exact finiteCheck_sound finiteCheck_4443_4506 (by simp; omega)
  by_cases h4570 : m ≤ 4570
  · exact finiteCheck_sound finiteCheck_4507_4570 (by simp; omega)
  by_cases h4634 : m ≤ 4634
  · exact finiteCheck_sound finiteCheck_4571_4634 (by simp; omega)
  by_cases h4698 : m ≤ 4698
  · exact finiteCheck_sound finiteCheck_4635_4698 (by simp; omega)
  by_cases h4762 : m ≤ 4762
  · exact finiteCheck_sound finiteCheck_4699_4762 (by simp; omega)
  by_cases h4826 : m ≤ 4826
  · exact finiteCheck_sound finiteCheck_4763_4826 (by simp; omega)
  by_cases h4890 : m ≤ 4890
  · exact finiteCheck_sound finiteCheck_4827_4890 (by simp; omega)
  by_cases h4954 : m ≤ 4954
  · exact finiteCheck_sound finiteCheck_4891_4954 (by simp; omega)
  by_cases h5018 : m ≤ 5018
  · exact finiteCheck_sound finiteCheck_4955_5018 (by simp; omega)
  by_cases h5082 : m ≤ 5082
  · exact finiteCheck_sound finiteCheck_5019_5082 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_5083_5146 (by simp; omega)

private theorem finiteModularCertificate_5147_6170
    {m : ℕ} (hlower : 5147 ≤ m) (hupper : m ≤ 6170) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h5210 : m ≤ 5210
  · exact finiteCheck_sound finiteCheck_5147_5210 (by simp; omega)
  by_cases h5274 : m ≤ 5274
  · exact finiteCheck_sound finiteCheck_5211_5274 (by simp; omega)
  by_cases h5338 : m ≤ 5338
  · exact finiteCheck_sound finiteCheck_5275_5338 (by simp; omega)
  by_cases h5402 : m ≤ 5402
  · exact finiteCheck_sound finiteCheck_5339_5402 (by simp; omega)
  by_cases h5466 : m ≤ 5466
  · exact finiteCheck_sound finiteCheck_5403_5466 (by simp; omega)
  by_cases h5530 : m ≤ 5530
  · exact finiteCheck_sound finiteCheck_5467_5530 (by simp; omega)
  by_cases h5594 : m ≤ 5594
  · exact finiteCheck_sound finiteCheck_5531_5594 (by simp; omega)
  by_cases h5658 : m ≤ 5658
  · exact finiteCheck_sound finiteCheck_5595_5658 (by simp; omega)
  by_cases h5722 : m ≤ 5722
  · exact finiteCheck_sound finiteCheck_5659_5722 (by simp; omega)
  by_cases h5786 : m ≤ 5786
  · exact finiteCheck_sound finiteCheck_5723_5786 (by simp; omega)
  by_cases h5850 : m ≤ 5850
  · exact finiteCheck_sound finiteCheck_5787_5850 (by simp; omega)
  by_cases h5914 : m ≤ 5914
  · exact finiteCheck_sound finiteCheck_5851_5914 (by simp; omega)
  by_cases h5978 : m ≤ 5978
  · exact finiteCheck_sound finiteCheck_5915_5978 (by simp; omega)
  by_cases h6042 : m ≤ 6042
  · exact finiteCheck_sound finiteCheck_5979_6042 (by simp; omega)
  by_cases h6106 : m ≤ 6106
  · exact finiteCheck_sound finiteCheck_6043_6106 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_6107_6170 (by simp; omega)

private theorem finiteModularCertificate_6171_6560
    {m : ℕ} (hlower : 6171 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h6234 : m ≤ 6234
  · exact finiteCheck_sound finiteCheck_6171_6234 (by simp; omega)
  by_cases h6298 : m ≤ 6298
  · exact finiteCheck_sound finiteCheck_6235_6298 (by simp; omega)
  by_cases h6362 : m ≤ 6362
  · exact finiteCheck_sound finiteCheck_6299_6362 (by simp; omega)
  by_cases h6426 : m ≤ 6426
  · exact finiteCheck_sound finiteCheck_6363_6426 (by simp; omega)
  by_cases h6490 : m ≤ 6490
  · exact finiteCheck_sound finiteCheck_6427_6490 (by simp; omega)
  by_cases h6554 : m ≤ 6554
  · exact finiteCheck_sound finiteCheck_6491_6554 (by simp; omega)
  · exact finiteCheck_sound finiteCheck_6555_6560 (by simp; omega)

private theorem finiteModularCertificate
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ (Nat.digits 3
      (powMod 4 m (3 ^ (6 * ternaryLength m)))).count 2 := by
  by_cases h1050 : m ≤ 1050
  · exact finiteModularCertificate_27_1050 hlower h1050
  by_cases h2074 : m ≤ 2074
  · exact finiteModularCertificate_1051_2074 (by omega) h2074
  by_cases h3098 : m ≤ 3098
  · exact finiteModularCertificate_2075_3098 (by omega) h3098
  by_cases h4122 : m ≤ 4122
  · exact finiteModularCertificate_3099_4122 (by omega) h4122
  by_cases h5146 : m ≤ 5146
  · exact finiteModularCertificate_4123_5146 (by omega) h5146
  by_cases h6170 : m ≤ 6170
  · exact finiteModularCertificate_5147_6170 (by omega) h6170
  · exact finiteModularCertificate_6171_6560 (by omega) hupper

/-- For every `m` in the closed interval from `27` through `6560`, the first
`6 * ternaryLength m` little-endian ternary digits of `4 ^ m` contain at least
two digits equal to `2`. -/
theorem four_pow_has_two_ternary_twos_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    hasTwoTernaryTwosBelow (6 * ternaryLength m) (4 ^ m) := by
  rw [hasTwoTernaryTwosBelow_iff_mod, ← powMod_eq_pow_mod]
  exact finiteModularCertificate hlower hupper

/-- Equivalent length-indexed form of the bounded ternary-prefix theorem. -/
theorem four_pow_has_two_ternary_twos_of_length_le_eight
    {m : ℕ} (hlower : 27 ≤ m) (hlength : ternaryLength m ≤ 8) :
    hasTwoTernaryTwosBelow (6 * ternaryLength m) (4 ^ m) := by
  have hupper : m < 3 ^ 8 :=
    (Nat.digits_length_le_iff (b := 3) (by decide) m).mp hlength
  norm_num at hupper
  exact four_pow_has_two_ternary_twos_in_finite_range hlower (by omega)

/-- Bounded C3 carry result: throughout `27 ≤ m ≤ 6560`, doubling
the selected prefix of the ternary expansion of `4 ^ m` produces at least two
outgoing carries. -/
theorem four_pow_prefix_carry_count_ge_two_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    2 ≤ prefixTernaryDoubleCarryCount
      (6 * ternaryLength m) (4 ^ m) := by
  exact two_le_prefixTernaryDoubleCarryCount_of_hasTwoTernaryTwosBelow
    (four_pow_has_two_ternary_twos_in_finite_range hlower hupper)

end GKPCarry
