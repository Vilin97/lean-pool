/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Tactic.NormNum.Prime
public import LeanPool.MarkoffModP.BGS.NumberTheory.RankinPositionalSupportBound

/-!
# Concrete positional data below `2^1248`

The table contains the first 275 odd primes, ending at 1783.  Its product is
strictly larger than `2^2496`.  Hence the joint odd support of every
`p < 2^1248` has fewer than 275 entries.  The precision is intentionally only
a coarse starting choice; later certificate generation may increase it
without changing the support argument.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- The generated positional cap table used for the cutoff at 1248. -/
def rankinCutoff1248CapTable : RankinPositionalCapTable where
  precision := 1000000
  oddPrimeFloors :=
      [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97, 101] ++
      [103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
        193, 197, 199, 211, 223, 227, 229, 233] ++
      [239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
        347, 349, 353, 359, 367, 373, 379, 383] ++
      [389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487,
        491, 499, 503, 509, 521, 523, 541, 547] ++
      [557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647,
        653, 659, 661, 673, 677, 683, 691, 701] ++
      [709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823,
        827, 829, 839, 853, 857, 859, 863, 877] ++
      [881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
        1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049] ++
      [1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151,
        1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229] ++
      [1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319,
        1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429] ++
      [1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
        1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597] ++
      [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697,
        1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783]

private def primeGapLadderCheck : ℕ → List ℕ → Bool
  | _, [] => true
  | previous, floor :: floors =>
      decide floor.Prime && decide (previous ≤ floor) &&
        decide (Nat.count (fun k => (previous + k).Prime) (floor - previous) = 1) &&
        primeGapLadderCheck floor floors

private theorem primeGapLadderCheck_sound (start previous : ℕ) (floors : List ℕ)
    (hstart : previous.primeCounting' = start)
    (hcheck : primeGapLadderCheck previous floors = true) :
    primeFloorLadderValidFrom start floors := by
  induction floors generalizing start previous with
  | nil => trivial
  | cons floor floors ih =>
      simp only [primeGapLadderCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hprime, hle⟩, hgap⟩, htail⟩
      have hcount : floor.primeCounting' = start + 1 := by
        have hadd := Nat.count_add Nat.Prime previous (floor - previous)
        rw [Nat.add_sub_of_le hle] at hadd
        change floor.primeCounting' = previous.primeCounting' +
          Nat.count (fun k => (previous + k).Prime) (floor - previous) at hadd
        exact hadd.trans (by rw [hstart, hgap])
      exact ⟨hprime, hcount, ih (start + 1) floor hcount htail⟩

private theorem primeGapLadderCheck_append (previous : ℕ) (left right : List ℕ) :
    primeGapLadderCheck previous (left ++ right) =
      (primeGapLadderCheck previous left &&
        primeGapLadderCheck (left.getLastD previous) right) := by
  induction left generalizing previous with
  | nil => simp [primeGapLadderCheck]
  | cons floor floors ih =>
      simp only [List.cons_append, primeGapLadderCheck, ih, List.getLastD_cons,
        Bool.and_assoc]

private theorem primeGapLadderCheck_append_of_checks
    (previous : ℕ) (left right : List ℕ)
    (hleft : primeGapLadderCheck previous left = true)
    (hright : primeGapLadderCheck (left.getLastD previous) right = true) :
    primeGapLadderCheck previous (left ++ right) = true := by
  rw [primeGapLadderCheck_append, hleft, hright]
  rfl

private theorem rankinCutoff1248PrimeGapChunk0_check :
    primeGapLadderCheck 2
      [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97, 101] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk1_check :
    primeGapLadderCheck 101
      [103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
        193, 197, 199, 211, 223, 227, 229, 233] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk2_check :
    primeGapLadderCheck 233
      [239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
        347, 349, 353, 359, 367, 373, 379, 383] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk3_check :
    primeGapLadderCheck 383
      [389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487,
        491, 499, 503, 509, 521, 523, 541, 547] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk4_check :
    primeGapLadderCheck 547
      [557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647,
        653, 659, 661, 673, 677, 683, 691, 701] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk5_check :
    primeGapLadderCheck 701
      [709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823,
        827, 829, 839, 853, 857, 859, 863, 877] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk6_check :
    primeGapLadderCheck 877
      [881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
        1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk7_check :
    primeGapLadderCheck 1049
      [1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151,
        1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk8_check :
    primeGapLadderCheck 1229
      [1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319,
        1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk9_check :
    primeGapLadderCheck 1429
      [1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
        1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGapChunk10_check :
    primeGapLadderCheck 1597
      [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697,
        1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783] = true := by
  norm_num [primeGapLadderCheck, Nat.count, List.range_succ, List.countP_cons]

private theorem rankinCutoff1248PrimeGaps_check :
    primeGapLadderCheck 2 rankinCutoff1248CapTable.oddPrimeFloors = true := by
  have htail9 := primeGapLadderCheck_append_of_checks 1429 _ _
    rankinCutoff1248PrimeGapChunk9_check rankinCutoff1248PrimeGapChunk10_check
  have htail8 := primeGapLadderCheck_append_of_checks 1229 _ _
    rankinCutoff1248PrimeGapChunk8_check htail9
  have htail7 := primeGapLadderCheck_append_of_checks 1049 _ _
    rankinCutoff1248PrimeGapChunk7_check htail8
  have htail6 := primeGapLadderCheck_append_of_checks 877 _ _
    rankinCutoff1248PrimeGapChunk6_check htail7
  have htail5 := primeGapLadderCheck_append_of_checks 701 _ _
    rankinCutoff1248PrimeGapChunk5_check htail6
  have htail4 := primeGapLadderCheck_append_of_checks 547 _ _
    rankinCutoff1248PrimeGapChunk4_check htail5
  have htail3 := primeGapLadderCheck_append_of_checks 383 _ _
    rankinCutoff1248PrimeGapChunk3_check htail4
  have htail2 := primeGapLadderCheck_append_of_checks 233 _ _
    rankinCutoff1248PrimeGapChunk2_check htail3
  have htail1 := primeGapLadderCheck_append_of_checks 101 _ _
    rankinCutoff1248PrimeGapChunk1_check htail2
  have htail0 := primeGapLadderCheck_append_of_checks 2 _ _
    rankinCutoff1248PrimeGapChunk0_check htail1
  simpa only [rankinCutoff1248CapTable, List.append_assoc] using htail0

theorem rankinCutoff1248CapTable_check :
    rankinCutoff1248CapTable.check = true := by
  apply (RankinPositionalCapTable.check_eq_true_iff _).mpr
  exact ⟨by decide, primeGapLadderCheck_sound 0 2 _ (by decide)
    rankinCutoff1248PrimeGaps_check⟩

theorem rankinCutoff1248CapTable_valid :
    rankinCutoff1248CapTable.Valid :=
  (RankinPositionalCapTable.check_eq_true_iff
    rankinCutoff1248CapTable).mp
    rankinCutoff1248CapTable_check

theorem rankinCutoff1248CapTable_product :
    2 ^ (2 * 1248) < rankinCutoff1248CapTable.oddPrimeFloors.prod := by
  decide +kernel

theorem rankinCutoff1248CapTable_length :
    rankinCutoff1248CapTable.oddPrimeFloors.length = 275 := by
  decide +kernel

/-- Uniform support-size coverage for the proposed new cutoff. -/
theorem jointOddPrimeList_length_lt_275_of_lt_two_pow_1248
    {p : ℕ} (hpOne : 1 < p) (hp : p < 2 ^ 1248) :
    (jointOddPrimeList p).length < 275 := by
  have hlength := jointOddPrimeList_length_lt_of_lt_pow_of_capTable
    hpOne hp rankinCutoff1248CapTable_valid
      rankinCutoff1248CapTable_product
  rw [rankinCutoff1248CapTable_length] at hlength
  exact hlength

theorem jointOddPrimeList_length_le_rankinCutoff1248CapTable
    {p : ℕ} (hpOne : 1 < p) (hp : p < 2 ^ 1248) :
    (jointOddPrimeList p).length ≤
      rankinCutoff1248CapTable.oddPrimeFloors.length := by
  exact (jointOddPrimeList_length_lt_of_lt_pow_of_capTable
    hpOne hp rankinCutoff1248CapTable_valid
      rankinCutoff1248CapTable_product).le

end BGS.NumberTheory
