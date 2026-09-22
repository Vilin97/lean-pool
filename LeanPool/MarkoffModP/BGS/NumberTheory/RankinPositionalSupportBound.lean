/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.RankinPositionalCoverage
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Product bounds for finite positional prime ladders

The product of the globally sorted odd support divides, up to harmless
overlap, `(p - 1) * (p + 1)`.  A checked literal prefix of the odd primes is
pointwise no larger than any support of the same length.  Combining these two
facts turns one exact primorial comparison into a uniform bound on the number
of exponent slots below a power cutoff.
-/

open scoped BigOperators

namespace BGS.NumberTheory

theorem jointOddPrimeList_prod_le_neighbors_mul
    {p : ℕ} (hp : 1 < p) :
    (jointOddPrimeList p).prod ≤ (p - 1) * (p + 1) := by
  let minusSupport := (p - 1).primeFactors
  let plusSupport := (p + 1).primeFactors
  have hminusProd : (∏ q ∈ minusSupport, q) ∣ p - 1 := by
    simpa [minusSupport] using Nat.prod_primeFactors_dvd (p - 1)
  have hplusProd : (∏ q ∈ plusSupport, q) ∣ p + 1 := by
    simpa [plusSupport] using Nat.prod_primeFactors_dvd (p + 1)
  have hunionProd :
      (∏ q ∈ minusSupport ∪ plusSupport, q) ∣
        (∏ q ∈ minusSupport, q) * (∏ q ∈ plusSupport, q) := by
    refine ⟨∏ q ∈ minusSupport ∩ plusSupport, q, ?_⟩
    simpa [mul_comm] using
      (Finset.prod_union_inter (s₁ := minusSupport) (s₂ := plusSupport)
        (f := fun q : ℕ => q)).symm
  have heraseProd :
      (∏ q ∈ (minusSupport ∪ plusSupport).erase 2, q) ∣
        ∏ q ∈ minusSupport ∪ plusSupport, q := by
    apply Finset.prod_dvd_prod_of_subset
    exact Finset.erase_subset 2 (minusSupport ∪ plusSupport)
  have hdiv :
      (∏ q ∈ (minusSupport ∪ plusSupport).erase 2, q) ∣
        (p - 1) * (p + 1) :=
    heraseProd.trans (hunionProd.trans (Nat.mul_dvd_mul hminusProd hplusProd))
  have hminusPositive : 0 < p - 1 := by omega
  have hplusPositive : 0 < p + 1 := by omega
  have hpositive : 0 < (p - 1) * (p + 1) :=
    Nat.mul_pos hminusPositive hplusPositive
  have hle := Nat.le_of_dvd hpositive hdiv
  change ((jointOddPrimeSupport p).sort (· ≤ ·)).prod ≤
    (p - 1) * (p + 1)
  rw [show ((jointOddPrimeSupport p).sort (· ≤ ·)).prod =
      ∏ q ∈ jointOddPrimeSupport p, q by
    calc
      ((jointOddPrimeSupport p).sort (· ≤ ·)).prod =
          (jointOddPrimeSupport p).toList.prod :=
        (Finset.sort_perm_toList (jointOddPrimeSupport p) (· ≤ ·)).prod_eq
      _ = ∏ q ∈ jointOddPrimeSupport p, q :=
        Finset.prod_toList (jointOddPrimeSupport p)]
  simpa [jointOddPrimeSupport, minusSupport, plusSupport] using hle

theorem capTable_oddPrimeFloors_prod_le_jointOddPrimeList_prod
    {p : ℕ} {table : RankinPositionalCapTable}
    (hvalid : table.Valid)
    (hlength : table.oddPrimeFloors.length ≤
      (jointOddPrimeList p).length) :
    table.oddPrimeFloors.prod ≤ (jointOddPrimeList p).prod := by
  let actual := jointOddPrimeList p
  have hactualNodup : actual.Nodup :=
    Finset.sort_nodup (jointOddPrimeSupport p) (· ≤ ·)
  have hpointwise : List.Forall₂ (· ≤ ·) table.oddPrimeFloors
      (actual.take table.oddPrimeFloors.length) := by
    rw [List.forall₂_iff_get]
    constructor
    · simp [actual, List.length_take, Nat.min_eq_left hlength]
    · intro index hfloorIndex htakeIndex
      have hactualIndex : index < actual.length :=
        hfloorIndex.trans_le hlength
      have hcapEq := table.oddCapAt_lowerPrime_eq_nthPrime
        hvalid hfloorIndex
      change table.oddPrimeFloors.getD index 0 =
        Nat.nth Nat.Prime (index + 1) at hcapEq
      rw [List.getD_eq_getElem table.oddPrimeFloors 0 hfloorIndex] at hcapEq
      have hmember : actual.get ⟨index, hactualIndex⟩ ∈ actual :=
        List.get_mem actual ⟨index, hactualIndex⟩
      have hbound := nthPrime_succ_idxOf_le_jointOddPrimeList p hmember
      have hindexEq :
          actual.idxOf (actual.get ⟨index, hactualIndex⟩) = index := by
        simpa using List.get_idxOf hactualNodup ⟨index, hactualIndex⟩
      rw [hindexEq] at hbound
      have htakeEq :
          (actual.take table.oddPrimeFloors.length).get
              ⟨index, htakeIndex⟩ =
            actual.get ⟨index, hactualIndex⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact (List.getElem_take' hactualIndex hfloorIndex).symm
      rw [htakeEq]
      exact hcapEq.le.trans hbound
  have hprefix := hpointwise.prod_le_prod
  have htakeSublist : List.Sublist
      (actual.take table.oddPrimeFloors.length) actual :=
    List.take_sublist _ _
  have hactualOne : ∀ prime ∈ actual, 1 ≤ prime := by
    intro prime hprime
    rcases (mem_jointOddPrimeList.mp hprime).2 with hminus | hplus
    · exact (Nat.prime_of_mem_primeFactors hminus).one_le
    · exact (Nat.prime_of_mem_primeFactors hplus).one_le
  exact hprefix.trans (htakeSublist.prod_le_prod hactualOne)

theorem jointOddPrimeList_length_lt_of_capTable_prod_gt
    {p : ℕ} {table : RankinPositionalCapTable}
    (hp : 1 < p) (hvalid : table.Valid)
    (hproduct : (p - 1) * (p + 1) < table.oddPrimeFloors.prod) :
    (jointOddPrimeList p).length < table.oddPrimeFloors.length := by
  by_contra hnot
  have hlength : table.oddPrimeFloors.length ≤
      (jointOddPrimeList p).length := by omega
  have htableSupport :=
    capTable_oddPrimeFloors_prod_le_jointOddPrimeList_prod hvalid hlength
  have hsupportNeighbors := jointOddPrimeList_prod_le_neighbors_mul hp
  exact (not_lt_of_ge (htableSupport.trans hsupportNeighbors)) hproduct

theorem neighbors_mul_lt_two_pow_two_mul
    {p exponent : ℕ} (hpOne : 1 < p) (hp : p < 2 ^ exponent) :
    (p - 1) * (p + 1) < 2 ^ (2 * exponent) := by
  have hminus : p - 1 < 2 ^ exponent :=
    (Nat.sub_le p 1).trans_lt hp
  have hplus : p + 1 ≤ 2 ^ exponent := by omega
  have hplusPos : 0 < p + 1 := by omega
  have hneighbors : (p - 1) * (p + 1) <
      (2 ^ exponent) * (2 ^ exponent) :=
    (Nat.mul_lt_mul_of_pos_right hminus hplusPos).trans_le
      (Nat.mul_le_mul_left (2 ^ exponent) hplus)
  have hpower : (2 ^ exponent) * (2 ^ exponent) =
      2 ^ (2 * exponent) := by
    rw [← pow_add]
    congr 1
    omega
  rwa [hpower] at hneighbors

theorem jointOddPrimeList_length_lt_of_lt_pow_of_capTable
    {p exponent : ℕ} {table : RankinPositionalCapTable}
    (hpOne : 1 < p) (hp : p < 2 ^ exponent)
    (hvalid : table.Valid)
    (hproduct : 2 ^ (2 * exponent) < table.oddPrimeFloors.prod) :
    (jointOddPrimeList p).length < table.oddPrimeFloors.length := by
  have hneighbors := neighbors_mul_lt_two_pow_two_mul hpOne hp
  apply jointOddPrimeList_length_lt_of_capTable_prod_gt hpOne hvalid
  exact hneighbors.trans hproduct

end BGS.NumberTheory
