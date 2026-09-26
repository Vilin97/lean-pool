/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.RankinProfileCertificate
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Matching an actual neighboring factorization to a Rankin profile

This file is the semantic layer between an executable profile payload and the
actual prime factorizations of `p - 1` and `p + 1`.  Odd primes are placed in
one globally increasing support list.  A matching assignment records, at each
actual prime, its side, exact exponent, and a rational weight cap whose lower
prime is no larger than the actual prime.
-/

@[expose] public section

namespace BGS.NumberTheory

open scoped BigOperators

/-- The odd prime support appearing in either neighboring integer. -/
def jointOddPrimeSupport (p : ℕ) : Finset ℕ :=
  ((p - 1).primeFactors ∪ (p + 1).primeFactors).erase 2

/-- The canonical globally increasing list of odd neighboring prime factors. -/
def jointOddPrimeList (p : ℕ) : List ℕ :=
  (jointOddPrimeSupport p).sort (· ≤ ·)

@[simp] theorem mem_jointOddPrimeList {p prime : ℕ} :
    prime ∈ jointOddPrimeList p ↔
      prime ≠ 2 ∧
        (prime ∈ (p - 1).primeFactors ∨
          prime ∈ (p + 1).primeFactors) := by
  simp [jointOddPrimeList, jointOddPrimeSupport, and_or_left]

/-- The neighboring side selected by an actual odd prime. -/
def actualNeighborSide (p prime : ℕ) : NeighborSide :=
  if prime ∈ (p - 1).primeFactors then .minus else .plus

/-- The exact exponent on the side selected by `actualNeighborSide`. -/
def actualNeighborExponent (p prime : ℕ) : ℕ :=
  if prime ∈ (p - 1).primeFactors then
    (p - 1).factorization prime
  else
    (p + 1).factorization prime

namespace RankinOddFactor

/-- One profile factor matches one actual odd neighboring prime. -/
def Matches (factor : RankinOddFactor) (p prime : ℕ) : Prop :=
  factor.side = actualNeighborSide p prime ∧
    factor.exponent = actualNeighborExponent p prime ∧
    factor.weightCap.lowerPrime ≤ prime

end RankinOddFactor

namespace RankinNeighborProfile

/-- A profile matches the complete actual factorization pair.  The total
assignment function is harmless away from the canonical support; its map on
that support is exactly the supplied odd-factor list. -/
def Matches (profile : RankinNeighborProfile) (p : ℕ) : Prop :=
  profile.minusTwoExponent = (p - 1).factorization 2 ∧
    profile.plusTwoExponent = (p + 1).factorization 2 ∧
    ∃ assignment : ℕ → RankinOddFactor,
      profile.oddFactors = (jointOddPrimeList p).map assignment ∧
      ∀ prime ∈ jointOddPrimeList p,
        (assignment prime).Matches p prime

end RankinNeighborProfile

private theorem rankinOddFactor_valid_of_allValid_of_mem
    {factor : RankinOddFactor} {factors : List RankinOddFactor}
    (hall : allRankinOddFactorsValid factors)
    (hmem : factor ∈ factors) :
    factor.Valid := by
  induction factors with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [allRankinOddFactorsValid] at hall
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hall.1
      · exact ih hall.2 hmem

/-- A matching assignment turns profile weight caps into a total rational
prime-weight function.  Primes outside the neighboring supports get weight
one. -/
def assignedPrimeWeight
    (p : ℕ) (profile : RankinNeighborProfile)
    (assignment : ℕ → RankinOddFactor) (prime : ℕ) : ℚ :=
  if prime = 2 then profile.twoWeightCap.weight
  else if prime ∈ jointOddPrimeSupport p then
    (assignment prime).weightCap.weight
  else 1

theorem assignedPrimeWeight_nonneg
    {p : ℕ} {profile : RankinNeighborProfile}
    (hprofile : profile.Valid)
    {assignment : ℕ → RankinOddFactor}
    (hlist :
      profile.oddFactors = (jointOddPrimeList p).map assignment)
    (prime : ℕ) :
    0 ≤ assignedPrimeWeight p profile assignment prime := by
  by_cases htwo : prime = 2
  · simp [assignedPrimeWeight, htwo,
      RationalPrimeWeightCap.weight_nonneg]
  by_cases hsupport : prime ∈ jointOddPrimeSupport p
  · have hprimeList : prime ∈ jointOddPrimeList p := by
      simpa [jointOddPrimeList] using hsupport
    have hfactorMem : assignment prime ∈ profile.oddFactors := by
      rw [hlist]
      exact List.mem_map_of_mem hprimeList
    have hfactorValid : (assignment prime).Valid :=
      rankinOddFactor_valid_of_allValid_of_mem hprofile.2.2.2.1 hfactorMem
    simp [assignedPrimeWeight, htwo, hsupport,
      RationalPrimeWeightCap.weight_nonneg]
  · simp [assignedPrimeWeight, htwo, hsupport]

theorem assignedPrimeWeight_power
    {p : ℕ} {profile : RankinNeighborProfile}
    (hprofile : profile.Valid)
    {assignment : ℕ → RankinOddFactor}
    (hlist :
      profile.oddFactors = (jointOddPrimeList p).map assignment)
    (hmatch :
      ∀ prime ∈ jointOddPrimeList p,
        (assignment prime).Matches p prime)
    (prime : ℕ) (hprime : prime.Prime) :
    1 ≤ (prime : ℚ) *
      (assignedPrimeWeight p profile assignment prime) ^ 12 := by
  by_cases htwo : prime = 2
  · subst prime
    simp only [assignedPrimeWeight, ite_eq_left]
    apply profile.twoWeightCap.one_le_prime_mul_weight_pow_twelve
      hprofile.2.1
    rw [hprofile.2.2.1]
  by_cases hsupport : prime ∈ jointOddPrimeSupport p
  · have hprimeList : prime ∈ jointOddPrimeList p := by
      simpa [jointOddPrimeList] using hsupport
    have hfactorMem : assignment prime ∈ profile.oddFactors := by
      rw [hlist]
      exact List.mem_map_of_mem hprimeList
    have hfactorValid : (assignment prime).Valid :=
      rankinOddFactor_valid_of_allValid_of_mem hprofile.2.2.2.1 hfactorMem
    have hfloor :
        (assignment prime).weightCap.lowerPrime ≤ prime :=
      (hmatch prime hprimeList).2.2
    simpa [assignedPrimeWeight, htwo, hsupport] using
      (assignment prime).weightCap.one_le_prime_mul_weight_pow_twelve
        hfactorValid.2.1 hfloor
  · simp [assignedPrimeWeight, htwo, hsupport]
    exact_mod_cast hprime.one_le

private theorem jointOddPrimeList_map_prod
    {M : Type*} [CommMonoid M]
    (p : ℕ) (f : ℕ → M) :
    ((jointOddPrimeList p).map f).prod =
      ∏ prime ∈ jointOddPrimeSupport p, f prime := by
  exact
    (((jointOddPrimeSupport p).sort_perm_toList (· ≤ ·)).map f).prod_eq.trans
      ((jointOddPrimeSupport p).prod_map_toList f)

private theorem oddDivisorCount_map_assignment
    (p : ℕ) (side : NeighborSide)
    (primes : List ℕ) (assignment : ℕ → RankinOddFactor)
    (hmatch :
      ∀ prime ∈ primes, (assignment prime).Matches p prime) :
    RankinNeighborProfile.oddDivisorCount side
        (primes.map assignment) =
      (primes.map fun prime =>
        if actualNeighborSide p prime = side then
          actualNeighborExponent p prime + 1
        else 1).prod := by
  induction primes with
  | nil => simp [RankinNeighborProfile.oddDivisorCount]
  | cons prime primes ih =>
      have hhead := hmatch prime (by simp)
      have htail :
          ∀ q ∈ primes, (assignment q).Matches p q := by
        intro q hq
        exact hmatch q (by simp [hq])
      simp only [List.map_cons, RankinNeighborProfile.oddDivisorCount,
        List.prod_cons]
      rw [ih htail]
      simp [RankinOddFactor.Matches] at hhead
      rw [hhead.1, hhead.2.1]

private theorem odd_prime_not_mem_both_neighbors
    {p prime : ℕ} (hp : 1 < p) (hodd : prime ≠ 2)
    (hminus : prime ∈ (p - 1).primeFactors)
    (hplus : prime ∈ (p + 1).primeFactors) : False := by
  have hdivMinus : prime ∣ p - 1 :=
    Nat.dvd_of_mem_primeFactors hminus
  have hdivPlus : prime ∣ p + 1 :=
    Nat.dvd_of_mem_primeFactors hplus
  have hdivTwo : prime ∣ 2 := by
    have hdiv := Nat.dvd_sub hdivPlus hdivMinus
    have hsub : p + 1 - (p - 1) = 2 := by omega
    simpa [hsub] using hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdivTwo with hone | htwo
  · exact (Nat.prime_of_mem_primeFactors hminus).ne_one hone
  · exact hodd htwo

private theorem jointOddPrimeList_factor_product_minus
    (p : ℕ) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .minus then
        actualNeighborExponent p prime + 1
      else 1).prod =
      ∏ prime ∈ (p - 1).primeFactors.erase 2,
        ((p - 1).factorization prime + 1) := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p - 1).primeFactors.erase 2,
        ((p - 1).factorization prime + 1)) =
        ∏ prime ∈ (p - 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .minus then
            actualNeighborExponent p prime + 1
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hminus : prime ∈ (p - 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      simp [actualNeighborSide, actualNeighborExponent, hminus]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .minus then
            actualNeighborExponent p prime + 1
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        simp only [jointOddPrimeSupport, Finset.mem_erase,
          Finset.mem_union]
        exact ⟨(Finset.mem_erase.mp hprime).1,
          Or.inl (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 := by
          exact (Finset.mem_erase.mp hsupport).1
        have hnotMinus : prime ∉ (p - 1).primeFactors := by
          intro hminus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hminus⟩)
        simp [actualNeighborSide, hnotMinus]

private theorem jointOddPrimeList_factor_product_plus
    (p : ℕ) (hp : 1 < p) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .plus then
        actualNeighborExponent p prime + 1
      else 1).prod =
      ∏ prime ∈ (p + 1).primeFactors.erase 2,
        ((p + 1).factorization prime + 1) := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p + 1).primeFactors.erase 2,
        ((p + 1).factorization prime + 1)) =
        ∏ prime ∈ (p + 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .plus then
            actualNeighborExponent p prime + 1
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hplus : prime ∈ (p + 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      have hodd : prime ≠ 2 := (Finset.mem_erase.mp hprime).1
      have hnotMinus : prime ∉ (p - 1).primeFactors := by
        intro hminus
        exact odd_prime_not_mem_both_neighbors hp hodd hminus hplus
      simp [actualNeighborSide, actualNeighborExponent, hnotMinus]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .plus then
            actualNeighborExponent p prime + 1
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        simp only [jointOddPrimeSupport, Finset.mem_erase,
          Finset.mem_union]
        exact ⟨(Finset.mem_erase.mp hprime).1,
          Or.inr (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 :=
          (Finset.mem_erase.mp hsupport).1
        have hnotPlus : prime ∉ (p + 1).primeFactors := by
          intro hplus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hplus⟩)
        have hminus : prime ∈ (p - 1).primeFactors := by
          rcases (Finset.mem_union.mp
              (Finset.mem_of_mem_erase hsupport)) with hminus | hplus
          · exact hminus
          · exact False.elim (hnotPlus hplus)
        simp [actualNeighborSide, hminus]

theorem RankinNeighborProfile.divisorCount_eq_neighborCards
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {profile : RankinNeighborProfile}
    (hmatch : profile.Matches p) :
    profile.divisorCount .minus = (p - 1).divisors.card ∧
      profile.divisorCount .plus = (p + 1).divisors.card := by
  rcases hmatch with
    ⟨hminusTwo, hplusTwo, assignment, hlist, hoddMatch⟩
  have hp : 1 < p := by omega
  have hpOdd : p % 2 = 1 :=
    hpPrime.eq_two_or_odd.resolve_left (by omega)
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have htwoMinus : 2 ∈ (p - 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hminusNe
    omega
  have htwoPlus : 2 ∈ (p + 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hplusNe
    omega
  constructor
  · rw [Nat.card_divisors hminusNe]
    rw [← Finset.mul_prod_erase
      (p - 1).primeFactors (fun prime =>
        (p - 1).factorization prime + 1) htwoMinus]
    simp only [RankinNeighborProfile.divisorCount,
      RankinNeighborProfile.twoExponent, hminusTwo, hlist]
    rw [oddDivisorCount_map_assignment p .minus
      (jointOddPrimeList p) assignment hoddMatch]
    rw [jointOddPrimeList_factor_product_minus p]
  · rw [Nat.card_divisors hplusNe]
    rw [← Finset.mul_prod_erase
      (p + 1).primeFactors (fun prime =>
        (p + 1).factorization prime + 1) htwoPlus]
    simp only [RankinNeighborProfile.divisorCount,
      RankinNeighborProfile.twoExponent, hplusTwo, hlist]
    rw [oddDivisorCount_map_assignment p .plus
      (jointOddPrimeList p) assignment hoddMatch]
    rw [jointOddPrimeList_factor_product_plus p hp]

theorem RankinNeighborProfile.jointDivisorCount_eq_neighborCards
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {profile : RankinNeighborProfile}
    (hmatch : profile.Matches p) :
    profile.jointDivisorCount =
      (p - 1).divisors.card + (p + 1).divisors.card := by
  rcases profile.divisorCount_eq_neighborCards hpPrime hpTwo hmatch with
    ⟨hminus, hplus⟩
  simp [RankinNeighborProfile.jointDivisorCount, hminus, hplus]

private theorem oddLowerNeighborProduct_map_assignment_le
    (p : ℕ) (side : NeighborSide)
    (primes : List ℕ) (assignment : ℕ → RankinOddFactor)
    (hmatch :
      ∀ prime ∈ primes, (assignment prime).Matches p prime) :
    RankinNeighborProfile.oddLowerNeighborProduct side
        (primes.map assignment) ≤
      (primes.map fun prime =>
        if actualNeighborSide p prime = side then
          prime ^ actualNeighborExponent p prime
        else 1).prod := by
  induction primes with
  | nil => simp [RankinNeighborProfile.oddLowerNeighborProduct]
  | cons prime primes ih =>
      have hhead := hmatch prime (by simp)
      have htail :
          ∀ q ∈ primes, (assignment q).Matches p q := by
        intro q hq
        exact hmatch q (by simp [hq])
      simp only [List.map_cons,
        RankinNeighborProfile.oddLowerNeighborProduct,
        List.prod_cons]
      rw [hhead.1, hhead.2.1]
      by_cases hside : actualNeighborSide p prime = side
      · simp only [hside, ite_eq_left]
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_left hhead.2.2 _)
          (ih htail)
      · simpa [hside] using ih htail

private theorem jointOddPrimeList_power_product_minus
    (p : ℕ) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .minus then
        prime ^ actualNeighborExponent p prime
      else 1).prod =
      ∏ prime ∈ (p - 1).primeFactors.erase 2,
        prime ^ (p - 1).factorization prime := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p - 1).primeFactors.erase 2,
        prime ^ (p - 1).factorization prime) =
        ∏ prime ∈ (p - 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .minus then
            prime ^ actualNeighborExponent p prime
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hminus : prime ∈ (p - 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      simp [actualNeighborSide, actualNeighborExponent, hminus]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .minus then
            prime ^ actualNeighborExponent p prime
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hprime).1,
            Finset.mem_union_left _ (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 := (Finset.mem_erase.mp hsupport).1
        have hnotMinus : prime ∉ (p - 1).primeFactors := by
          intro hminus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hminus⟩)
        simp [actualNeighborSide, hnotMinus]

private theorem jointOddPrimeList_power_product_plus
    (p : ℕ) (hp : 1 < p) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .plus then
        prime ^ actualNeighborExponent p prime
      else 1).prod =
      ∏ prime ∈ (p + 1).primeFactors.erase 2,
        prime ^ (p + 1).factorization prime := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p + 1).primeFactors.erase 2,
        prime ^ (p + 1).factorization prime) =
        ∏ prime ∈ (p + 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .plus then
            prime ^ actualNeighborExponent p prime
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hplus : prime ∈ (p + 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      have hodd : prime ≠ 2 := (Finset.mem_erase.mp hprime).1
      have hnotMinus : prime ∉ (p - 1).primeFactors := by
        intro hminus
        exact odd_prime_not_mem_both_neighbors hp hodd hminus hplus
      simp [actualNeighborSide, actualNeighborExponent, hnotMinus]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .plus then
            prime ^ actualNeighborExponent p prime
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hprime).1,
            Finset.mem_union_right _ (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 := (Finset.mem_erase.mp hsupport).1
        have hnotPlus : prime ∉ (p + 1).primeFactors := by
          intro hplus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hplus⟩)
        have hminus : prime ∈ (p - 1).primeFactors := by
          rcases Finset.mem_union.mp
              (Finset.mem_of_mem_erase hsupport) with hminus | hplus
          · exact hminus
          · exact False.elim (hnotPlus hplus)
        simp [actualNeighborSide, hminus]

/-- Matching profiles give genuine lower bounds for both neighboring
integers. -/
theorem RankinNeighborProfile.lowerNeighborProducts_le
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {profile : RankinNeighborProfile}
    (hmatch : profile.Matches p) :
    profile.lowerNeighborProduct .minus ≤ p - 1 ∧
      profile.lowerNeighborProduct .plus ≤ p + 1 := by
  rcases hmatch with
    ⟨hminusTwo, hplusTwo, assignment, hlist, hoddMatch⟩
  have hp : 1 < p := by omega
  have hpOdd : p % 2 = 1 :=
    hpPrime.eq_two_or_odd.resolve_left (by omega)
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have htwoMinus : 2 ∈ (p - 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hminusNe
    omega
  have htwoPlus : 2 ∈ (p + 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hplusNe
    omega
  constructor
  · simp only [RankinNeighborProfile.lowerNeighborProduct,
      RankinNeighborProfile.twoExponent, hminusTwo, hlist]
    calc
      2 ^ (p - 1).factorization 2 *
          RankinNeighborProfile.oddLowerNeighborProduct .minus
            ((jointOddPrimeList p).map assignment) ≤
        2 ^ (p - 1).factorization 2 *
          ((jointOddPrimeList p).map fun prime =>
            if actualNeighborSide p prime = .minus then
              prime ^ actualNeighborExponent p prime
            else 1).prod :=
        Nat.mul_le_mul_left _
          (oddLowerNeighborProduct_map_assignment_le
            p .minus (jointOddPrimeList p) assignment hoddMatch)
      _ = 2 ^ (p - 1).factorization 2 *
          ∏ prime ∈ (p - 1).primeFactors.erase 2,
            prime ^ (p - 1).factorization prime := by
        rw [jointOddPrimeList_power_product_minus p]
      _ = ∏ prime ∈ (p - 1).primeFactors,
            prime ^ (p - 1).factorization prime :=
        Finset.mul_prod_erase (p - 1).primeFactors
          (fun prime => prime ^ (p - 1).factorization prime) htwoMinus
      _ = p - 1 := (Nat.prod_primeFactors_pow_factorization hminusNe).symm
  · simp only [RankinNeighborProfile.lowerNeighborProduct,
      RankinNeighborProfile.twoExponent, hplusTwo, hlist]
    calc
      2 ^ (p + 1).factorization 2 *
          RankinNeighborProfile.oddLowerNeighborProduct .plus
            ((jointOddPrimeList p).map assignment) ≤
        2 ^ (p + 1).factorization 2 *
          ((jointOddPrimeList p).map fun prime =>
            if actualNeighborSide p prime = .plus then
              prime ^ actualNeighborExponent p prime
            else 1).prod :=
        Nat.mul_le_mul_left _
          (oddLowerNeighborProduct_map_assignment_le
            p .plus (jointOddPrimeList p) assignment hoddMatch)
      _ = 2 ^ (p + 1).factorization 2 *
          ∏ prime ∈ (p + 1).primeFactors.erase 2,
            prime ^ (p + 1).factorization prime := by
        rw [jointOddPrimeList_power_product_plus p hp]
      _ = ∏ prime ∈ (p + 1).primeFactors,
            prime ^ (p + 1).factorization prime :=
        Finset.mul_prod_erase (p + 1).primeFactors
          (fun prime => prime ^ (p + 1).factorization prime) htwoPlus
      _ = p + 1 := (Nat.prod_primeFactors_pow_factorization hplusNe).symm

private theorem oddCoarseEulerProduct_map_assignment
    (p : ℕ) (side : NeighborSide)
    (primes : List ℕ) (assignment : ℕ → RankinOddFactor)
    (hmatch :
      ∀ prime ∈ primes, (assignment prime).Matches p prime) :
    RankinNeighborProfile.oddCoarseEulerProduct side
        (primes.map assignment) =
      (primes.map fun prime =>
        if actualNeighborSide p prime = side then
          coarseRankinPrimePowerFactor
            (actualNeighborExponent p prime)
            (assignment prime).weightCap.weight
        else 1).prod := by
  induction primes with
  | nil => simp [RankinNeighborProfile.oddCoarseEulerProduct]
  | cons prime primes ih =>
      have hhead := hmatch prime (by simp)
      have htail :
          ∀ q ∈ primes, (assignment q).Matches p q := by
        intro q hq
        exact hmatch q (by simp [hq])
      simp only [List.map_cons,
        RankinNeighborProfile.oddCoarseEulerProduct,
        List.prod_cons]
      rw [ih htail]
      simp [RankinOddFactor.Matches] at hhead
      rw [hhead.1, hhead.2.1]

private theorem jointOddPrimeList_coarse_product_minus
    (p : ℕ)
    (profile : RankinNeighborProfile)
    (assignment : ℕ → RankinOddFactor) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .minus then
        coarseRankinPrimePowerFactor
          (actualNeighborExponent p prime)
          (assignment prime).weightCap.weight
      else 1).prod =
      ∏ prime ∈ (p - 1).primeFactors.erase 2,
        coarseRankinPrimePowerFactor ((p - 1).factorization prime)
          (assignedPrimeWeight p profile assignment prime) := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p - 1).primeFactors.erase 2,
        coarseRankinPrimePowerFactor ((p - 1).factorization prime)
          (assignedPrimeWeight p profile assignment prime)) =
        ∏ prime ∈ (p - 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .minus then
            coarseRankinPrimePowerFactor
              (actualNeighborExponent p prime)
              (assignment prime).weightCap.weight
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hodd : prime ≠ 2 := (Finset.mem_erase.mp hprime).1
      have hminus : prime ∈ (p - 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      have hsupport : prime ∈ jointOddPrimeSupport p := by
        exact Finset.mem_erase.mpr ⟨hodd,
          Finset.mem_union_left _ hminus⟩
      simp [actualNeighborSide, actualNeighborExponent,
        assignedPrimeWeight, hodd, hminus, hsupport]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .minus then
            coarseRankinPrimePowerFactor
              (actualNeighborExponent p prime)
              (assignment prime).weightCap.weight
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hprime).1,
            Finset.mem_union_left _ (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 := (Finset.mem_erase.mp hsupport).1
        have hnotMinus : prime ∉ (p - 1).primeFactors := by
          intro hminus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hminus⟩)
        simp [actualNeighborSide, hnotMinus]

private theorem jointOddPrimeList_coarse_product_plus
    (p : ℕ) (hp : 1 < p)
    (profile : RankinNeighborProfile)
    (assignment : ℕ → RankinOddFactor) :
    ((jointOddPrimeList p).map fun prime =>
      if actualNeighborSide p prime = .plus then
        coarseRankinPrimePowerFactor
          (actualNeighborExponent p prime)
          (assignment prime).weightCap.weight
      else 1).prod =
      ∏ prime ∈ (p + 1).primeFactors.erase 2,
        coarseRankinPrimePowerFactor ((p + 1).factorization prime)
          (assignedPrimeWeight p profile assignment prime) := by
  rw [jointOddPrimeList_map_prod]
  symm
  calc
    (∏ prime ∈ (p + 1).primeFactors.erase 2,
        coarseRankinPrimePowerFactor ((p + 1).factorization prime)
          (assignedPrimeWeight p profile assignment prime)) =
        ∏ prime ∈ (p + 1).primeFactors.erase 2,
          (if actualNeighborSide p prime = .plus then
            coarseRankinPrimePowerFactor
              (actualNeighborExponent p prime)
              (assignment prime).weightCap.weight
          else 1) := by
      apply Finset.prod_congr rfl
      intro prime hprime
      have hodd : prime ≠ 2 := (Finset.mem_erase.mp hprime).1
      have hplus : prime ∈ (p + 1).primeFactors :=
        Finset.mem_of_mem_erase hprime
      have hnotMinus : prime ∉ (p - 1).primeFactors := by
        intro hminus
        exact odd_prime_not_mem_both_neighbors hp hodd hminus hplus
      have hsupport : prime ∈ jointOddPrimeSupport p := by
        exact Finset.mem_erase.mpr ⟨hodd,
          Finset.mem_union_right _ hplus⟩
      simp [actualNeighborSide, actualNeighborExponent,
        assignedPrimeWeight, hodd, hnotMinus, hsupport]
    _ = ∏ prime ∈ jointOddPrimeSupport p,
          (if actualNeighborSide p prime = .plus then
            coarseRankinPrimePowerFactor
              (actualNeighborExponent p prime)
              (assignment prime).weightCap.weight
          else 1) := by
      apply Finset.prod_subset
      · intro prime hprime
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hprime).1,
            Finset.mem_union_right _ (Finset.mem_of_mem_erase hprime)⟩
      · intro prime hsupport hnot
        have hodd : prime ≠ 2 := (Finset.mem_erase.mp hsupport).1
        have hnotPlus : prime ∉ (p + 1).primeFactors := by
          intro hplus
          exact hnot (Finset.mem_erase.mpr ⟨hodd, hplus⟩)
        have hminus : prime ∈ (p - 1).primeFactors := by
          rcases Finset.mem_union.mp
              (Finset.mem_of_mem_erase hsupport) with hminus | hplus
          · exact hminus
          · exact False.elim (hnotPlus hplus)
        simp [actualNeighborSide, hminus]

theorem RankinNeighborProfile.factorizationCoarse_eq_coarseEulerProduct
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {profile : RankinNeighborProfile}
    (hmatch : profile.Matches p) :
    ∃ assignment : ℕ → RankinOddFactor,
      profile.oddFactors = (jointOddPrimeList p).map assignment ∧
      (∀ prime ∈ jointOddPrimeList p,
        (assignment prime).Matches p prime) ∧
      (p - 1).factorization.prod (fun prime exponent =>
          coarseRankinPrimePowerFactor exponent
            (assignedPrimeWeight p profile assignment prime)) =
        profile.coarseEulerProduct .minus ∧
      (p + 1).factorization.prod (fun prime exponent =>
          coarseRankinPrimePowerFactor exponent
            (assignedPrimeWeight p profile assignment prime)) =
        profile.coarseEulerProduct .plus := by
  rcases hmatch with
    ⟨hminusTwo, hplusTwo, assignment, hlist, hoddMatch⟩
  have hp : 1 < p := by omega
  have hpOdd : p % 2 = 1 :=
    hpPrime.eq_two_or_odd.resolve_left (by omega)
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have htwoMinus : 2 ∈ (p - 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hminusNe
    omega
  have htwoPlus : 2 ∈ (p + 1).primeFactors := by
    apply Nat.prime_two.mem_primeFactors _ hplusNe
    omega
  refine ⟨assignment, hlist, hoddMatch, ?_, ?_⟩
  · simp only [Finsupp.prod]
    rw [Nat.support_factorization]
    rw [← Finset.mul_prod_erase
      (p - 1).primeFactors
      (fun prime => coarseRankinPrimePowerFactor
        ((p - 1).factorization prime)
        (assignedPrimeWeight p profile assignment prime)) htwoMinus]
    simp only [assignedPrimeWeight, ite_eq_left,
      RankinNeighborProfile.coarseEulerProduct,
      RankinNeighborProfile.twoExponent, hminusTwo, hlist]
    rw [oddCoarseEulerProduct_map_assignment p .minus
      (jointOddPrimeList p) assignment hoddMatch]
    rw [jointOddPrimeList_coarse_product_minus
      p profile assignment]
    rfl
  · simp only [Finsupp.prod]
    rw [Nat.support_factorization]
    rw [← Finset.mul_prod_erase
      (p + 1).primeFactors
      (fun prime => coarseRankinPrimePowerFactor
        ((p + 1).factorization prime)
        (assignedPrimeWeight p profile assignment prime)) htwoPlus]
    simp only [assignedPrimeWeight, ite_eq_left,
      RankinNeighborProfile.coarseEulerProduct,
      RankinNeighborProfile.twoExponent, hplusTwo, hlist]
    rw [oddCoarseEulerProduct_map_assignment p .plus
      (jointOddPrimeList p) assignment hoddMatch]
    rw [jointOddPrimeList_coarse_product_plus
      p hp profile assignment]
    rfl

/-- A valid matching profile supplies one total rational weight assignment
whose two exact Euler products are bounded by the profile's two coarse
products. -/
theorem RankinNeighborProfile.exists_assignedPrimeWeight_bounds
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {profile : RankinNeighborProfile}
    (hprofile : profile.Valid) (hmatch : profile.Matches p) :
    ∃ assignment : ℕ → RankinOddFactor,
      (∀ prime,
        0 ≤ assignedPrimeWeight p profile assignment prime) ∧
      (∀ prime : ℕ, prime.Prime →
        1 ≤ (prime : ℚ) *
          (assignedPrimeWeight p profile assignment prime) ^ 12) ∧
      (p - 1).factorization.prod (fun prime exponent =>
          rankinPrimePowerFactor prime exponent
            (assignedPrimeWeight p profile assignment prime)) ≤
        profile.coarseEulerProduct .minus ∧
      (p + 1).factorization.prod (fun prime exponent =>
          rankinPrimePowerFactor prime exponent
            (assignedPrimeWeight p profile assignment prime)) ≤
        profile.coarseEulerProduct .plus := by
  obtain ⟨assignment, hlist, hoddMatch, hminusEq, hplusEq⟩ :=
    profile.factorizationCoarse_eq_coarseEulerProduct
      hpPrime hpTwo hmatch
  have hnonneg :
      ∀ prime, 0 ≤ assignedPrimeWeight p profile assignment prime :=
    assignedPrimeWeight_nonneg hprofile hlist
  have hpower :
      ∀ prime : ℕ, prime.Prime →
        1 ≤ (prime : ℚ) *
          (assignedPrimeWeight p profile assignment prime) ^ 12 :=
    assignedPrimeWeight_power hprofile hlist hoddMatch
  refine ⟨assignment, hnonneg, hpower, ?_, ?_⟩
  · exact (factorizationEulerProduct_le_coarse
      (p - 1) (assignedPrimeWeight p profile assignment) hnonneg).trans_eq
        hminusEq
  · exact (factorizationEulerProduct_le_coarse
      (p + 1) (assignedPrimeWeight p profile assignment) hnonneg).trans_eq
        hplusEq

end BGS.NumberTheory
