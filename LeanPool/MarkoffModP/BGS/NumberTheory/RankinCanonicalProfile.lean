/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.RankinProfileMatching
import LeanPool.MarkoffModP.BGS.NumberTheory.RankinJointEnvelopeCertificate

/-!
# Canonical Rankin profile attached to a neighboring factorization

The numerical certificate will choose rational caps.  This file fixes the
mathematical coverage map independently of those choices: every odd prime in
the globally sorted support is sent to its actual side and exponent, while the
cap assignment and the twelfth-root cap remain explicit parameters.
-/

namespace BGS.NumberTheory

private theorem factorization_two_mul_of_odd
    {n : ℕ} (hn : Odd n) :
    (2 * n).factorization 2 = 1 := by
  have hnNe : n ≠ 0 := hn.pos.ne'
  have hfactorization := Nat.factorization_mul (by norm_num : 2 ≠ 0) hnNe
  have happly := congrArg (fun factorization : ℕ →₀ ℕ =>
    factorization 2) hfactorization
  simpa [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat] using happly

/-- For an odd prime, exactly one neighboring two-adic exponent is one and
the other is at least two. -/
theorem neighboring_twoFactorization_shape
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p) :
    (((p - 1).factorization 2 = 1 ∧
        2 ≤ (p + 1).factorization 2) ∨
      ((p + 1).factorization 2 = 1 ∧
        2 ≤ (p - 1).factorization 2)) := by
  have hpOdd : Odd p := hpPrime.odd_iff.mpr (by omega)
  rcases hpOdd with ⟨k, rfl⟩
  rcases k.even_or_odd with hkEven | hkOdd
  · right
    have hkPlusOdd : Odd (k + 1) := hkEven.add_one
    constructor
    · have hplusEq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hplusEq]
      exact factorization_two_mul_of_odd hkPlusOdd
    · have hminusEq : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hminusEq]
      have hne : 2 * k ≠ 0 := by
        rcases hkEven with ⟨j, hj⟩
        omega
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp
      rcases hkEven with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      norm_num
      omega
  · left
    have hkPlusEven : Even (k + 1) := hkOdd.add_one
    constructor
    · have hminusEq : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hminusEq]
      exact factorization_two_mul_of_odd hkOdd
    · have hplusEq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hplusEq]
      have hne : 2 * (k + 1) ≠ 0 := by omega
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp
      rcases hkPlusEven with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      norm_num
      omega

theorem actualNeighborExponent_pos
    {p prime : ℕ} (hp : 1 < p)
    (hprime : prime ∈ jointOddPrimeList p) :
    0 < actualNeighborExponent p prime := by
  have hdata := mem_jointOddPrimeList.mp hprime
  have hprimePrime : prime.Prime := by
    rcases hdata.2 with hminus | hplus
    · exact Nat.prime_of_mem_primeFactors hminus
    · exact Nat.prime_of_mem_primeFactors hplus
  by_cases hminus : prime ∈ (p - 1).primeFactors
  · simp only [actualNeighborExponent, ite_eq_left hminus]
    exact hprimePrime.factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hminus)
  · have hplus : prime ∈ (p + 1).primeFactors :=
      hdata.2.resolve_left hminus
    simp only [actualNeighborExponent, ite_eq_right hminus]
    exact hprimePrime.factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hplus)

/-- The exact odd factor produced from one actual support prime and one chosen
rational cap. -/
def canonicalRankinOddFactor
    (p : ℕ) (oddCap : ℕ → RationalPrimeWeightCap)
    (prime : ℕ) : RankinOddFactor where
  side := actualNeighborSide p prime
  exponent := actualNeighborExponent p prime
  weightCap := oddCap prime

/-- The complete canonical profile for `p`, parameterized by cap choices. -/
def canonicalRankinNeighborProfile
    (p : ℕ) (twoCap : RationalPrimeWeightCap)
    (oddCap : ℕ → RationalPrimeWeightCap)
    (rootCap : ℕ) : RankinNeighborProfile where
  minusTwoExponent := (p - 1).factorization 2
  plusTwoExponent := (p + 1).factorization 2
  twoWeightCap := twoCap
  oddFactors := (jointOddPrimeList p).map
    (canonicalRankinOddFactor p oddCap)
  rootCap := rootCap

theorem canonicalRankinNeighborProfile_matches
    {p : ℕ} {twoCap : RationalPrimeWeightCap}
    {oddCap : ℕ → RationalPrimeWeightCap} {rootCap : ℕ}
    (hfloor :
      ∀ prime ∈ jointOddPrimeList p,
        (oddCap prime).lowerPrime ≤ prime) :
    (canonicalRankinNeighborProfile p twoCap oddCap rootCap).Matches p := by
  refine ⟨rfl, rfl, canonicalRankinOddFactor p oddCap, rfl, ?_⟩
  intro prime hprime
  exact ⟨rfl, rfl, hfloor prime hprime⟩

private theorem allRankinOddFactorsValid_map_canonical
    {p : ℕ} (hp : 1 < p)
    {oddCap : ℕ → RationalPrimeWeightCap}
    (hcap :
      ∀ prime ∈ jointOddPrimeList p,
        (oddCap prime).Valid ∧
          (oddCap prime).lowerPrime.Prime ∧
          3 ≤ (oddCap prime).lowerPrime) :
    allRankinOddFactorsValid
      ((jointOddPrimeList p).map
        (canonicalRankinOddFactor p oddCap)) := by
  have hpos :
      ∀ prime ∈ jointOddPrimeList p,
        0 < actualNeighborExponent p prime :=
    fun prime hprime => actualNeighborExponent_pos hp hprime
  generalize jointOddPrimeList p = primes at hcap hpos ⊢
  induction primes with
  | nil => simp [allRankinOddFactorsValid]
  | cons prime primes ih =>
      simp only [List.map_cons, allRankinOddFactorsValid]
      constructor
      · exact ⟨hpos prime (by simp),
          (hcap prime (by simp)).1,
          (hcap prime (by simp)).2.1,
          (hcap prime (by simp)).2.2⟩
      · apply ih
        · intro q hq
          exact hcap q (by simp [hq])
        · intro q hq
          exact hpos q (by simp [hq])

/-- The exact assumptions on generated caps under which the canonical profile
is structurally and arithmetically valid. -/
theorem canonicalRankinNeighborProfile_valid
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {twoCap : RationalPrimeWeightCap}
    {oddCap : ℕ → RationalPrimeWeightCap} {rootCap : ℕ}
    (htwoValid : twoCap.Valid)
    (htwoFloor : twoCap.lowerPrime = 2)
    (hoddValid :
      ∀ prime ∈ jointOddPrimeList p,
        (oddCap prime).Valid ∧
          (oddCap prime).lowerPrime.Prime ∧
          3 ≤ (oddCap prime).lowerPrime)
    (hfloorStrict :
      (jointOddPrimeList p).Pairwise fun left right =>
        (oddCap left).lowerPrime < (oddCap right).lowerPrime)
    (hrootPos : 0 < rootCap)
    (hroot :
      (canonicalRankinNeighborProfile p twoCap oddCap rootCap).witnessCap ≤
        rootCap ^ 12) :
    (canonicalRankinNeighborProfile p twoCap oddCap rootCap).Valid := by
  refine ⟨neighboring_twoFactorization_shape hpPrime hpTwo,
    htwoValid, htwoFloor, ?_, ?_, hrootPos, hroot⟩
  · exact allRankinOddFactorsValid_map_canonical (by omega) hoddValid
  · rw [rankinOddFloorsStrictlyIncreasing,
      canonicalRankinNeighborProfile, List.pairwise_map]
    simpa [canonicalRankinOddFactor] using hfloorStrict

/-- The side-erased joint root condition is sufficient for validity of the
actual side assignment.  This lets a finite certificate choose its root cap
without branching over which neighboring factor receives each odd prime. -/
theorem canonicalRankinNeighborProfile_valid_of_jointEnvelope
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    {twoCap : RationalPrimeWeightCap}
    {oddCap : ℕ → RationalPrimeWeightCap} {rootCap : ℕ}
    (htwoValid : twoCap.Valid)
    (htwoFloor : twoCap.lowerPrime = 2)
    (hoddValid :
      ∀ prime ∈ jointOddPrimeList p,
        (oddCap prime).Valid ∧
          (oddCap prime).lowerPrime.Prime ∧
          3 ≤ (oddCap prime).lowerPrime)
    (hfloorStrict :
      (jointOddPrimeList p).Pairwise fun left right =>
        (oddCap left).lowerPrime < (oddCap right).lowerPrime)
    (hrootPos : 0 < rootCap)
    (hjointRoot :
      RankinNeighborProfile.JointEnvelopeValid
        (canonicalRankinNeighborProfile p twoCap oddCap rootCap)) :
    (canonicalRankinNeighborProfile p twoCap oddCap rootCap).Valid := by
  apply canonicalRankinNeighborProfile_valid hpPrime hpTwo
    htwoValid htwoFloor hoddValid hfloorStrict hrootPos
  exact
    (RankinNeighborProfile.witnessCap_le_jointEnvelopeWitnessCap_of_shape
      (canonicalRankinNeighborProfile p twoCap oddCap rootCap)
      (neighboring_twoFactorization_shape hpPrime hpTwo)).trans
      hjointRoot

/-- A deliberately loose but universally available cap: weight one at the
actual prime.  It is used only to prove that the profile representation is
total; optimized certificates replace it by smaller rational caps. -/
def unitRationalPrimeWeightCap (prime : ℕ) : RationalPrimeWeightCap where
  lowerPrime := prime
  numerator := 1
  denominator := 1

theorem unitRationalPrimeWeightCap_valid
    {prime : ℕ} (hprime : 0 < prime) :
    (unitRationalPrimeWeightCap prime).Valid := by
  simp [unitRationalPrimeWeightCap, RationalPrimeWeightCap.Valid]
  omega

private theorem pairwise_lt_of_pairwise_le_of_nodup
    {values : List ℕ}
    (hle : values.Pairwise (· ≤ ·)) (hnodup : values.Nodup) :
    values.Pairwise (· < ·) := by
  induction values with
  | nil => simp
  | cons value values ih =>
      rw [List.pairwise_cons] at hle ⊢
      rw [List.nodup_cons] at hnodup
      constructor
      · intro later hlater
        exact lt_of_le_of_ne (hle.1 later hlater) (by
          intro heq
          exact hnodup.1 (heq ▸ hlater))
      · exact ih hle.2 hnodup.2

theorem jointOddPrimeList_pairwise_lt (p : ℕ) :
    (jointOddPrimeList p).Pairwise (· < ·) := by
  apply pairwise_lt_of_pairwise_le_of_nodup
  · exact Finset.pairwise_sort (jointOddPrimeSupport p) (· ≤ ·)
  · exact Finset.sort_nodup (jointOddPrimeSupport p) (· ≤ ·)

/-- A concrete canonical profile exists for every `p`: exact-prime unit
weights and a deliberately oversized root cap make validity unconditional.
This theorem is a coverage sanity check, not the optimized numerical
certificate. -/
def unitCanonicalRankinNeighborProfile (p : ℕ) : RankinNeighborProfile :=
  let seed := canonicalRankinNeighborProfile p
    (unitRationalPrimeWeightCap 2)
    unitRationalPrimeWeightCap 1
  canonicalRankinNeighborProfile p
    (unitRationalPrimeWeightCap 2)
    unitRationalPrimeWeightCap (seed.witnessCap + 1)

theorem unitCanonicalRankinNeighborProfile_matches (p : ℕ) :
    (unitCanonicalRankinNeighborProfile p).Matches p := by
  apply canonicalRankinNeighborProfile_matches
  intro prime hprime
  simp [unitRationalPrimeWeightCap]

theorem unitCanonicalRankinNeighborProfile_valid
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p) :
    (unitCanonicalRankinNeighborProfile p).Valid := by
  let seed := canonicalRankinNeighborProfile p
    (unitRationalPrimeWeightCap 2)
    unitRationalPrimeWeightCap 1
  change (canonicalRankinNeighborProfile p
    (unitRationalPrimeWeightCap 2)
    unitRationalPrimeWeightCap (seed.witnessCap + 1)).Valid
  apply canonicalRankinNeighborProfile_valid hpPrime hpTwo
  · exact unitRationalPrimeWeightCap_valid (by norm_num)
  · rfl
  · intro prime hprime
    have hprimePrime : prime.Prime := by
      rcases (mem_jointOddPrimeList.mp hprime).2 with hminus | hplus
      · exact Nat.prime_of_mem_primeFactors hminus
      · exact Nat.prime_of_mem_primeFactors hplus
    have hthree : 3 ≤ prime := by
      have hneTwo := (mem_jointOddPrimeList.mp hprime).1
      have htwo := hprimePrime.two_le
      omega
    exact ⟨unitRationalPrimeWeightCap_valid hprimePrime.pos,
      hprimePrime, hthree⟩
  · simpa [unitRationalPrimeWeightCap] using
      jointOddPrimeList_pairwise_lt p
  · omega
  · change seed.witnessCap ≤ (seed.witnessCap + 1) ^ 12
    exact (Nat.le_succ seed.witnessCap).trans
      (Nat.le_pow (by norm_num : 0 < 12))

end BGS.NumberTheory
