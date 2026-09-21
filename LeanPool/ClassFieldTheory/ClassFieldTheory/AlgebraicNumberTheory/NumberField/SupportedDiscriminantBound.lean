/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.GaloisDifferentBound
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Multiset.Count
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
/-!
# A discriminant bound from a prime-to-degree ramification support

Every prime factor of the different lies above a rational divisor of the
discriminant. The CRT trace bound controls its exponent by the exponent
in the corresponding rational prime ideal. Hence the different divides
(c), and taking the absolute ideal norm gives |disc(L)| <= c^[L:Q].
The Galois hypothesis is retained: it is what makes each e*f divide the
whole extension degree.
-/

open scoped NumberField
open NumberField UniqueFactorizationMonoid

noncomputable section

namespace AlgebraicNumberTheory.Discriminant

/-- The different divides a supported rational integer prime to the
Galois degree. -/
theorem differentIdeal_dvd_span_of_coprime_support
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (c : ℕ) (hc : 0 < c) (hcn : Nat.Coprime c (Module.finrank ℚ L))
    (hSupport : ∀ q : Nat.Primes, (q : ℤ) ∣ NumberField.discr L → (q : ℕ) ∣ c) :
    differentIdeal ℤ (𝓞 L) ∣ Ideal.span {(c : 𝓞 L)} := by
  classical
  let D : Ideal (𝓞 L) := differentIdeal ℤ (𝓞 L)
  let J : Ideal (𝓞 L) := Ideal.span {(c : 𝓞 L)}
  have hD : D ≠ 0 := differentIdeal_ne_bot
  have hJ : J ≠ 0 := by
    exact mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hc.ne')
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hD hJ).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  by_cases hPmem : P ∈ normalizedFactors D
  · have hPrime : Prime P := prime_of_normalized_factor P hPmem
    have : P.IsPrime := Ideal.isPrime_of_prime hPrime
    have : P.IsMaximal := (Ideal.isPrime_of_prime hPrime).isMaximal hPrime.ne_zero
    have hPD : P ∣ D := dvd_of_mem_normalizedFactors hPmem
    obtain ⟨q, f, hf, hqP, hq, hPNorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hqAbs : q ∣ (NumberField.discr L).natAbs := by
      have hN := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hPD)
      rw [hPNorm, NumberField.absNorm_differentIdeal L (𝓞 L)] at hN
      exact (dvd_pow_self q hf.ne').trans hN
    have hqDiscr : (q : ℤ) ∣ NumberField.discr L :=
      Int.natAbs_dvd_natAbs.mp hqAbs
    have hqc : q ∣ c := hSupport ⟨q, hq⟩ hqDiscr
    have hqDegree : ¬ q ∣ Module.finrank ℚ L :=
      hq.coprime_iff_not_dvd.mp (hcn.of_dvd_left hqc)
    have : Fact q.Prime := ⟨hq⟩
    let p : Ideal ℤ := Ideal.span {(q : ℤ)}
    have : P.LiesOver p :=
      (Ideal.liesOver_span_iff (show P.IsPrime from inferInstance).ne_top
        (Nat.prime_iff_prime_int.mp hq)).mpr (by simpa only [map_natCast] using hqP)
    have hp0 : p ≠ ⊥ := by
      exact mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr hq.ne_zero)
    have hpMap0 : p.map (algebraMap ℤ (𝓞 L)) ≠ 0 :=
      Ideal.map_ne_bot_of_ne_bot hp0
    obtain ⟨Q, _, hFactorD⟩ := Ideal.eq_prime_pow_mul_coprime hD P
    have hCount : (normalizedFactors D).count P < P.ramificationIdx ℤ := by
      apply Nat.lt_of_not_ge
      intro he
      apply ramification_power_not_dvd_differentIdeal_of_not_dvd_degree L q hq P hqDegree
      exact (pow_dvd_pow P he).trans ⟨Q, hFactorD⟩
    have hMap : p.map (algebraMap ℤ (𝓞 L)) ∣ J := by
      rw [Ideal.dvd_iff_le]
      change Ideal.span {(c : 𝓞 L)} ≤ _
      rw [Ideal.map_span, Set.image_singleton]
      apply Ideal.span_singleton_le_span_singleton.mpr
      rcases hqc with ⟨k, hk⟩
      refine ⟨(k : 𝓞 L), ?_⟩
      simp only [hk, Nat.cast_mul, map_natCast]
    have hFactors :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hpMap0 hJ).mp hMap
    have hCountMap := Multiset.le_iff_count.mp hFactors P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hpMap0]
      at hCountMap
    exact hCount.le.trans hCountMap
  · rw [Multiset.count_eq_zero.mpr hPmem]
    exact Nat.zero_le _

/-- A supported integer prime to a finite Galois degree bounds the root
scale of its absolute discriminant. -/
theorem natAbs_discr_le_pow_of_coprime_support
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (c : ℕ) (hc : 0 < c) (hcn : Nat.Coprime c (Module.finrank ℚ L))
    (hSupport : ∀ q : Nat.Primes, (q : ℤ) ∣ NumberField.discr L → (q : ℕ) ∣ c) :
    (NumberField.discr L).natAbs ≤ c ^ Module.finrank ℚ L := by
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp
    (differentIdeal_dvd_span_of_coprime_support L c hc hcn hSupport))
  rw [NumberField.absNorm_differentIdeal L (𝓞 L),
    Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank] at h
  exact Nat.le_of_dvd (pow_pos hc _) h

end AlgebraicNumberTheory.Discriminant
